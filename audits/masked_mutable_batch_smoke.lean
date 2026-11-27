import REWB.MaskedMutableProgressionBatchQuery

/-! Actual enumerator → fanout → source rows → physical deletion → run-ID
queries, checked against physical-window scans and independently updated
source masks. References and scans occur only in this audit. -/
open REWB REWB.RunGeometry REWB.MaskedMutableProgression
open REWB.MaskedMutableProgression.Batch

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def marked (mask : Array Bool) (p : Nat) : Bool := mask[p]?.getD false

private def brute (R : Bounds) (mask : Array Bool) (K s lo hi r : Nat) : Option Nat :=
  ((List.range (R.hi-R.lo+1)).find? fun i=>
    let p:=R.lo+i
    let k:=(p-s)/R.period
    marked mask p && s≤p && (p-s)%R.period=0 && lo≤k && k≤hi && k%K=r).map (R.lo+·)

private structure Stats where
  prepared : Nat := 0
  requests : Nat := 0
  rowChecks : Nat := 0
  queryChecks : Nat := 0
  deliveries : Nat := 0
  maxRows : Nat := 0

private def check (st : State) (mask : Array Bool) (removed : List Nat) (stats : Stats) : IO Stats := do
  let mut out:=stats
  require (st.indexes.size==st.runs.size) "row alignment"
  require (st.singleton.base==0 && st.singleton.len==st.n+1 && st.singleton.step==1) "singleton shape"
  for p in [:st.n+3] do
    require ((member st.singleton p).1==(p≤st.n && marked mask p)) s!"singleton p={p}"
  let mut delivered:=0
  for id in [:st.runs.size] do
    match st.runs[id]?,st.indexes[id]? with
    | some R,some idx =>
      require (idx.base==R.lo && idx.len==R.hi-R.lo+1 && idx.step==st.modulus*R.period) "run shape"
      for p in [:st.n+3] do
        let inRun:=R.lo≤p && p≤R.hi
        let pending:=(MaskedSourceFanout.read st.sources.rows p).ids.contains id
        require (pending==(inRun && !removed.contains p)) s!"pending p={p} id={id}"
        require ((member idx p).1==(inRun && marked mask p)) s!"row membership p={p} id={id}"
      for p in List.range' R.lo (R.hi-R.lo+1) do
        if removed.contains p then delivered:=delivered+1
      for s in #[0,R.lo,R.lo+1] do
        for bounds in #[(0,st.n+2),(1,st.n+3),(2,1)] do
          for r in #[0,1,st.modulus-1,st.modulus] do
            let got:=queryRun st id s bounds.1 bounds.2 r
            let want:=brute R mask st.modulus s bounds.1 bounds.2 r
            require (got.value==want)
              s!"run query n={st.n} id={id} run={repr R} K={st.modulus} s={s} lo={bounds.1} hi={bounds.2} r={r} got={got.value} want={want}"
            require (got.work≤79*((st.n+2).log2+1)+7) "run query counter"
            out:={out with queryChecks:=out.queryChecks+1}
      out:={out with rowChecks:=out.rowChecks+1}
    | _,_ => throw (IO.userError "missing aligned run index")
  require (st.delivered==delivered) "exact delivered memberships"
  require (st.delivered≤6*st.n*(st.n.log2+1)) "delivery mass"
  require ((queryRun st st.runs.size 0 0 10 0).value==none) "outside run ID"
  pure out

private def one (text : Array (Fin 2)) (source : Array Bool) (K : Nat) (stats : Stats) : IO Stats := do
  let initial:=prepare text ⟨0,by decide⟩ source K
  require (initial.preparationWork≤sourcePreparationBudget text.size) "source preparation counter"
  require (initial.enumerationWork≤MaskedRunEnumerationCost.coefficient 2*(text.size+1)*((text.size+1).log2+1)^2)
    "enumeration counter"
  let mut out:={stats with prepared:=stats.prepared+1,maxRows:=max stats.maxRows initial.runs.size}
  let mut st:=initial
  let mut live:=source
  let mut removed : List Nat:=[]
  out←check st live removed out
  let requests:=List.range (text.size+2)++[text.size,0,text.size+3]++List.range (text.size+2)
  for p in requests do
    let oldDelivered:=st.delivered
    let ids:=(MaskedSourceFanout.read st.sources.rows p).ids
    let next:=eraseSource p st
    require (next.delivered==oldDelivered+ids.length) "actual ID visits"
    require (next.updateWork≤st.updateWork+requestBudget st.n+ids.length*rowBudget st.n) "one update counter"
    require (next.requests==st.requests+1) "request counter"
    st:=next
    live:=live.setIfInBounds p false
    removed:=p::removed
    out:={out with requests:=out.requests+1}
    out←check st live removed out
  require (st.totalWork≤totalBudget 2 text.size requests.length) "full batch counter"
  require (st.updateWork≤sourceUpdateBudget text.size requests.length) "closed update counter"
  require (st.runs==initial.runs) "retained run descriptors"
  out←check initial source [] out
  pure {out with deliveries:=out.deliveries+st.delivered}

private def deep : IO Unit := do
  let n:=512
  let text : Array (Fin 2):=Array.replicate n ⟨0,by decide⟩
  let source:=Array.replicate (n+1) true
  let initial:=prepare text ⟨0,by decide⟩ source 17
  let ps:=List.range (n+1)++List.range (n+1)++[n+2,0]
  let final:=eraseMany ps initial
  require (initial.runs.size==1 && final.indexes.size==1) "deep actual cubic run"
  require (final.delivered==n+1) "deep one-time memberships"
  require (final.singleton.tree.count==0 && initial.singleton.tree.count==n+1) "deep persistent singleton"
  for p in [:n+1] do
    require ((member final.singleton p).1==false && (member initial.singleton p).1==true) "deep singleton semantics"
  for r in [:17] do
    require ((queryRun final 0 0 0 (n+1) r).value==none) "deep exhausted run"
    require ((queryRun initial 0 0 0 (n+1) r).value==some r) "deep old run snapshot"
  require (final.updateWork≤sourceUpdateBudget n ps.length) "deep update bound"
  require (final.totalWork≤totalBudget 2 n ps.length) "deep full bound"
  IO.println s!"mutableBatchDeep n={n} runs={initial.runs.size} requests={ps.length} delivered={final.delivered} enumerationWork={initial.enumerationWork} sourcePreparationWork={initial.preparationWork} updateWork={final.updateWork} persistence=true repeatedRequests=true"

def main : IO Unit := do
  let mut stats : Stats:={}
  for n in [:8] do
    for bits in [:2^n] do
      let text:=Array.ofFn (fun i : Fin n=>(⟨(bits/2^i.val)%2,Nat.mod_lt _ (by decide)⟩ : Fin 2))
      let maskSize:=if bits%3=0 then n/2 else n+1
      let source:=Array.ofFn (fun i : Fin maskSize=>(i.val+bits)%3 != 1)
      for K in #[1,2,17] do stats←one text source K stats
  IO.println s!"mutableBatchPrepared={stats.prepared} requests={stats.requests} rowChecks={stats.rowChecks} runQueries={stats.queryChecks} delivered={stats.deliveries} maxRuns={stats.maxRows} exactCurrentSources=true sharedEnumerator=true"
  deep
