import REWB.MaskedSourceFanoutRegression

open REWB.MaskedSourceFanout

def checkText (text : Array (Fin 2)) : IO Nat := do
  let index:=prepare text 0
  let bound:=6*text.size*(text.size.log2+1)
  unless index.sources.rows.size=text.size+1 && index.sources.memberships≤bound &&
      index.preparationWork≤text.size+3+11*bound do
    throw (IO.userError "fanout preparation exceeds its proved bounds")
  let mut checks:=0
  for p in [0:text.size+3] do
    let expected:=(index.runs.toList.zipIdx.filter fun (r,_)=>decide (r.lo≤p ∧ p≤r.hi)).map Prod.snd
    let cell:=read index.sources.rows p
    unless cell.ids==expected.reverse && cell.count=expected.length &&
        cell.ids.eraseDups.length=cell.ids.length do
      throw (IO.userError s!"fanout row mismatch n={text.size} p={p}")
    checks:=checks+1
  let positions:=(List.range (text.size+1)).filter (fun p=>p%2==0)
  let requests:=positions++positions.reverse++[text.size+2,text.size+2]
  let out:=drain requests index.sources
  let jobs:=out.deliveries.flatMap fun d=>d.affected.ids.map (fun id=>(d.source,id))
  let expectedJobs:=positions.flatMap fun p=>(read index.sources.rows p).ids.map (fun id=>(p,id))
  unless jobs.length=expectedJobs.length && jobs.all expectedJobs.contains &&
      jobs.eraseDups.length=jobs.length && out.visits=jobs.length && out.visits≤bound do
    throw (IO.userError "source removal lost or replayed an affected run ID")
  unless out.work=8*requests.length && out.remaining.work=index.sources.work+5*requests.length &&
      out.visits+out.remaining.memberships=index.sources.memberships do
    throw (IO.userError "source fanout delivery ledger mismatch")
  for p in [0:text.size+1] do
    let after:=read out.remaining.rows p
    let before:=read index.sources.rows p
    unless (if positions.contains p then after.ids.isEmpty else after.ids==before.ids) do
      throw (IO.userError "source removal changed an unrequested row")
  let rest:=drain (List.range (text.size+1)) out.remaining
  unless rest.visits+out.visits=index.sources.memberships && rest.remaining.memberships=0 do
    throw (IO.userError "remaining sources did not deliver the complementary memberships")
  return checks

def binary (n code : Nat) : Array (Fin 2) :=
  ((List.range n).map fun i=>(⟨(code/2^i)%2,Nat.mod_lt _ (by decide)⟩ : Fin 2)).toArray

def main : IO Unit := do
  let mut texts:=0
  let mut rows:=0
  for n in [0:8] do
    for code in [0:2^n] do
      rows:=rows+(←checkText (binary n code))
      texts:=texts+1
  let patterned:=((List.range 96).map fun i=>(if i%4=3 then 1 else 0 : Fin 2)).toArray
  rows:=rows+(←checkText patterned)
  let large:=prepare (Array.replicate 2048 (0 : Fin 2)) 0
  let out:=drain (List.range 2049++List.range 2049) large.sources
  unless out.visits=large.sources.memberships && out.remaining.memberships=0 do
    throw (IO.userError "large repeated deletion delivery failed")
  IO.println s!"source fanout texts={texts+1}, checked rows={rows}, exact reverse addresses and one-shot deliveries passed"
  IO.println s!"unary n=2048 runs={large.runs.size}, memberships={large.sources.memberships}, preparationWork={large.preparationWork}, delivered={out.visits}, repeated requests={out.calls}"
  IO.println "Fanout only constructs affected run IDs; mutable source indexes and cached-bank repairs are separately linked."
