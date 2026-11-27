import REWB.MaskedTraversalCompleteRegression
import REWB.MaskedTraversalBankReadySemantics

/-! Actual descriptor/catalog/bank/window execution versus independent
original-cut and dense-gap enumeration. Reference scans live only here.
The tested queries receive no physical path, supplied cluster/AP list,
selected run ID, answer table, or supplied cut answer. -/
namespace REWB.MaskedTraversalComplete.Audit
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedTraversalAggregate

abbrev all : DFA (Fin 3) := ⟨1,0,fun _ _=>0,fun _=>true⟩
abbrev eps : DFA (Fin 3) := ⟨2,0,fun _ _=>1,fun q=>q==0⟩
abbrev even : DFA (Fin 3) := ⟨2,0,fun q _=>if q==0 then 1 else 0,fun q=>q==0⟩

def check (b : Bool) (message : String) : IO Unit := unless b do throw (IO.userError message)

def occurrences (w : Word (Fin 3)) (base L : Nat) : List Nat :=
  (List.range (w.length+1)).filter fun p=>decide (p+L≤w.length) &&
    (Spec.slice w p (p+L)==Spec.slice w base (base+L))

/-- Independent class-component reference: only sorted physical starts
and the numerical dense-gap condition, without descriptor/tree queries. -/
def tagged (xs : List Nat) (L : Nat) : List (Nat×Nat) :=
  match xs with
  | []=>[]
  | p::ps=>(ps.foldl (fun state q=>
      let first:=if 2*(q-state.1)≤L then state.2.1 else q
      (q,first,(q,first)::state.2.2)) (p,p,[(p,p)])).2.2.reverse

def accepted (A : DFA α) (w : Word α) : Bool := A.final (A.run A.initial w)

def cuts (B C E : DFA (Fin 3)) (w : Word (Fin 3)) (base low high : Nat)
    (different : Bool) : List (Nat×Nat) :=
  (List.range (high-low+1)).flatMap fun offset=>
    let L:=low+offset
    let members:=tagged (occurrences w base L) L
    members.flatMap fun p=>members.filterMap fun j=>
      if (!different || p.2!=j.2) && decide (p.1+L≤j.1 ∧ j.1+L≤w.length) &&
          (Spec.slice w p.1 (p.1+L)==Spec.slice w j.1 (j.1+L)) &&
          accepted B (Spec.slice w p.1 (p.1+L)) && accepted C (Spec.slice w (p.1+L) j.1) &&
          accepted E (Spec.slice w (j.1+L) w.length) then some (p.1,j.1) else none

def reference (candidates : List (Nat×Nat)) (source target : Array Bool) (lo hi : Nat) : Bool :=
  candidates.any fun pair=>decide (lo≤pair.1 ∧ pair.1<hi) &&
    source[pair.1]?.getD false && target[pair.2]?.getD false

structure Stats where
  queries : Nat := 0
  positive : Nat := 0
  erased : Nat := 0
  sameOnly : Nat := 0
  incoming : Nat := 0
  maximum : Nat := 0
  deriving Repr

def fixture (label : String) (B C E : DFA (Fin 3)) (text : Array (Fin 3))
    (base reset current low : Nat) (sourceOnly targetOnly : Option Nat) (erases : List Nat) : IO Stats := do
  let w:=text.toList
  let n:=text.size
  let height:=(n+1).log2+1
  let capacity:=2^height
  let xs:=occurrences w base reset
  let partition:=(MaskedClusterLeaders.execute height reset
    (xs.reverse.map MaskedClusterLeaders.Operation.insert)).state
  let leaders:=partition.leaders.entries
  for L in List.range (current-low+1) do
    let fresh:=occurrences w base (low+L)
    check (fresh==xs) s!"{label}: tested length band changes full class"
    let expected:=(tagged fresh (low+L)).filterMap fun pair=>if pair.1==pair.2 then some pair.1 else none
    check (expected==leaders) s!"{label}: tested length band changes leaders"
  let source:=Array.ofFn fun p : Fin (n+1)=>match sourceOnly with
    | none=>true
    | some q=>decide (p.val=q)
  let target:=Array.ofFn fun p : Fin (n+1)=>match targetOnly with
    | none=>true
    | some q=>decide (p.val=q)
  let book:=ReplayMaps.prepare C.stateCount E.stateCount
  let prepared:=MaskedCluster.prepare C.stateCount E.stateCount
  let ci:=BoundaryApplication.Range.build C w
  let ei:=BoundaryApplication.Range.build E w
  let env:Clip.Env C E:=⟨book,prepared,ci,ei,target⟩
  let sources:=MaskedMutableProgression.Batch.prepare text 0 source prepared.K
  let catalog:=MaskedRunCatalog.ofBatch target sources
  let classes:=MaskedSuffixClass.prepare text 0
  let anchors:=Array.replicate (n+1) (some reset)
  let mut st:=Mutable.Store.empty C E sources
  let mut stats:Stats:={}
  for first in leaders do
    st:=MaskedTraversalBankReady.write C E book prepared ci ei partition capacity first reset anchors
      ⟨true,0,n+1⟩ catalog classes target st
    let some entry:=st.slots[first]?.join | throw (IO.userError s!"{label}: actual bank missing")
    if entry.config.incomingEnabled then stats:={stats with incoming:=stats.incoming+1}
  let initial:=(refreshMany st leaders (fresh (prepare C E height)).1).1
  let mut tree:=if current<reset then
      (shorten (bankAction (replay C E ci ei base current reset).maps) initial).1 else initial
  let cut:=Cut.build B C E w
  let candidates:=cuts B C E w base low current true
  let unfiltered:=cuts B C E w base low current false
  let windows:=if n≤14 then
      (List.range (n+3)).flatMap fun lo=>(List.range (n+3)).map fun hi=>(lo,hi)
    else [(0,n+1),(0,0),(n+1,n+1),(n+2,0),(n+1,n+2)]++
      (List.range 17).flatMap fun i=>let p:=i*n/16; [(p,p+1),(p,n+1),(0,p)]
  let mut live:=source
  for version in List.range (erases.length+1) do
    for bounds in windows do
      let out:=queryWindow B C E cut env st partition capacity tree bounds.1 bounds.2 base low current current
      let expected:=reference candidates live target bounds.1 bounds.2
      check (out.band.answer==expected)
        s!"{label}: version={version}, window={bounds}, actual={out.band.answer}, expected={expected}"
      check (decide (out.bankCalls≤2 ∧ out.queries≤1)) s!"{label}: query counters"
      stats:={stats with
        queries:=stats.queries+1
        positive:=stats.positive+(if expected then 1 else 0)
        sameOnly:=stats.sameOnly+(if !expected && reference unfiltered live target bounds.1 bounds.2 then 1 else 0)
        maximum:=max stats.maximum out.clippingWork}
    if let some p:=erases[version]? then
      let before:=tree
      let saved:=(queryWindow B C E cut env st partition capacity tree 0 (n+1) base low current current).band.answer
      let changed:=eraseCurrent env partition capacity current p st tree
      check changed.ready s!"{label}: actual current-length erasure failed"
      check (decide (changed.calls≤1)) s!"{label}: multiple erased banks"
      let replayed:=(queryWindow B C E cut env st partition capacity before 0 (n+1) base low current current).band.answer
      check (replayed==saved) s!"{label}: earlier persistent version changed"
      st:=changed.store
      tree:=changed.tree
      live:=live.setIfInBounds p false
      stats:={stats with erased:=stats.erased+1}
  IO.println s!"completeFixture {label} n={n} lengths={low}..{current} retained={reset} class={xs.length} leaders={leaders.length} {repr stats}"
  (←IO.getStdout).flush
  return stats

def run : IO Unit := do
  let begin←IO.monoMsNow
  let overlap : Array (Fin 3):=#[0,1,0,0,1,0,1,0,0,1,0,0,1,0]
  let shortened : Array (Fin 3):=#[0,1,0,1,0,1,0,1,0,2,2,2,0,1,0,1,0]
  let a←fixture "adjacent-dense-overshoot" all all all overlap 0 6 6 6 (some 0) (some 8) [5,0,0]
  let b←fixture "overshoot-forbids-first-target" all all all overlap 0 6 6 6 (some 0) (some 5) []
  let c←fixture "same-dense-cluster-excluded" all all all #[0,0,0,0,0,0,0,0] 0 2 2 2 none none [0,1]
  let d←fixture "terminal-empty-suffix" all all eps #[0,1,0] 0 1 1 1 (some 0) (some 2) []
  let e←fixture "nonempty-suffix-rejected" all all eps #[0,1,0,1] 0 1 1 1 (some 0) (some 2) []
  let f←fixture "retained-anchor-shortening" all even all shortened 0 5 4 4 none (some 12) [0,2,4,1]
  let deep:=Array.ofFn fun i : Fin 128=>if i.val%4=0 then (0 : Fin 3) else 1
  let g←fixture "deep-sparse-bank-chain" all all all deep 0 1 1 1 none none [0,4,1]
  check (a.positive>0 && a.incoming>0 && b.positive==0 && c.positive==0 && c.sameOnly>0 &&
    d.positive>0 && e.positive==0 && f.positive>0 && g.positive>0) "required path/negative branches absent"
  let stats:=[a,b,c,d,e,f,g]
  let finish←IO.monoMsNow
  IO.println s!"completeQuery fixtures=7 queries={(stats.map (·.queries)).sum} positive={(stats.map (·.positive)).sum} sameClusterOnly={(stats.map (·.sameOnly)).sum} erases={(stats.map (·.erased)).sum} mismatches=0 elapsed={finish-begin}ms"

end REWB.MaskedTraversalComplete.Audit

def main : IO Unit := REWB.MaskedTraversalComplete.Audit.run
