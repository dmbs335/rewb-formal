import REWB.BoundaryApplicationSubset
open REWB REWB.BoundaryApplication

def aMachine : DFA (Fin 2) := ⟨2,0,fun q _=>⟨(q.val+1)%2,by omega⟩,fun q=>decide (q=0)⟩
def bMachine : DFA (Fin 2) := aMachine
def dMachine : DFA (Fin 2) := ⟨2,0,fun _ a=>a,fun q=>decide (q=0)⟩
def eMachine : DFA (Fin 2) := ⟨2,0,fun _ _=>1,fun _=>true⟩

def auditNode (w : Word (Fin 2)) (g : Nat) (shared : RTable.Shared aMachine bMachine dMachine)
    (blank : BoundaryIndex.Merge.State (Subset.count aMachine) 2 (height w.length))
    (t : TrieFor w) (s : Versions.Snapshot 2 2 (height w.length)) : IO (Nat×Nat) := do
  let rtable := RTable.node aMachine bMachine dMachine w shared t
  let source := (Versions.root s).state
  let lifted := Lift.importMany rtable.map source.tree source.positions blank
  unless lifted.1.cachedSize == source.cachedSize do throw (IO.userError "empty subset color lost a live record")
  let targets := t.leaves.filterMap fun a=>match a.record with
    | .source _ => none
    | .target p => some p
  let endpoint := w.length-(representative w t).start
  for alpha in (List.ofFn id : List (Fin 2)) do
    for right in List.range (w.length+1) do
      let actual := (BoundaryIndex.TokenIndex.query eMachine
        (BoundaryIndex.Colors.select aMachine alpha) lifted.1.tree (right+1)).1
      let expected := targets.any fun target=>
        decide (target.val≤right) &&
        eMachine.final (eMachine.run eMachine.initial (Spec.slice w target.val right)) &&
        (List.range (t.depth+1)).any fun len=>
          let first := Spec.slice w (endpoint-t.depth) (endpoint-len)
          aMachine.final (aMachine.run alpha first) &&
          dMachine.final (dMachine.run (color dMachine w g target t.depth) first) &&
          bMachine.final (bMachine.run bMachine.initial (Spec.slice w (endpoint-len) endpoint))
      unless actual == expected do throw (IO.userError s!"node R/lift query mismatch depth={t.depth}, right={right}")
  match t,s with
  | .node _ _ l r,.node _ _ a b =>
      let left ← auditNode w g shared blank l a
      let right ← auditNode w g shared blank r b
      pure (left.1+right.1+1,left.2+right.2+lifted.2)
  | .leaf _,.leaf _ => pure (1,lifted.2)
  | _,_ => throw (IO.userError "node R snapshot topology mismatch")

def main : IO Unit := do
  let w : Word (Fin 2) := (List.range 16).map fun i=>⟨(i/3+i)%2,by omega⟩
  let idx := FixedEnd.build dMachine eMachine w 0 7
    (by simp only [w,List.length_map,List.length_range]; omega)
  let base := BoundaryIndex.MergeBuild.prepare (k:=Subset.count aMachine) (FixedEnd.rows eMachine w) (height w.length)
  let blank : BoundaryIndex.Merge.State (Subset.count aMachine) 2 (height w.length) := ⟨base.1,[],0⟩
  let shared := RTable.prepare aMachine bMachine dMachine w
  let checked ← auditNode w 7 shared blank idx.trie.tree idx.versions
  IO.println s!"nodeRows={checked.1} heterogeneousSubsetQueries=true allClosedCuts=true importWork={checked.2} subsetColors={Subset.count aMachine}"
