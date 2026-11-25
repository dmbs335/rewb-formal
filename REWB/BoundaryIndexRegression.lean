import REWB.BoundaryIndexQuery

/-! Kernel-checked regressions for the persistent colored aggregate.
The DFA below has a noninjective transition: either state becomes 1 after
any letter. In particular a later suffix state cannot recover whether an
earlier empty suffix was accepting. -/
namespace REWB.BoundaryIndex.Regression

def reset : DFA Bool :=
  ⟨2,0,fun _ _=>1,fun q=>decide (q=0)⟩

def select (c : Fin 3) : Fin 3→Bool := fun d=>decide (d=c)

def base : Tree 3 2 2 :=
  (TokenIndex.build reset [Token.mark 1,Token.letter false,Token.mark 2] 2).1

def collapse : Vector (Fin 3) 3 := Vector.ofFn (fun _=>0)

def merged : Tree 3 2 2 := (Tree.recolor collapse base).1

def inserted : Tree 3 2 2 := (Tree.insert merged 1 1 reset.initial).1

/-- Both colors remain available at their respective right boundaries
when their classes coalesce into zero. -/
theorem coalescing_endpoints :
    (TokenIndex.query reset (select 0) merged 1).1=true ∧
    (TokenIndex.query reset (select 0) merged 3).1=true := by decide

/-- A query at the earlier boundary accepts its empty suffix. The next
boundary rejects after reading a letter, and the final marker accepts again. -/
theorem exact_right_boundary :
    (TokenIndex.query reset (select 0) merged 1).1=true ∧
    (TokenIndex.query reset (select 0) merged 2).1=false ∧
    (TokenIndex.query reset (select 0) merged 3).1=true := by decide

/-- An endpoint inserted after a pending collapse keeps its new color 1. -/
theorem fresh_color_survives :
    (TokenIndex.query reset (select 1) inserted 2).1=true ∧
    (TokenIndex.query reset (select 0) inserted 2).1=false := by decide

/-- Earlier versions are still independently queryable. -/
theorem old_versions_preserved :
    (TokenIndex.query reset (select 1) base 1).1=true ∧
    (TokenIndex.query reset (select 0) base 1).1=false ∧
    (TokenIndex.query reset (select 1) merged 2).1=false := by decide

/-- The full subset encoding realizes a preimage even for the constant
transition that merges all original DFA states. -/
theorem concrete_preimage :
    let tr : Vector (Fin 2) 2 := Vector.ofFn (fun _=>1)
    let c := Colors.encode reset (fun q : Fin 2=>decide (q=(1 : Fin 2)))
    Colors.decode reset ((Colors.preimageMap reset tr).get c) (0 : Fin 2)=true ∧
    Colors.decode reset ((Colors.preimageMap reset tr).get c) (1 : Fin 2)=true := by
  simp only [Colors.preimageMap_correct,Colors.decode_encode,Table.get_ofFn]
  decide

end REWB.BoundaryIndex.Regression
