import REWB.PeriodicConstructionCutQuery
import REWB.MaskedPeriodicTuples

/-! Measured finite tuple extraction. The filter ranges over the fixed
transformation universe, and every candidate's joint-cut lookup is
accounted for. The output order and duplicate behavior match the frozen
tuple lists exactly. -/
namespace REWB.PeriodicConstruction.Cut
open REWB.FiniteRelation REWB.MaskedCut.DFAIndex

variable {M : Type} [DecidableEq M] {o : RangeProducts.Ops M} {e : Enumeration M}

def extractCell (k : Primitives o) (select : M→M→Result M) (table : MatrixTable.Matrix e)
    (target p s : M) : Result Bool :=
  let r:=read k table p s
  if r.1 then
    let selected:=select p s
    let eq:=k.equal selected.1 target
    (eq.1,r.2+selected.2+eq.2+3)
  else (false,r.2+1)

theorem extractCell_value (k : Primitives o) (select : M→M→Result M)
    (table : MatrixTable.Matrix e) (target p s : M) :
    (extractCell k select table target p s).1=
      (MatrixTable.denote table p s && decide ((select p s).1=target)) := by
  simp only [extractCell,read_value,k.equal_value]
  cases h : MatrixTable.denote table p s <;> simp [h]

def extract (k : Primitives o) (u : Universe e) (select : M→M→Result M)
    (table : MatrixTable.Matrix e) : Result (List M) :=
  Orbit.filter (fun target=>finiteAny u (fun p=>finiteAny u (extractCell k select table target p))) u.values

theorem extract_value (k : Primitives o) (u : Universe e) (select : M→M→Result M)
    (table : MatrixTable.Matrix e) :
    (extract k u select table).1=e.elems.filter (fun target=>
      FiniteRelation.any e (fun p=>FiniteRelation.any e (fun s=>
        MatrixTable.denote table p s && decide ((select p s).1=target)))) := by
  simp only [extract,Orbit.filter_value,finiteAny_value,extractCell_value,u.values_eq]

def extractCellCost (N C : Nat) : Nat := readCost N C+2*C+3
def extractCost (N C : Nat) : Nat := N*(N*(N*(extractCellCost N C+2)+3)+3)+1

theorem extractCell_work (k : Primitives o) (select : M→M→Result M)
    (table : MatrixTable.Matrix e) (target p s : M) (C : Nat)
    (he : ∀a b,(k.equal a b).2≤C) (hs : ∀a b,(select a b).2≤C) :
    (extractCell k select table target p s).2≤extractCellCost e.elems.length C := by
  have hr:=read_work k table p s C he
  have hsel:=hs p s
  have heq:=he (select p s).1 target
  simp only [extractCell]
  split <;> dsimp only [extractCellCost] <;> omega

theorem extract_work (k : Primitives o) (u : Universe e) (select : M→M→Result M)
    (table : MatrixTable.Matrix e) (C : Nat)
    (he : ∀a b,(k.equal a b).2≤C) (hs : ∀a b,(select a b).2≤C) :
    (extract k u select table).2≤extractCost e.elems.length C := by
  have hf : ∀target,(finiteAny u (fun p=>finiteAny u (extractCell k select table target p))).2≤
      e.elems.length*(e.elems.length*(extractCellCost e.elems.length C+2)+3)+1 := by
    intro target
    apply finiteAny_work
    intro p
    exact finiteAny_work u (extractCell k select table target p) (extractCellCost e.elems.length C)
      (fun s=>extractCell_work k select table target p s C he hs)
  have h:=Orbit.filter_work
    (fun target=>finiteAny u (fun p=>finiteAny u (extractCell k select table target p))) u.values
    (e.elems.length*(e.elems.length*(extractCellCost e.elems.length C+2)+3)+1)
    (fun target _=>hf target)
  simpa only [extract,extractCost,u.values_eq,Nat.add_assoc,Nat.reduceAdd] using h

def selectFull (B C E : DFA α) (p s : Joint B C E) : Result (Joint B C E) :=
  ((p.1,s.2.1,s.2.2),3)

def selectConstrained (B C E : DFA α) (tail p s : Joint B C E) : Result (Joint B C E) :=
  let c:=compose s.2.1 tail.2.1
  ((p.1,c.1,s.2.2),c.2+3)

theorem selectConstrained_value (B C E : DFA α) (tail p s : Joint B C E) :
    (selectConstrained B C E tail p s).1=constrained B C E p s tail := by
  simp only [selectConstrained,compose_value,constrained]

theorem selectFull_work (B C E : DFA α) (p s : Joint B C E) :
    (selectFull B C E p s).2≤primitiveCost B.stateCount C.stateCount E.stateCount := by
  simp only [selectFull,primitiveCost]
  omega

theorem selectConstrained_work (B C E : DFA α) (tail p s : Joint B C E) :
    (selectConstrained B C E tail p s).2≤primitiveCost B.stateCount C.stateCount E.stateCount := by
  have h:=compose_work s.2.1 tail.2.1
  dsimp only [selectConstrained,primitiveCost]
  omega

def fullTuples (B C E : DFA α) : Option (MatrixTable.Matrix (jointEnum B C E))→Result (List (Joint B C E))
  | none=>([],1)
  | some table=>
    let env:=prepare B C E
    let out:=extract env.1.kernel env.1.catalog (selectFull B C E) table
    (out.1,env.2+out.2+2)

theorem fullTuples_value (B C E : DFA α) (answer : Option (MatrixTable.Matrix (jointEnum B C E))) :
    (fullTuples B C E answer).1=MaskedPeriodic.fullTuples B C E answer := by
  cases answer with
  | none=>rfl
  | some table=>
    simp only [fullTuples,extract_value,selectFull,MaskedPeriodic.fullTuples,
      MaskedPeriodic.fullContains,MaskedPeriodic.fullTuple,Option.map,Option.getD_some]
    rfl

def tupleCost (b c e : Nat) : Nat := prepareCost b c e+
  extractCost (cardinality b c e) (primitiveCost b c e)+2

theorem fullTuples_work (B C E : DFA α) (answer : Option (MatrixTable.Matrix (jointEnum B C E))) :
    (fullTuples B C E answer).2≤tupleCost B.stateCount C.stateCount E.stateCount := by
  cases answer with
  | none=>simp only [fullTuples,tupleCost]; omega
  | some table=>
    have hp:=prepare_work B C E
    have he:=extract_work (prepare B C E).1.kernel (prepare B C E).1.catalog
      (selectFull B C E) table (primitiveCost B.stateCount C.stateCount E.stateCount)
      (primitives_equal B C E) (selectFull_work B C E)
    rw [enum_cardinality] at he
    dsimp only [fullTuples,tupleCost]
    omega

def constrainedTuples (B C E : DFA α) (out : ConstrainedOutput B C E) : Result (List (Joint B C E)) :=
  let env:=prepare B C E
  let result:=extract env.1.kernel env.1.catalog (selectConstrained B C E out.tail) out.cuts
  (result.1,env.2+result.2+2)

theorem constrainedTuples_value (B C E : DFA α) (out : ConstrainedOutput B C E) :
    (constrainedTuples B C E out).1=(out.tuples B C E).toList := by
  simp only [constrainedTuples,extract_value,selectConstrained_value,ConstrainedOutput.tuples,
    ConstrainedOutput.contains,List.toList_toArray]
  rfl

theorem constrainedTuples_work (B C E : DFA α) (out : ConstrainedOutput B C E) :
    (constrainedTuples B C E out).2≤tupleCost B.stateCount C.stateCount E.stateCount := by
  have hp:=prepare_work B C E
  have he:=extract_work (prepare B C E).1.kernel (prepare B C E).1.catalog
    (selectConstrained B C E out.tail) out.cuts (primitiveCost B.stateCount C.stateCount E.stateCount)
    (primitives_equal B C E) (selectConstrained_work B C E out.tail)
  rw [enum_cardinality] at he
  dsimp only [constrainedTuples,tupleCost]
  omega

end REWB.PeriodicConstruction.Cut
