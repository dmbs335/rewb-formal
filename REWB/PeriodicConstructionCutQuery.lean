import REWB.PeriodicConstructionCutDFA
import REWB.PeriodicConstructionCutRange

/-! The counted three-range cut query preserves the complete original
result. Its bound includes all summary products, list-table reads and
the final transported matrix. A concrete DFA wrapper also accounts for
constructing its finite enumeration and materialized identity. -/
namespace REWB.PeriodicConstruction.Cut
open REWB.FiniteRelation REWB.MaskedCut.DFAIndex

variable {M : Type} [DecidableEq M] {o : RangeProducts.Ops M} {e : Enumeration M}

def indexQuery (k : Primitives o) (u : Universe e) (idx : MaskedCut.Index.Tree e)
    (l a b r : Nat) : Result (MaskedCut.Index.Result e) :=
  let algebra:=summaryProducts k u
  let left:=rangeQuery algebra idx l a
  let middle:=rangeQuery algebra idx a b
  let right:=rangeQuery algebra idx b r
  let products:=left.1.products+middle.1.products+right.1.products
  let visits:=left.1.visits+middle.1.visits+right.1.visits
  match left.1.answer,middle.1.answer,right.1.answer with
  | some x,some y,some z=>
    let out:=window k u x y z
    (⟨some out.1,products,visits⟩,algebra.unit.2+left.2+middle.2+right.2+out.2+10)
  | _,_,_=>(⟨none,products,visits⟩,algebra.unit.2+left.2+middle.2+right.2+10)

theorem indexQuery_value (k : Primitives o) (u : Universe e) (idx : MaskedCut.Index.Tree e)
    (l a b r : Nat) : (indexQuery k u idx l a b r).1=MaskedCut.Index.query o e idx l a b r := by
  simp only [indexQuery,rangeQuery_value,MaskedCut.Index.query]
  cases hl : (DyadicIndex.query (MaskedCut.ops o e) idx l a).answer <;>
    cases hm : (DyadicIndex.query (MaskedCut.ops o e) idx a b).answer <;>
    cases hr : (DyadicIndex.query (MaskedCut.ops o e) idx b r).answer <;>
    simp only [hl,hm,hr,Option.bind,Option.map,window_value]

def rangeCost (N C : Nat) : Nat := 2*summaryCost N C+20

theorem indexQuery_work (k : Primitives o) (u : Universe e) (idx : MaskedCut.Index.Tree e)
    (l a b r C : Nat) (hu : k.unit.2≤C)
    (hm : ∀x y,(k.multiply x y).2≤C) (he : ∀x y,(k.equal x y).2≤C) (ht : Tiny idx) :
    (indexQuery k u idx l a b r).2≤
      rangeCost e.elems.length C*((MaskedCut.Index.query o e idx l a b r).products+
        (MaskedCut.Index.query o e idx l a b r).visits)+windowCost e.elems.length C+oneCost e.elems.length C+10 := by
  have hunit:=summaryOne_work k u C hu
  have h1:=rangeQuery_work (summaryProducts k u) idx l a (summaryCost e.elems.length C)
    (summaryProducts_unit k u C hu) (summaryProducts_mul k u C hm he) ht
  have h2:=rangeQuery_work (summaryProducts k u) idx a b (summaryCost e.elems.length C)
    (summaryProducts_unit k u C hu) (summaryProducts_mul k u C hm he) ht
  have h3:=rangeQuery_work (summaryProducts k u) idx b r (summaryCost e.elems.length C)
    (summaryProducts_unit k u C hu) (summaryProducts_mul k u C hm he) ht
  simp only [indexQuery]
  split
  · rename_i x y z hx hy hz
    have hw:=window_work k u x y z C hu hm he
    dsimp only
    simp only [MaskedCut.Index.query,rangeCost,summaryProducts,Nat.mul_add] at h1 h2 h3 ⊢
    omega
  · dsimp only
    simp only [MaskedCut.Index.query,rangeCost,summaryProducts,Nat.mul_add] at h1 h2 h3 ⊢
    omega

theorem absorb (A B x : Nat) : A*x+B≤(A+B)*(x+1) := by
  simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one]
  omega

def queryIndex (B C E : DFA α) (idx : MaskedCut.Index.Tree (jointEnum B C E))
    (l a b r : Nat) : Result (MaskedCut.Index.Result (jointEnum B C E)) :=
  let env:=prepare B C E
  let out:=indexQuery env.1.kernel env.1.catalog idx l a b r
  (out.1,env.2+out.2+2)

theorem queryIndex_value (B C E : DFA α) (idx : MaskedCut.Index.Tree (jointEnum B C E))
    (l a b r : Nat) :
    (queryIndex B C E idx l a b r).1=MaskedCut.Index.query (jointOps B C E) (jointEnum B C E) idx l a b r := by
  simp only [queryIndex,indexQuery_value]

def indexCoefficient (b c e : Nat) : Nat :=
  prepareCost b c e+rangeCost (cardinality b c e) (primitiveCost b c e)+
    windowCost (cardinality b c e) (primitiveCost b c e)+
    oneCost (cardinality b c e) (primitiveCost b c e)+12

theorem queryIndex_work (B C E : DFA α) (idx : MaskedCut.Index.Tree (jointEnum B C E))
    (l a b r : Nat) (ht : Tiny idx) :
    (queryIndex B C E idx l a b r).2≤indexCoefficient B.stateCount C.stateCount E.stateCount*
      ((MaskedCut.Index.query (jointOps B C E) (jointEnum B C E) idx l a b r).products+
       (MaskedCut.Index.query (jointOps B C E) (jointEnum B C E) idx l a b r).visits+1) := by
  have h:=indexQuery_work (prepare B C E).1.kernel (prepare B C E).1.catalog idx l a b r
    (primitiveCost B.stateCount C.stateCount E.stateCount)
    (primitives_unit B C E) (primitives_mul B C E) (primitives_equal B C E) ht
  have hp:=prepare_work B C E
  rw [enum_cardinality] at h
  have ha:=absorb (rangeCost (cardinality B.stateCount C.stateCount E.stateCount)
      (primitiveCost B.stateCount C.stateCount E.stateCount))
    (prepareCost B.stateCount C.stateCount E.stateCount+
      windowCost (cardinality B.stateCount C.stateCount E.stateCount)
        (primitiveCost B.stateCount C.stateCount E.stateCount)+
      oneCost (cardinality B.stateCount C.stateCount E.stateCount)
        (primitiveCost B.stateCount C.stateCount E.stateCount)+12)
    ((MaskedCut.Index.query (jointOps B C E) (jointEnum B C E) idx l a b r).products+
      (MaskedCut.Index.query (jointOps B C E) (jointEnum B C E) idx l a b r).visits)
  dsimp only [queryIndex,indexCoefficient]
  have heq : prepareCost B.stateCount C.stateCount E.stateCount+
      rangeCost (cardinality B.stateCount C.stateCount E.stateCount)
        (primitiveCost B.stateCount C.stateCount E.stateCount)+
      windowCost (cardinality B.stateCount C.stateCount E.stateCount)
        (primitiveCost B.stateCount C.stateCount E.stateCount)+
      oneCost (cardinality B.stateCount C.stateCount E.stateCount)
        (primitiveCost B.stateCount C.stateCount E.stateCount)+12=
      rangeCost (cardinality B.stateCount C.stateCount E.stateCount)
        (primitiveCost B.stateCount C.stateCount E.stateCount)+
      (prepareCost B.stateCount C.stateCount E.stateCount+
       windowCost (cardinality B.stateCount C.stateCount E.stateCount)
         (primitiveCost B.stateCount C.stateCount E.stateCount)+
       oneCost (cardinality B.stateCount C.stateCount E.stateCount)
         (primitiveCost B.stateCount C.stateCount E.stateCount)+12) := by omega
  rw [heq]
  exact Nat.le_trans (by omega) ha

def queryRange (B C E : DFA α) (idx : MaskedCut.Index.Tree (jointEnum B C E))
    (l r : Nat) : Result (DyadicIndex.Result (MaskedCut.Summary (jointEnum B C E))) :=
  let env:=prepare B C E
  let algebra:=summaryProducts env.1.kernel env.1.catalog
  let out:=rangeQuery algebra idx l r
  (out.1,env.2+algebra.unit.2+out.2+2)

theorem queryRange_value (B C E : DFA α) (idx : MaskedCut.Index.Tree (jointEnum B C E)) (l r : Nat) :
    (queryRange B C E idx l r).1=DyadicIndex.query (MaskedCut.ops (jointOps B C E) (jointEnum B C E)) idx l r := by
  simp only [queryRange,rangeQuery_value]

def rangeCoefficient (b c e : Nat) : Nat :=
  prepareCost b c e+rangeCost (cardinality b c e) (primitiveCost b c e)+
    oneCost (cardinality b c e) (primitiveCost b c e)+2

theorem queryRange_work (B C E : DFA α) (idx : MaskedCut.Index.Tree (jointEnum B C E))
    (l r : Nat) (ht : Tiny idx) :
    (queryRange B C E idx l r).2≤rangeCoefficient B.stateCount C.stateCount E.stateCount*
      ((DyadicIndex.query (MaskedCut.ops (jointOps B C E) (jointEnum B C E)) idx l r).products+
       (DyadicIndex.query (MaskedCut.ops (jointOps B C E) (jointEnum B C E)) idx l r).visits+1) := by
  have h:=rangeQuery_work (summaryProducts (prepare B C E).1.kernel (prepare B C E).1.catalog) idx l r
    (summaryCost (jointEnum B C E).elems.length (primitiveCost B.stateCount C.stateCount E.stateCount))
    (summaryProducts_unit _ _ _ (primitives_unit B C E))
    (summaryProducts_mul _ _ _ (primitives_mul B C E) (primitives_equal B C E)) ht
  have hp:=prepare_work B C E
  have hu:=summaryOne_work (prepare B C E).1.kernel (prepare B C E).1.catalog
    (primitiveCost B.stateCount C.stateCount E.stateCount) (primitives_unit B C E)
  rw [enum_cardinality] at h
  rw [enum_cardinality] at hu
  have ha:=absorb (rangeCost (cardinality B.stateCount C.stateCount E.stateCount)
      (primitiveCost B.stateCount C.stateCount E.stateCount))
    (prepareCost B.stateCount C.stateCount E.stateCount+
      oneCost (cardinality B.stateCount C.stateCount E.stateCount)
        (primitiveCost B.stateCount C.stateCount E.stateCount)+2)
    ((DyadicIndex.query (MaskedCut.ops (jointOps B C E) (jointEnum B C E)) idx l r).products+
      (DyadicIndex.query (MaskedCut.ops (jointOps B C E) (jointEnum B C E)) idx l r).visits)
  dsimp only [queryRange,rangeCoefficient,rangeCost,summaryProducts] at h ha ⊢
  have he : prepareCost B.stateCount C.stateCount E.stateCount+
      (2*summaryCost (cardinality B.stateCount C.stateCount E.stateCount)
      (primitiveCost B.stateCount C.stateCount E.stateCount)+20)+
      oneCost (cardinality B.stateCount C.stateCount E.stateCount)
        (primitiveCost B.stateCount C.stateCount E.stateCount)+2=
      (2*summaryCost (cardinality B.stateCount C.stateCount E.stateCount)
      (primitiveCost B.stateCount C.stateCount E.stateCount)+20)+
      (prepareCost B.stateCount C.stateCount E.stateCount+
       oneCost (cardinality B.stateCount C.stateCount E.stateCount)
         (primitiveCost B.stateCount C.stateCount E.stateCount)+2) := by omega
  rw [he]
  exact Nat.le_trans (by omega) ha

theorem dfaBuild_tiny (B C E : DFA α) (w : Word α) : Tiny (MaskedCut.DFAIndex.build B C E w).1 :=
  buildFor_tiny _ _

end REWB.PeriodicConstruction.Cut
