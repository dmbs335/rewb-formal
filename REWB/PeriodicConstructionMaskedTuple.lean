import REWB.PeriodicConstructionMaskedBranch

/-! Actual joint-map adapter and tuple loop with all local periodic
formula/window construction included. The old Answer (including its
mask counters) is preserved exactly. No interval or exponent is scanned.
Joint-cut enumeration/index products are inputs to this local compiler
and retain their separate measured ledger. -/
namespace REWB.PeriodicConstruction.Masked
open REWB.PeriodicConstruction REWB.MaskedPeriodic REWB.MaskedFiniteAction.Maps
open REWB.MaskedCut.DFAIndex
variable {α : Type}

theorem tabulate_id (m : Nat) :
    (tabulate m (fun q : Fin m=>(q,1))).1=identity m := by
  apply Vector.ext
  intro i hi
  change (tabulate m (fun q=>(q,1))).1.get ⟨i,hi⟩=(identity m).get ⟨i,hi⟩
  simp only [tabulate_get,identity,BoundaryIndex.Table.get_ofFn,id_eq]

def fromTuple (B C E : DFA α) (period cut : Joint B C E) (after : Map E.stateCount) :
    Result (InputData B.stateCount C.stateCount E.stateCount) :=
  let ib:=tabulate B.stateCount (fun q=>(q,1))
  let ic:=tabulate C.stateCount (fun q=>(q,1))
  let b:=ofMaps B period.1 ib.1 cut.1
  let c:=ofMaps C period.2.1 cut.2.1 ic.1
  let e:=ofMaps E period.2.2 cut.2.2 after
  (⟨b.1,c.1,e.1⟩,ib.2+ic.2+b.2+c.2+e.2+4)

def fromTupleCost (b c e : Nat) : Nat := 10*b+10*c+6*e+21

theorem fromTuple_value (B C E : DFA α) (period cut : Joint B C E) (after : Map E.stateCount) :
    (fromTuple B C E period cut after).1.data=MaskedPeriodic.fromTuple B C E period cut after := by
  simp only [fromTuple,InputData.data,ofMaps_value,tabulate_id,MaskedPeriodic.fromTuple]

theorem fromTuple_work (B C E : DFA α) (period cut : Joint B C E) (after : Map E.stateCount) :
    (fromTuple B C E period cut after).2≤fromTupleCost B.stateCount C.stateCount E.stateCount := by
  have hiB:=tabulate_work (fun q : Fin B.stateCount=>(q,1)) 1 (fun _=>Nat.le_refl _)
  have hiC:=tabulate_work (fun q : Fin C.stateCount=>(q,1)) 1 (fun _=>Nat.le_refl _)
  have hB:=ofMaps_work B period.1 (tabulate B.stateCount (fun q=>(q,1))).1 cut.1
  have hC:=ofMaps_work C period.2.1 cut.2.1 (tabulate C.stateCount (fun q=>(q,1))).1
  have hE:=ofMaps_work E period.2.2 cut.2.2 after
  unfold fromTuple fromTupleCost
  dsimp only
  simp only [Nat.reduceAdd,Nat.mul_comm _ 4] at hiB hiC
  omega

def queryTuple (B C E : DFA α) (period cut : Joint B C E) (after : Map E.stateCount)
    (branch : Branch) (N : Nat) (counts : Array Nat) (base q s K : Nat) :
    Result MaskedProgression.Answer :=
  let data:=fromTuple B C E period cut after
  let out:=queryBranch data.1 branch N counts base q s K
  (out.1,data.2+out.2+1)

def tupleConstructionCost (b c e K : Nat) : Nat := fromTupleCost b c e+windowsCost b c e K+2

theorem queryTuple_value (B C E : DFA α) (period cut : Joint B C E) (after : Map E.stateCount)
    (branch : Branch) (N : Nat) (counts : Array Nat) (base q s K : Nat) :
    (queryTuple B C E period cut after branch N counts base q s K).1=
      MaskedPeriodic.queryBranch (MaskedPeriodic.fromTuple B C E period cut after)
        branch N counts base q s K := by
  simp only [queryTuple,queryBranch_value,fromTuple_value]

theorem queryTuple_extra (B C E : DFA α) (period cut : Joint B C E) (after : Map E.stateCount)
    (branch : Branch) (N : Nat) (counts : Array Nat) (base q s K : Nat) :
    (queryTuple B C E period cut after branch N counts base q s K).2≤
      (MaskedPeriodic.queryBranch (MaskedPeriodic.fromTuple B C E period cut after)
        branch N counts base q s K).slots+
      (MaskedPeriodic.queryBranch (MaskedPeriodic.fromTuple B C E period cut after)
        branch N counts base q s K).arithmetic+
      tupleConstructionCost B.stateCount C.stateCount E.stateCount K := by
  have hd:=fromTuple_work B C E period cut after
  have hq:=queryBranch_extra (fromTuple B C E period cut after).1 branch N counts base q s K
  rw [fromTuple_value] at hq
  unfold queryTuple tupleConstructionCost
  dsimp only
  omega

def tupleQuery (B C E : DFA α) (period : Joint B C E) (after : Map E.stateCount)
    (branch : Branch) (N : Nat) (counts : Array Nat) (base q s K : Nat) :
    List (Joint B C E)→Result MaskedProgression.Answer
  | [] => (⟨false,0,1⟩,2)
  | cut::rest =>
    let a:=queryTuple B C E period cut after branch N counts base q s K
    let z:=tupleQuery B C E period after branch N counts base q s K rest
    (⟨a.1.answer || z.1.answer,a.1.slots+z.1.slots,a.1.arithmetic+z.1.arithmetic+1⟩,a.2+z.2+5)

theorem tupleQuery_value (B C E : DFA α) (period : Joint B C E) (after : Map E.stateCount)
    (branch : Branch) (N : Nat) (counts : Array Nat) (base q s K : Nat) (cuts : List (Joint B C E)) :
    (tupleQuery B C E period after branch N counts base q s K cuts).1=
      MaskedPeriodic.tupleQuery B C E period after branch N counts base q s cuts K := by
  induction cuts with
  | nil => rfl
  | cons cut cuts ih => simp only [tupleQuery,queryTuple_value,ih,MaskedPeriodic.tupleQuery]

theorem tupleQuery_extra (B C E : DFA α) (period : Joint B C E) (after : Map E.stateCount)
    (branch : Branch) (N : Nat) (counts : Array Nat) (base q s K : Nat) (cuts : List (Joint B C E)) :
    (tupleQuery B C E period after branch N counts base q s K cuts).2≤
      (MaskedPeriodic.tupleQuery B C E period after branch N counts base q s cuts K).slots+
      (MaskedPeriodic.tupleQuery B C E period after branch N counts base q s cuts K).arithmetic+
      cuts.length*(tupleConstructionCost B.stateCount C.stateCount E.stateCount K+4)+1 := by
  induction cuts with
  | nil => simp [tupleQuery,MaskedPeriodic.tupleQuery]
  | cons cut cuts ih =>
    have h:=queryTuple_extra B C E period cut after branch N counts base q s K
    simp only [tupleQuery,MaskedPeriodic.tupleQuery,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem tupleQuery_length_le (B C E : DFA α) (period : Joint B C E) (after : Map E.stateCount)
    (branch : Branch) (N : Nat) (counts : Array Nat) (base q s K : Nat) (cuts : List (Joint B C E)) :
    cuts.length≤(MaskedPeriodic.tupleQuery B C E period after branch N counts base q s cuts K).slots+
      (MaskedPeriodic.tupleQuery B C E period after branch N counts base q s cuts K).arithmetic := by
  induction cuts with
  | nil => simp
  | cons cut cuts ih =>
    simp only [MaskedPeriodic.tupleQuery,List.length_cons]
    omega

theorem tupleQuery_inflate (B C E : DFA α) (period : Joint B C E) (after : Map E.stateCount)
    (branch : Branch) (N : Nat) (counts : Array Nat) (base q s K : Nat) (cuts : List (Joint B C E)) :
    (tupleQuery B C E period after branch N counts base q s K cuts).2≤
      (tupleConstructionCost B.stateCount C.stateCount E.stateCount K+6)*
      ((MaskedPeriodic.tupleQuery B C E period after branch N counts base q s cuts K).slots+
       (MaskedPeriodic.tupleQuery B C E period after branch N counts base q s cuts K).arithmetic+1) := by
  have h:=tupleQuery_extra B C E period after branch N counts base q s K cuts
  have hl:=Nat.mul_le_mul_right (tupleConstructionCost B.stateCount C.stateCount E.stateCount K+4)
    (tupleQuery_length_le B C E period after branch N counts base q s K cuts)
  let x:=(MaskedPeriodic.tupleQuery B C E period after branch N counts base q s cuts K).slots+
    (MaskedPeriodic.tupleQuery B C E period after branch N counts base q s cuts K).arithmetic
  let c:=tupleConstructionCost B.stateCount C.stateCount E.stateCount K
  change _≤(c+6)*(x+1)
  change _≤x+cuts.length*(c+4)+1 at h
  change cuts.length*(c+4)≤x*(c+4) at hl
  calc
    _≤x+cuts.length*(c+4)+1 := h
    _≤x+x*(c+4)+1 := Nat.add_le_add_right (Nat.add_le_add_left hl x) 1
    _≤(c+6)*(x+1) := by
      rw [Nat.mul_comm x (c+4)]
      simp only [Nat.add_mul,Nat.mul_add,Nat.mul_one,Nat.one_mul]
      omega

end REWB.PeriodicConstruction.Masked
