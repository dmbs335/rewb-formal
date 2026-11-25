import REWB.MaskedPeriodicBatchScan

/-! Input-length bounds for the existing periodic query ledger. These
include range products/visits and mask-query scalar/slot work. Descriptor,
projection and interval construction retain their separately stated scope;
this file does not assert a complete machine-time bound for that compiler.
-/
namespace REWB.MaskedPeriodic.Batch
open REWB.MaskedFiniteAction.Maps REWB.MaskedCut REWB.MaskedCut.DFAIndex REWB.Spec
variable {α : Type}

def queryLimit (b c e : DFA α) (n : Nat) : Nat :=
  tupleWork b.stateCount c.stateCount e.stateCount*((jointEnum b c e).elems.length*2+1)+
    10*(n.log2+2)+24

theorem phase_mask_work (b c e : DFA α)
    (prepared : PreparedPattern b.stateCount c.stateCount e.stateCount)
    (idx : Index.Tree (jointEnum b c e)) (tail : Map e.stateCount)
    (s eta q N : Nat) (counts : Array Nat) (base : Nat) :
    (phaseQuery b c e prepared idx tail s eta q N counts base s).result.slots+
      (phaseQuery b c e prepared idx tail s eta q N counts base s).result.arithmetic≤
        tupleWork b.stateCount c.stateCount e.stateCount*((jointEnum b c e).elems.length*2+1)+4 := by
  simp only [phaseQuery]
  split
  next period after hp ha =>
    have hz:=queryBranch_work (fromTuple b c e period (wordTuple b c e [] [] []) after)
      .zero N counts base q s
    have hi:=queryInterior_mask_work b c e idx s q period after N counts base s
    have he:=queryEnding_mask_work b c e idx s eta q period tail N counts base s
    simp only [prepared.exact,joinAnswers]
    simp only [queryInterior,queryEnding] at hi he
    simp only [queryInterior,queryEnding]
    rw [Nat.mul_add,Nat.mul_one,←Nat.mul_assoc]
    unfold tupleWork at hz hi he ⊢
    omega
  next hp => simp only [Nat.zero_add]; omega

theorem phase_range_work (b c e : DFA α)
    (prepared : PreparedPattern b.stateCount c.stateCount e.stateCount)
    (w : Word α) (tail : Map e.stateCount) (s eta q N : Nat)
    (counts : Array Nat) (base : Nat) (he : eta≤q) (hn : s+q≤w.length) :
    (phaseQuery b c e prepared (DFAIndex.build b c e w).1 tail s eta q N counts base s).products≤9 ∧
      (phaseQuery b c e prepared (DFAIndex.build b c e w).1 tail s eta q N counts base s).visits≤
        10*(w.length.log2+2) := by
  have hc:=contexts_bounds b c e w s eta q tail he hn
  have hi:=interiorTuples_bounds b c e w s q hn
  have hx:=endingTuples_bounds b c e w s eta q he hn
  simp only [phaseQuery]
  split
  · simp only [queryInterior,queryEnding]
    constructor <;> omega
  · dsimp only
    constructor <;> omega

theorem query_work (b c e : DFA α)
    (prepared : PreparedPattern b.stateCount c.stateCount e.stateCount)
    (w : Word α) (tail : Map e.stateCount) (s R q : Nat)
    (counts : Array Nat) (base : Nat) (hn : R≤w.length) :
    queryCost (Text.query b c e prepared (DFAIndex.build b c e w).1 tail s R q counts base)≤
      queryLimit b c e w.length := by
  by_cases hg : 0<q ∧ s+q≤R
  · have hm:=phase_mask_work b c e prepared (DFAIndex.build b c e w).1 tail
      s ((R-s)%q) q ((R-s)/q) counts base
    have hr:=phase_range_work b c e prepared w tail s ((R-s)%q) q ((R-s)/q) counts base
      (Nat.le_of_lt (Nat.mod_lt _ hg.1)) (by omega)
    simp only [Text.query,if_pos hg,Text.chargeEndpoints,queryCost,queryLimit]
    omega
  · simp only [Text.query,if_neg hg,queryCost,queryLimit]
    omega

end REWB.MaskedPeriodic.Batch
