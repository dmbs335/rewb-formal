import REWB.MaskedAllStartCost
import REWB.ResidualCachedGrowth

/-! Fixed-pattern polynomial envelopes for actual all-start preparation.
The geometric tree capacity is bounded before polynomial certification;
the inferred coefficient cannot depend on the text length or grid width.
The scope is exactly that of preparationWork, including its explicit
finite-compiler exclusions. -/
namespace REWB.MaskedAllStart
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedTraversalAggregate
open REWB.ResidualCached.Growth
variable {σ : Nat}

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

theorem capacity_bound (n : Nat) : 2^(MaskedSuffixClass.height n)≤2*(n+1) := by
  have hh:=Nat.mul_le_mul_right 2 (Nat.log2_self_le (by omega : n+1≠0))
  simpa only [MaskedSuffixClass.height,Nat.pow_succ,Nat.mul_comm] using hh

def preparationEnvelope (B C E : DFA (Fin σ)) (n : Nat) : Nat :=
  let h:=MaskedSuffixClass.height n
  MaskedTraversalInitial.initialBudget B C E n+
    (32*(σ+2)+830)*(n+1)*((n+1).log2+1)^2+401*(n+1)*((n+1).log2+1)^2+
    (2*(n+1)*(Tree.joinBudget (2*ReplayMaps.count C.stateCount E.stateCount)
      (2*(MaskedClusterStage.dfa C E).stateCount)+Tree.leafBudget (2*ReplayMaps.count C.stateCount E.stateCount)
      (2*(MaskedClusterStage.dfa C E).stateCount))+h+1)+geometryBudget h n+
    C.stateCount*((n.log2+1)*n)+n*C.stateCount+
    E.stateCount*((n.log2+1)*n)+n*E.stateCount+(n.log2+1)*n+20*(n+1)+h+20

theorem preparation_envelope (B C E : DFA (Fin σ)) (n : Nat) :
    preparationBudget B C E n≤preparationEnvelope B C E n := by
  have hh:=Nat.mul_le_mul_right
    (Tree.joinBudget (2*ReplayMaps.count C.stateCount E.stateCount)
      (2*(MaskedClusterStage.dfa C E).stateCount)+Tree.leafBudget (2*ReplayMaps.count C.stateCount E.stateCount)
      (2*(MaskedClusterStage.dfa C E).stateCount)) (capacity_bound n)
  dsimp only [preparationBudget,preparationEnvelope,templateBudget]
  omega

theorem preparation_profile (B C E : DFA (Fin σ)) :
    ∃coefficient,∀n s,Bound n s (preparationBudget B C E n) 1 0 0 2 coefficient := by
  have envelope : ∃coefficient,∀n s,Bound n s (preparationEnvelope B C E n) 1 0 0 2 coefficient := by
    refine ⟨?C,?proof⟩
    case proof =>
      intro n s
      residual_growth
  obtain ⟨coefficient,hc⟩:=envelope
  exact ⟨coefficient,fun n s=>Nat.le_trans (preparation_envelope B C E n) (hc n s)⟩

theorem prepare_work_closed (B C E : DFA (Fin σ)) :
    ∃coefficient,∀(text : Array (Fin σ)) (fallback : Fin σ) (source target : Array Bool),
      (prepare B C E text fallback source target).preparationWork≤
        coefficient*(text.size+2)*((text.size+2).log2+1)^2 := by
  obtain ⟨coefficient,hc⟩:=preparation_profile B C E
  refine ⟨coefficient,?_⟩
  intro text fallback source target
  have hp:=Nat.le_trans (prepare_work B C E text fallback source target) (hc text.size 1)
  simpa only [Bound,scale,Nat.pow_one,Nat.pow_zero,Nat.mul_one,height,Nat.mul_assoc] using hp

end REWB.MaskedAllStart
