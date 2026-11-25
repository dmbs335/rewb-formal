import REWB.MaskedAllStartFullCostInitialRuns
import REWB.ResidualCachedGrowth

/-! Empty and periodic initialization with the actual measured formula
compiler installed. The returned semantic state is identical to the
original initialization, including its existing counters. Additional work
is obtained from the executed replacement, never from a supplied bound. -/
namespace REWB.MaskedAllStart.FullCost.Initial
open REWB.PeriodicConstruction REWB.ResidualCached.Growth
variable {σ : Nat}

def start (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) (K : Nat) : Result MaskedTraversalInitial.Result :=
  let empty:=MaskedEmpty.solve B C E text.toList source target
  let ⟨cyclic,cyclicWork⟩:=periodic B C E text fallback source target
  let bits:=MaskedTraversalInitial.unionBits (text.size+1) empty.answers cyclic.output.hits
  let answers:=MaskedTraversalAnswers.fromBits bits
  let sources:=MaskedMutableProgression.Batch.run text fallback source K answers.history
  (⟨empty,cyclic,answers,sources,
    empty.work+MaskedTraversalInitial.periodicUnits cyclic+answers.work+12*(text.size+1)+sources.totalWork⟩,
    empty.work+cyclicWork+answers.work+12*(text.size+1)+sources.totalWork+text.size+15)

theorem start_value (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) (K : Nat) :
    (start B C E text fallback source target K).1=
      MaskedTraversalInitial.start B C E text fallback source target K := by
  simp only [start,periodic_value,MaskedTraversalInitial.start]

def initialBudget (B C E : DFA (Fin σ)) (n : Nat) : Nat :=
  (12*C.stateCount+6*E.stateCount+92)*(n+1)+periodicBudget B C E n+
    MaskedMutableProgression.Batch.totalBudget σ n (n+1)+n+15

theorem start_work (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) (K : Nat) (hK : 0<K) :
    (start B C E text fallback source target K).2≤initialBudget B C E text.size := by
  have hp:=periodic_work B C E text fallback source target
  have he:=MaskedEmpty.solve_work B C E text.toList source target
  simp only [Array.length_toList] at he
  have hs:=MaskedTraversalInitial.start_source_work B C E text fallback source target K hK
  have ha : (MaskedTraversalInitial.start B C E text fallback source target K).answers.work=
      16*(text.size+1) := by
    change 16*(MaskedTraversalInitial.unionBits _ _ _).size=_
    rw [MaskedTraversalInitial.union_size]
  unfold start
  simp only [periodic_value]
  change (MaskedEmpty.solve B C E text.toList source target).work+
    (periodic B C E text fallback source target).2+
    (MaskedTraversalInitial.start B C E text fallback source target K).answers.work+
    12*(text.size+1)+(MaskedTraversalInitial.start B C E text fallback source target K).sources.totalWork+
    text.size+15≤_
  rw [he,ha]
  unfold initialBudget
  simp only [Nat.add_mul]
  omega

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem initial_profile (B C E : DFA (Fin σ)) :
    ∃coefficient,∀n s,Bound n s (initialBudget B C E n) 1 0 0 2 coefficient := by
  refine ⟨?coefficient,?proof⟩
  case proof=>
    intro n s
    residual_growth

theorem start_work_closed (B C E : DFA (Fin σ)) :
    ∃coefficient,∀(text : Array (Fin σ)) (fallback : Fin σ) (source target : Array Bool)
      (K : Nat),0<K→
      (start B C E text fallback source target K).2≤
        coefficient*(text.size+2)*(height text.size)^2 := by
  obtain ⟨coefficient,hc⟩:=initial_profile B C E
  refine ⟨coefficient,?_⟩
  intro text fallback source target K hK
  have hh:=Nat.le_trans (start_work B C E text fallback source target K hK) (hc text.size 1)
  simpa only [Bound,scale,Nat.pow_one,Nat.pow_zero,Nat.mul_one,Nat.one_mul,Nat.mul_assoc] using hh

end REWB.MaskedAllStart.FullCost.Initial
