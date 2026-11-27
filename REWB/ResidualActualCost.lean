import REWB.ResidualActualCostRows

/-! Rounded bounds for the actual P1/P2 executions. Actual all-start row
production, cached dispatch and every counted fixed-pattern action build
are included. This is a bound on those concrete ledgers; the separate
periodic construction refinement supplies additional operation costs. -/
namespace REWB.ResidualActual.Cost
open REWB.ResidualCached.Growth
variable {σ : Nat}

theorem rowVolume_rounded (n : Nat) :
    rowVolume n (ThresholdBudget.block n)≤
      3*(ThresholdBudget.base n)^75*(height n)^3 := by
  have h:=Nat.mul_le_mul_right ((height n)^3)
    (ResidualCached.Rounded.grid n (ThresholdBudget.base n)
      (ThresholdBudget.base_pos n) (ThresholdBudget.rounded_lower n))
  simpa only [rowVolume,MaskedAllStart.Rows.Cost.volume,ThresholdBudget.block,
    Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using h

theorem p1_inputs_rounded (P : SevenDFA (Fin σ)) (text : Array (Fin σ))
    (fallback : Fin σ) (charge : Nat) :
    (P1.inputs P text.toList fallback (ThresholdBudget.block text.size)).work+
      charge*(P1.inputs P text.toList fallback (ThresholdBudget.block text.size)).fixedPatternBuilds≤
      (3*p1Coefficient P charge)*(ThresholdBudget.base text.size)^75*(height text.size)^3 := by
  have h:=p1_inputs_work P text.toList fallback (ThresholdBudget.block text.size) charge
  conv at h => rhs; rw [Array.length_toList]
  have hr:=Nat.mul_le_mul_left (p1Coefficient P charge) (rowVolume_rounded text.size)
  exact Nat.le_trans h (by simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hr)

theorem p2_inputs_rounded (P : SevenDFA (Fin σ)) (text : Array (Fin σ))
    (fallback : Fin σ) (charge : Nat) :
    (P2.inputs P text.toList fallback (ThresholdBudget.block text.size)).work+
      charge*(P2.inputs P text.toList fallback (ThresholdBudget.block text.size)).fixedPatternBuilds≤
      (3*p2Coefficient P charge)*(ThresholdBudget.base text.size)^75*(height text.size)^3 := by
  have h:=p2_inputs_work P text.toList fallback (ThresholdBudget.block text.size) charge
  conv at h => rhs; rw [Array.length_toList]
  have hr:=Nat.mul_le_mul_left (p2Coefficient P charge) (rowVolume_rounded text.size)
  exact Nat.le_trans h (by simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hr)

theorem auto_charged_bound (P : SevenDFA (Fin σ)) (charge : Nat) :
    ∃coefficient,∀(text : Array (Fin σ)) (fallback : Fin σ),
      (P1.auto P text fallback).accountedWork+(P2.auto P text fallback).accountedWork+
        charge*((P1.auto P text fallback).fixedPatternBuilds+(P2.auto P text fallback).fixedPatternBuilds)≤
        coefficient*(ThresholdBudget.base text.size)^75*(height text.size)^3 := by
  obtain ⟨cached,_hpos,hcached⟩:=ResidualCached.Cost.budget_bound P
  refine ⟨3*p1Coefficient P charge+3*p2Coefficient P charge+cached+24,?_⟩
  intro text fallback
  have h₁:=p1_inputs_rounded P text fallback charge
  have h₂:=p2_inputs_rounded P text fallback charge
  have hc:=hcached text.size
  have he:=ResidualActual.auto_accountedWork P text fallback
  have ho:=Nat.mul_le_mul_left 2 (ResidualCached.Cost.overhead text.size
    (ThresholdBudget.base text.size) (ThresholdBudget.base_pos text.size)
    (ThresholdBudget.rounded_lower text.size))
  change (P1.auto P text fallback).accountedWork+(P2.auto P text fallback).accountedWork+
    charge*((P1.inputs P text.toList fallback (ThresholdBudget.block text.size)).fixedPatternBuilds+
      (P2.inputs P text.toList fallback (ThresholdBudget.block text.size)).fixedPatternBuilds)≤_
  simp only [Nat.mul_add,Nat.add_mul,Nat.mul_assoc] at h₁ h₂ hc ho ⊢
  omega

theorem auto_bound (P : SevenDFA (Fin σ)) :
    ∃coefficient,∀(text : Array (Fin σ)) (fallback : Fin σ),
      (P1.auto P text fallback).accountedWork+(P2.auto P text fallback).accountedWork≤
        coefficient*(ThresholdBudget.base text.size)^75*(height text.size)^3 := by
  simpa only [Nat.zero_mul,Nat.add_zero] using auto_charged_bound P 0

end REWB.ResidualActual.Cost
