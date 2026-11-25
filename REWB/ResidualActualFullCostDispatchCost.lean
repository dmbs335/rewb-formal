import REWB.ResidualActualFullCostDispatch
import REWB.ResidualActualFullCostInputsCost
import REWB.ResidualActualPeriodicCost

/-! The actual finite-row construction and actual periodic construction
fit the same rounded target envelope. These are bounds on the concrete
mixed unit-operation ledger documented by the implementation, and do not
claim refcount, allocator, garbage-collector or machine-bit cost. -/
namespace REWB.ResidualActual.FullCost.Cost
open REWB.ResidualCached.Growth
variable {σ : Nat}

theorem p1_inputs_rounded (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) :
    (P1.inputs P text.toList fallback (ThresholdBudget.block text.size)).2≤
      (3*p1Coefficient P 0)*(ThresholdBudget.base text.size)^75*(height text.size)^3 := by
  have h:=p1_inputs_work P text.toList fallback (ThresholdBudget.block text.size) 0
  simp only [Nat.zero_mul,Nat.add_zero,Array.length_toList] at h
  have hr:=Nat.mul_le_mul_left (p1Coefficient P 0) (ResidualActual.Cost.rowVolume_rounded text.size)
  exact Nat.le_trans h (by
    simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hr)

theorem p2_inputs_rounded (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) :
    (P2.inputs P text.toList fallback (ThresholdBudget.block text.size)).2≤
      (3*p2Coefficient P 0)*(ThresholdBudget.base text.size)^75*(height text.size)^3 := by
  have h:=p2_inputs_work P text.toList fallback (ThresholdBudget.block text.size) 0
  simp only [Nat.zero_mul,Nat.add_zero,Array.length_toList] at h
  have hr:=Nat.mul_le_mul_left (p2Coefficient P 0) (ResidualActual.Cost.rowVolume_rounded text.size)
  exact Nat.le_trans h (by
    simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hr)

theorem auto_charged_bound (P : SevenDFA (Fin σ)) (charge : Nat) :
    ∃coefficient,∀(text : Array (Fin σ)) (fallback : Fin σ),
      (P1.auto P text fallback).accountedWork+(P2.auto P text fallback).accountedWork+
        charge*((P1.auto P text fallback).fixedPatternBuilds+(P2.auto P text fallback).fixedPatternBuilds)≤
        coefficient*(ThresholdBudget.base text.size)^75*(height text.size)^3 := by
  obtain ⟨coefficient,hc⟩:=Periodic.Cost.auto_charged_bound P charge
  refine ⟨coefficient+3*p1Coefficient P 0+3*p2Coefficient P 0,?_⟩
  intro text fallback
  have hold:=hc text fallback
  have h₁:=P1.auto_work_le_base P text fallback
  have h₂:=P2.auto_work_le_base P text fallback
  have hr₁:=p1_inputs_rounded P text fallback
  have hr₂:=p2_inputs_rounded P text fallback
  rw [P1.auto_builds,P2.auto_builds]
  simp only [Nat.add_mul,Nat.mul_assoc] at hold hr₁ hr₂ ⊢
  omega

theorem auto_bound (P : SevenDFA (Fin σ)) :
    ∃coefficient,∀(text : Array (Fin σ)) (fallback : Fin σ),
      (P1.auto P text fallback).accountedWork+(P2.auto P text fallback).accountedWork≤
        coefficient*(ThresholdBudget.base text.size)^75*(height text.size)^3 := by
  simpa only [Nat.zero_mul,Nat.add_zero] using auto_charged_bound P 0

theorem p1_charged_bound (P : SevenDFA (Fin σ)) (charge : Nat) :
    ∃coefficient,∀(text : Array (Fin σ)) (fallback : Fin σ),
      (P1.auto P text fallback).accountedWork+charge*(P1.auto P text fallback).fixedPatternBuilds≤
        coefficient*(ThresholdBudget.base text.size)^75*(height text.size)^3 := by
  obtain ⟨coefficient,hc⟩:=auto_charged_bound P charge
  refine ⟨coefficient,?_⟩
  intro text fallback
  have h:=hc text fallback
  simp only [Nat.mul_add] at h
  omega

theorem p1_target (P : SevenDFA (Fin σ)) (charge : Nat)
    (texts : Nat → Array (Fin σ)) (fallback : Fin σ) (hsize : ∀n,(texts n).size=n) :
    Spec.Target25Over13 (fun n=>(P1.auto P (texts n) fallback).accountedWork+
      charge*(P1.auto P (texts n) fallback).fixedPatternBuilds) := by
  obtain ⟨coefficient,hc⟩:=p1_charged_bound P charge
  apply ResidualActual.Matcher.Cost.target_of_bound _ coefficient
  intro n
  simpa only [ResidualActual.Matcher.Cost.scale,Nat.mul_assoc,hsize n] using hc (texts n) fallback

theorem p2_charged_bound (P : SevenDFA (Fin σ)) (charge : Nat) :
    ∃coefficient,∀(text : Array (Fin σ)) (fallback : Fin σ),
      (P2.auto P text fallback).accountedWork+charge*(P2.auto P text fallback).fixedPatternBuilds≤
        coefficient*(ThresholdBudget.base text.size)^75*(height text.size)^3 := by
  obtain ⟨coefficient,hc⟩:=auto_charged_bound P charge
  refine ⟨coefficient,?_⟩
  intro text fallback
  have h:=hc text fallback
  simp only [Nat.mul_add] at h
  omega

theorem p2_target (P : SevenDFA (Fin σ)) (charge : Nat)
    (texts : Nat → Array (Fin σ)) (fallback : Fin σ) (hsize : ∀n,(texts n).size=n) :
    Spec.Target25Over13 (fun n=>(P2.auto P (texts n) fallback).accountedWork+
      charge*(P2.auto P (texts n) fallback).fixedPatternBuilds) := by
  obtain ⟨coefficient,hc⟩:=p2_charged_bound P charge
  apply ResidualActual.Matcher.Cost.target_of_bound _ coefficient
  intro n
  simpa only [ResidualActual.Matcher.Cost.scale,Nat.mul_assoc,hsize n] using hc (texts n) fallback

end REWB.ResidualActual.FullCost.Cost
