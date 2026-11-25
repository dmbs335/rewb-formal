import REWB.ResidualActualPeriodic
import REWB.ResidualActualCost
import REWB.ResidualActualMatcherCostBase

/-! The actual measured periodic branches are absorbed into the existing
rounded residual envelope.  This refinement charges their schedule,
formula/event and chronological construction; the row producer still has
the stated scope of ResidualActual.inputs.  The separate full-cost row
substitution can use the unchanged cached-layer input/value interface. -/
namespace REWB.ResidualActual.Periodic.Cost
open REWB.ResidualCached.Growth
variable {σ : Nat}

theorem periodic_rounded (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n : Nat) :
    PeriodicActual.roundedWork P f n≤
      PeriodicActual.roundedCoefficient P*(ThresholdBudget.base n)^75*(height n)^3 := by
  have h:=PeriodicActual.rounded_bound P f n
  change _≤PeriodicActual.roundedCoefficient P*(ThresholdBudget.base n)^75*height n at h
  have hp:=REWB.Cost.pow_mono_exponent (height n) 1 3 (by unfold height; omega) (by decide)
  simp only [Nat.pow_one] at hp
  exact Nat.le_trans h (Nat.mul_le_mul_left
    (PeriodicActual.roundedCoefficient P*(ThresholdBudget.base n)^75) hp)

theorem auto_charged_bound (P : SevenDFA (Fin σ)) (charge : Nat) :
    ∃coefficient,∀(text : Array (Fin σ)) (fallback : Fin σ),
      (P1.auto P text fallback).accountedWork+(P2.auto P text fallback).accountedWork+
        charge*((P1.auto P text fallback).fixedPatternBuilds+(P2.auto P text fallback).fixedPatternBuilds)≤
        coefficient*(ThresholdBudget.base text.size)^75*(height text.size)^3 := by
  obtain ⟨coefficient,hc⟩:=ResidualActual.Cost.auto_charged_bound P charge
  refine ⟨coefficient+PeriodicActual.roundedCoefficient P,?_⟩
  intro text fallback
  have hold:=hc text fallback
  have h₁:=P1.auto_work_le_old P text fallback
  have h₂:=P2.auto_work_le_old P text fallback
  have hp:=periodic_rounded P (ArrayText.read text fallback) text.size
  rw [P1.auto_builds,P2.auto_builds]
  unfold PeriodicActual.roundedWork at hp
  simp only [Nat.add_mul]
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

theorem auto_target (P : SevenDFA (Fin σ)) (charge : Nat)
    (texts : Nat → Array (Fin σ)) (fallback : Fin σ) (hsize : ∀n,(texts n).size=n) :
    Spec.Target25Over13 (fun n=>
      (P1.auto P (texts n) fallback).accountedWork+(P2.auto P (texts n) fallback).accountedWork+
        charge*((P1.auto P (texts n) fallback).fixedPatternBuilds+
          (P2.auto P (texts n) fallback).fixedPatternBuilds)) := by
  obtain ⟨coefficient,hc⟩:=auto_charged_bound P charge
  apply ResidualActual.Matcher.Cost.target_of_bound _ coefficient
  intro n
  simpa only [ResidualActual.Matcher.Cost.scale,Nat.mul_assoc,hsize n] using hc (texts n) fallback

theorem p1_target (P : SevenDFA (Fin σ)) (charge : Nat)
    (texts : Nat → Array (Fin σ)) (fallback : Fin σ) (hsize : ∀n,(texts n).size=n) :
    Spec.Target25Over13 (fun n=>(P1.auto P (texts n) fallback).accountedWork+
      charge*(P1.auto P (texts n) fallback).fixedPatternBuilds) := by
  obtain ⟨coefficient,hc⟩:=p1_charged_bound P charge
  apply ResidualActual.Matcher.Cost.target_of_bound _ coefficient
  intro n
  simpa only [ResidualActual.Matcher.Cost.scale,Nat.mul_assoc,hsize n] using hc (texts n) fallback

theorem p2_target (P : SevenDFA (Fin σ)) (charge : Nat)
    (texts : Nat → Array (Fin σ)) (fallback : Fin σ) (hsize : ∀n,(texts n).size=n) :
    Spec.Target25Over13 (fun n=>(P2.auto P (texts n) fallback).accountedWork+
      charge*(P2.auto P (texts n) fallback).fixedPatternBuilds) := by
  obtain ⟨coefficient,hc⟩:=p2_charged_bound P charge
  apply ResidualActual.Matcher.Cost.target_of_bound _ coefficient
  intro n
  simpa only [ResidualActual.Matcher.Cost.scale,Nat.mul_assoc,hsize n] using hc (texts n) fallback

end REWB.ResidualActual.Periodic.Cost
