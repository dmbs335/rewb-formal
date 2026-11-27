import REWB.MachineCostTransfer
import REWB.ResidualActualFullCostMatcherCost

/-! Conditional transfer from the actual matcher ledger to a separately
verified execution cost. The output-refinement and step-bound arguments
below must be proved for a concrete implementation. They are neither
executable oracles nor discharged obligations in this file.

In particular, these lemmas do not assert the existence of a complete
word-RAM implementation or a compiler-cost preservation theorem. -/
namespace REWB.MachineCostTransfer
open REWB.ResidualActual.FullCost
variable {σ : Nat}

/-- The added preparation cost is fixed before the input word is chosen. -/
theorem word_target_with_preprocessing (p : Expr (Fin σ)) (fallback : Fin σ)
    (charge preprocessing : Nat) (words : Nat→Word (Fin σ))
    (hsize : ∀n,(words n).length=n) :
    Spec.Target25Over13
      (fun n=>preprocessing+Matcher.Cost.wordWork p fallback charge (words n)) :=
  fixed_preprocessing (Matcher.Cost.word_target p charge words fallback hsize) preprocessing

/-- The coefficient is selected before the word: this statement retains
the uniformity of the original concrete-ledger bound. -/
theorem uniform_step_envelope (p : Expr (Fin σ)) (fallback : Fin σ) (charge : Nat)
    (steps : Word (Fin σ)→Nat) (preprocessing factor overhead : Nat)
    (step_bound : ∀w,steps w≤preprocessing+
      factor*(Matcher.Cost.wordWork p fallback charge w+w.length+1)*(height w.length)^overhead) :
    ∃coefficient,∀w,steps w≤coefficient*Matcher.Cost.scale w.length*(height w.length)^overhead := by
  obtain ⟨coefficient,hwork⟩ := Matcher.Cost.word_charged_bound p charge
  refine ⟨preprocessing+factor*(coefficient+1),?_⟩
  intro w
  have hw := hwork w fallback
  have hlength := Matcher.Cost.scale_length w.length
  have hscale := Matcher.Cost.scale_positive w.length
  have hlog : 1≤(height w.length)^overhead :=
    Nat.pow_pos (MachineWordBounds.height_positive w.length)
  have hvolume : 1≤Matcher.Cost.scale w.length*(height w.length)^overhead := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul hscale hlog
  have hlinear : Matcher.Cost.wordWork p fallback charge w+w.length+1≤
      (coefficient+1)*Matcher.Cost.scale w.length := by
    rw [Nat.add_mul,Nat.one_mul]
    omega
  have hfixed := Nat.mul_le_mul_left preprocessing hvolume
  have hbody := Nat.mul_le_mul_right ((height w.length)^overhead)
    (Nat.mul_le_mul_left factor hlinear)
  calc
    steps w≤preprocessing+factor*(Matcher.Cost.wordWork p fallback charge w+w.length+1)*
        (height w.length)^overhead := step_bound w
    _≤preprocessing*(Matcher.Cost.scale w.length*(height w.length)^overhead)+
        factor*((coefficient+1)*Matcher.Cost.scale w.length)*(height w.length)^overhead :=
      Nat.add_le_add (by simpa only [Nat.mul_one] using hfixed) hbody
    _=(preprocessing+factor*(coefficient+1))*Matcher.Cost.scale w.length*
        (height w.length)^overhead := by
      simp only [Nat.add_mul,Nat.mul_assoc]

/- A uniform explicit logarithmic exponent for the conditional transfer.
The constant is chosen before all input words, not separately for each
length-indexed test family. -/
set_option exponentiation.threshold 1024 in
theorem uniform_step_power_bound (p : Expr (Fin σ)) (fallback : Fin σ) (charge : Nat)
    (steps : Word (Fin σ)→Nat) (preprocessing factor overhead : Nat)
    (step_bound : ∀w,steps w≤preprocessing+
      factor*(Matcher.Cost.wordWork p fallback charge w+w.length+1)*(height w.length)^overhead) :
    ∃coefficient,0<coefficient ∧ ∀w,(steps w)^13≤
      coefficient*(w.length+2)^25*(height w.length)^(39+overhead*13) := by
  obtain ⟨coefficient,hsteps⟩ := uniform_step_envelope p fallback charge steps
    preprocessing factor overhead step_bound
  refine ⟨(coefficient+1)^13*(2^39)^25,
    Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos (Nat.pow_pos (by decide))),?_⟩
  intro w
  have hlarger := Nat.le_trans (hsteps w)
    (Nat.mul_le_mul_right ((height w.length)^overhead)
      (Nat.mul_le_mul_right (Matcher.Cost.scale w.length) (Nat.le_succ coefficient)))
  have hp := Nat.pow_le_pow_left hlarger 13
  have he : ((ThresholdBudget.base w.length)^75)^13=
      ((ThresholdBudget.base w.length)^39)^25 := by
    rw [←Nat.pow_mul,←Nat.pow_mul]
  simp only [Matcher.Cost.scale,Nat.mul_pow] at hp
  rw [he,
    show ((ResidualCached.Growth.height w.length)^3)^13=
      (ResidualCached.Growth.height w.length)^39 by rw [←Nat.pow_mul],
    show ((height w.length)^overhead)^13=(height w.length)^(overhead*13) by
      rw [←Nat.pow_mul]] at hp
  have hp' : (steps w)^13≤(coefficient+1)^13*((ThresholdBudget.base w.length)^39)^25*
      (height w.length)^(39+overhead*13) := by
    simpa only [height,MachineWordBounds.height,ResidualCached.Growth.height,
      Nat.pow_add,Nat.mul_assoc] using hp
  have ht := Nat.pow_le_pow_left (ThresholdBudget.rounded_upper w.length) 25
  rw [Nat.mul_pow] at ht
  have hb := Nat.mul_le_mul_right ((height w.length)^(39+overhead*13))
    (Nat.mul_le_mul_left ((coefficient+1)^13) ht)
  exact Nat.le_trans hp' (by simpa only [Nat.mul_assoc] using hb)

/-- The machine step count must independently satisfy `step_bound`. -/
theorem word_target_of_step_bound (p : Expr (Fin σ)) (fallback : Fin σ) (charge : Nat)
    (steps : Word (Fin σ)→Nat) (preprocessing factor overhead : Nat)
    (step_bound : ∀w,steps w≤preprocessing+
      factor*(Matcher.Cost.wordWork p fallback charge w+w.length+1)*(height w.length)^overhead)
    (words : Nat→Word (Fin σ)) (hsize : ∀n,(words n).length=n) :
    Spec.Target25Over13 (fun n=>steps (words n)) := by
  apply of_simulation_bound (Matcher.Cost.word_target p charge words fallback hsize)
    preprocessing factor overhead
  intro n
  simpa only [hsize n] using step_bound (words n)

/-- Both premises describe the proposed implementation. Neither follows
merely from the numerical target of its source-level matcher. -/
theorem correct_and_target_of_refinement (p : Expr (Fin σ)) (fallback : Fin σ) (charge : Nat)
    (run : Word (Fin σ)→Bool) (steps : Word (Fin σ)→Nat)
    (preprocessing factor overhead : Nat)
    (answers : ∀w,run w=Matcher.matchWord p fallback w)
    (step_bound : ∀w,steps w≤preprocessing+
      factor*(Matcher.Cost.wordWork p fallback charge w+w.length+1)*(height w.length)^overhead)
    (words : Nat→Word (Fin σ)) (hsize : ∀n,(words n).length=n) :
    Spec.CorrectMatcher p run ∧ Spec.Target25Over13 (fun n=>steps (words n)) := by
  constructor
  · intro w
    rw [answers w]
    exact Matcher.matchWord_correct p fallback w
  · exact word_target_of_step_bound p fallback charge steps preprocessing factor overhead
      step_bound words hsize

end REWB.MachineCostTransfer
