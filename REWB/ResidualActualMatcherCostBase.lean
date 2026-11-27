import REWB.ResidualActualMatcher
import REWB.ResidualActualIndependentCost

/-! Fixed-list cost composition and conversion of the concrete rounded
envelope to the 25/13 ledger target. The form premises below are erased
proof helpers; no runtime answer or cost provider is an executable input. -/
namespace REWB.ResidualActual.Matcher.Cost
open REWB.ResidualCached.Growth
variable {σ : Nat}

def scale (n : Nat) : Nat := (ThresholdBudget.base n)^75*(height n)^3

theorem scale_length (n : Nat) : n+2≤scale n := by
  exact Nat.le_trans (Independent.Cost.volume_length n) (Independent.Cost.volume_rounded n)

theorem scale_positive (n : Nat) : 1≤scale n := by
  have h:=scale_length n
  omega

theorem add_fixed {n x coefficient : Nat} (h : x≤coefficient*scale n) (fixed : Nat) :
    x+fixed≤(coefficient+fixed)*scale n := by
  have hf:=Nat.mul_le_mul_left fixed (scale_positive n)
  rw [Nat.add_mul]
  omega

theorem run_charged_of_forms (compiled : Compiled σ) (charge : Nat)
    (forms : ∀F,F∈compiled→∃coefficient,∀(text : Array (Fin σ)) (fallback : Fin σ),
      (form F text fallback).accountedWork+charge*(form F text fallback).fixedPatternBuilds≤coefficient*scale text.size) :
    ∃coefficient,∀(text : Array (Fin σ)) (fallback : Fin σ),
      (run compiled text fallback).accountedWork+charge*(run compiled text fallback).fixedPatternBuilds≤coefficient*scale text.size := by
  induction compiled with
  | nil =>
    refine ⟨1,?_⟩
    intro text fallback
    simpa only [run,Nat.mul_zero,Nat.add_zero,Nat.one_mul] using scale_positive text.size
  | cons F rest ih =>
    obtain ⟨one,hOne⟩:=forms F List.mem_cons_self
    obtain ⟨tail,hTail⟩:=ih (fun G hG=>forms G (List.mem_cons_of_mem F hG))
    refine ⟨one+tail+3,?_⟩
    intro text fallback
    have ho:=hOne text fallback
    have ht:=hTail text fallback
    have hf:=Nat.mul_le_mul_left 3 (scale_positive text.size)
    change (form F text fallback).accountedWork+(run rest text fallback).accountedWork+3+
      charge*((form F text fallback).fixedPatternBuilds+(run rest text fallback).fixedPatternBuilds)≤_
    simp only [Nat.mul_add,Nat.add_mul]
    omega

set_option exponentiation.threshold 1024 in
theorem target_of_bound (work : Nat→Nat) (coefficient : Nat)
    (h : ∀n,work n≤coefficient*scale n) : Spec.Target25Over13 work := by
  refine ⟨(coefficient+1)^13*(2^39)^25,39,
    Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos (Nat.pow_pos (by decide))),?_⟩
  intro n
  have larger:=Nat.le_trans (h n) (Nat.mul_le_mul_right (scale n) (Nat.le_succ coefficient))
  have hp:=Nat.pow_le_pow_left larger 13
  have he : ((ThresholdBudget.base n)^75)^13=((ThresholdBudget.base n)^39)^25 := by
    rw [←Nat.pow_mul,←Nat.pow_mul]
  simp only [scale,Nat.mul_pow] at hp
  rw [he,show ((height n)^3)^13=(height n)^39 by rw [←Nat.pow_mul]] at hp
  have ht:=Nat.pow_le_pow_left (ThresholdBudget.rounded_upper n) 25
  rw [Nat.mul_pow] at ht
  have hb:=Nat.mul_le_mul_right ((height n)^39) (Nat.mul_le_mul_left ((coefficient+1)^13) ht)
  exact Nat.le_trans hp (by simpa only [height,Nat.mul_assoc] using hb)

end REWB.ResidualActual.Matcher.Cost
