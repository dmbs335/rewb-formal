import REWB.ResidualActualFullCostMatcher
import REWB.ResidualActualMatcherCostBase

/-! Finite-list composition for the actual construction-counted matcher.
The rounded envelope is reused as a proof lemma; no coefficient or
uniform syntactic family is evaluated by the runtime matcher. -/
namespace REWB.ResidualActual.FullCost.Matcher.Cost
open REWB.ResidualCached.Growth
export REWB.ResidualActual.Matcher.Cost
  (scale scale_length scale_positive add_fixed target_of_bound)
variable {σ : Nat}

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

end REWB.ResidualActual.FullCost.Matcher.Cost
