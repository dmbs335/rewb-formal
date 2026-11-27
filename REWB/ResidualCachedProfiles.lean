import REWB.ResidualCachedGrowth

/-! Closed fixed-pattern growth profiles of the actual finite cache
bank budgets. In particular, the grid factor occurs once in build cost;
it is never multiplied by the number of residual windows. -/
namespace REWB.ResidualCached.Growth
variable {σ : Nat}

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

theorem p1_build (P : SevenDFA (Fin σ)) :
    ∃C,∀n s,Bound n s (P1.buildBudget P n s) 1 0 1 2 C := by
  refine ⟨?C,?proof⟩
  case proof =>
    intro n s
    residual_growth

theorem p2_build (P : SevenDFA (Fin σ)) :
    ∃C,∀n s,Bound n s (P2.buildBudget P n s) 1 0 1 2 C := by
  refine ⟨?C,?proof⟩
  case proof =>
    intro n s
    residual_growth

theorem p1_query (P : SevenDFA (Fin σ)) :
    ∃C,∀n s,Bound n s (P1.queryBudget P n s+3) 0 2 0 2 C := by
  refine ⟨?C,?proof⟩
  case proof =>
    intro n s
    residual_growth

theorem p2_query (P : SevenDFA (Fin σ)) :
    ∃C,∀n s,Bound n s (P2.queryBudget P n s+3) 0 2 0 2 C := by
  refine ⟨?C,?proof⟩
  case proof =>
    intro n s
    residual_growth

theorem p1_short (P : SevenDFA (Fin σ)) :
    ∃C,∀n L,Bound n L (ShortOuter.P1.budget P n L) 1 2 0 2 C := by
  refine ⟨?C,?proof⟩
  case proof =>
    intro n L
    residual_growth

theorem p2_short (P : SevenDFA (Fin σ)) :
    ∃C,∀n L,Bound n L (ShortOuter.P2.budget P n L) 1 2 0 2 C := by
  refine ⟨?C,?proof⟩
  case proof =>
    intro n L
    residual_growth

theorem run_preparation (σ : Nat) :
    ∃C,∀n s,Bound n s (ResidualDispatch.runPreparationBudget σ n s) 1 0 1 2 C := by
  refine ⟨?C,?proof⟩
  case proof =>
    intro n s
    residual_growth

theorem strip_generation (σ : Nat) :
    ∃C,∀n s,Bound n s (ResidualStripSchedule.generationBudget σ n s) 1 0 1 2 C := by
  refine ⟨?C,?proof⟩
  case proof =>
    intro n s
    residual_growth

end REWB.ResidualCached.Growth
