import REWB.ResidualStripScheduleCost

/-! Kernel regressions for exact triple deduplication, the overlap-only
cut rule, edge-cut rejection and a stored grid cut in a gap shorter than
D. The last theorem uses the actual indexed generator and full schedule. -/
namespace REWB.ResidualStripSchedule.Regression
open REWB.IndexedGrid REWB.GlobalCoverage

theorem repeated_strip_once :
    (dedup 8 3 [⟨0,5,1⟩,⟨0,5,1⟩,⟨2,3,4⟩]).strips=[⟨0,5,1⟩] := by
  simp only [dedup,RunDedup.run]
  simp only [show (8+1).log2+1=4 by simp [Nat.log2]]
  decide

theorem separated_once :
    (one 1 2 ⟨1,4,10⟩).jobs=[direct ⟨1,4,10⟩] ∧ (one 1 2 ⟨1,4,10⟩).probes=0 := by
  decide

theorem overlap_exact_cuts :
    (one 3 2 ⟨0,8,2⟩).jobs=[atCut 3 ⟨0,8,2⟩ 1,atCut 3 ⟨0,8,2⟩ 2] ∧
    (one 3 2 ⟨0,8,2⟩).probes=4 := by decide

theorem empty_schedule : (collect 2 1 []).jobs=[] ∧ (collect 2 1 []).queries=0 := by decide

private def text : Nat→Fin 1 := fun _=>0
private def strip : Strip := ⟨0,6,2⟩

private theorem maximal : MaximalStrip text 8 strip.lo strip.hi strip.distance := by
  refine ⟨by decide,by decide,by decide,?_,Or.inl rfl,Or.inl rfl⟩
  intro i _ _
  rfl

theorem existing_short_gap_cut :
    ¬3+3≤3 ∧ ∃W,W∈(prepare text 8 1 2 3).batch.jobs ∧ W.left≤1 ∧ 3≤W.right ∧ W.distance=2 := by
  have hm:=generate_maximal text 8 1 2 strip (by decide) (by decide) maximal (by decide)
  have hr:=(generate_mem text 8 1 2 strip).mp hm |>.1
  exact ⟨by decide,prepare_existing_cut text 8 1 2 3 strip 1 3 1 hr
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)⟩

theorem actual_query_budget : (prepare text 8 1 2 3).batch.queries≤138 := by
  have hh:=prepare_queries text 8 1 2 3 (by decide) (by decide)
  exact Nat.le_trans hh (by decide)

end REWB.ResidualStripSchedule.Regression
