import REWB.BoundaryRangeNearIndexBorderAll

/-! Kernel regressions for positive and empty copies in one block,
right-end clipping, the common C/K split, and the all-four union. -/
namespace REWB.BoundaryRange.NearIndex.Border.Regression
open REWB.Spec (slice)

abbrev allWords : DFA (Fin 2) := ⟨1,0,fun _ _=>0,fun _=>true⟩
abbrev epsilon : DFA (Fin 2) := ⟨2,0,fun _ _=>1,fun q=>decide (q=0)⟩
abbrev nonempty : DFA (Fin 2) := ⟨2,0,fun _ _=>1,fun q=>decide (q=1)⟩
def word : Word (Fin 2) := [0,1,0]

private theorem repeated_zero : Copy epsilon nonempty epsilon word 1 2 3 := by
  refine ⟨1,by decide,by decide,?_,?_,?_,?_⟩
  all_goals first | decide | (unfold DFA.accepts; decide)

theorem positive_in_same_block :
    (query (build epsilon nonempty epsilon allWords nonempty epsilon word 0) 1 3 0 3).1=true := by
  apply (query_correct epsilon nonempty epsilon allWords nonempty epsilon word 0 1 3 0 3
    (by decide) (by decide)).mpr
  refine ⟨1,1,2,⟨by decide,by decide,by decide,?_,?_,?_,repeated_zero⟩,by decide,by decide,by decide⟩
  all_goals unfold DFA.accepts; decide

theorem empty_in_same_block :
    (query (build allWords epsilon epsilon epsilon epsilon allWords word 0) 1 1 0 2).1=true := by
  apply (query_correct allWords epsilon epsilon epsilon epsilon allWords word 0 1 1 0 2
    (by decide) (by decide)).mpr
  refine ⟨1,1,1,⟨by decide,by decide,by decide,?_,?_,?_,?_⟩,by decide,by decide,by decide⟩
  · unfold DFA.accepts; decide
  · unfold DFA.accepts; decide
  · unfold DFA.accepts; decide
  · refine ⟨0,by decide,by decide,?_,?_,?_,?_⟩
    all_goals first | decide | (unfold DFA.accepts; decide)

theorem clipped_at_target_start :
    (copy (build epsilon nonempty epsilon allWords nonempty epsilon word 0)
      1 ⟨2,by decide⟩ 2).1=false := by
  cases hv : (copy (build epsilon nonempty epsilon allWords nonempty epsilon word 0)
    1 ⟨2,by decide⟩ 2).1 with
  | false => rfl
  | true =>
    obtain ⟨L,_,hr,_,_,hB,_⟩:=(copy_correct epsilon nonempty epsilon allWords nonempty epsilon word 0
      1 ⟨2,by decide⟩ 2 (by decide) (by decide) (by decide)).mp hv
    have hL : L=0 := by change 2+L≤2 at hr; omega
    subst L
    have hn : ¬nonempty.accepts (slice word 1 1) := by unfold DFA.accepts; decide
    exact False.elim (hn hB)

theorem common_split_required :
    (gap (build allWords allWords epsilon nonempty allWords allWords word 0) 0 0 1).1=false := by
  cases hv : (gap (build allWords allWords epsilon nonempty allWords allWords word 0) 0 0 1).1 with
  | false => rfl
  | true =>
    obtain ⟨p,_,_,hp,hC,hK,_⟩:=(gap_iff_split allWords allWords epsilon nonempty allWords allWords
      word 0 0 0 1 (by decide) (by decide) (by decide)).mp hv
    have h : p=0 ∨ p=1 := by omega
    rcases h with h|h
    · subst p
      have hn : ¬nonempty.accepts (slice word 0 0) := by unfold DFA.accepts; decide
      exact False.elim (hn hK)
    · subst p
      have hn : ¬epsilon.accepts (slice word 0 1) := by unfold DFA.accepts; decide
      exact False.elim (hn hC)

theorem all_four_positive :
    (Full.query (Full.build epsilon nonempty epsilon allWords nonempty epsilon word 0 0 3
      (by decide) (by decide)) 1 3).1=true := by
  apply (Full.query_iff epsilon nonempty epsilon allWords nonempty epsilon word 0 0 3
    (by decide) (by decide) 1 3 (by decide) (by decide) (by decide)).mpr
  refine ⟨1,1,2,⟨by decide,by decide,by decide,?_,?_,?_,repeated_zero⟩,by decide⟩
  all_goals unfold DFA.accepts; decide

theorem all_four_zero_width :
    Full.query (Full.build allWords allWords allWords allWords allWords allWords [] 0 0 0
      (Nat.le_refl 0) (Nat.le_refl 0)) 0 0=(false,7) := rfl

end REWB.BoundaryRange.NearIndex.Border.Regression
