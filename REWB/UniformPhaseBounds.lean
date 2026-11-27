import REWB.UniformProjection

/-! Pattern-only bounds for the actual P2 compiler and the P1
    source/target formulas. The finite shape families do not depend on
    the input word, run period, endpoint phases, external contexts or
    numeric coordinate bounds. They also supply the positive common
    modulus required by ExponentIntervals and the offline batch join. -/
namespace REWB.UniformPhaseBounds
open REWB.AffineProjection REWB.PhaseSolver REWB.UniformProjection
variable {α : Type}

def p2Zero : P2Periodic.Layout Nat := ⟨0,0,0,0,0,0,0,0⟩

def p2Family (P : SevenDFA α) : Family :=
  systemFamily (P2Periodic.constraints P 1 0 [] [] (P2Periodic.endpoints p2Zero))

theorem p2_family_constant (P : SevenDFA α) (q n : Nat) (pre post : Word α)
    (ph : P2Periodic.Layout Nat) :
    systemFamily (P2Periodic.constraints P q n pre post (P2Periodic.endpoints ph))=
      p2Family P := rfl

theorem p2_covered [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (q n : Nat) (pre post : Word α) (ph : P2Periodic.Layout Nat) :
    Covered (compileSystem q n s (P2Periodic.constraints P q n pre post
      (P2Periodic.endpoints ph))) (p2Family P) := by
  rw [← p2_family_constant P q n pre post ph]
  exact covered_system q n s _

def p2Budget (P : SevenDFA α) : Nat := budget 8 (p2Family P)

def p2AllStagesBudget (P : SevenDFA α) : Nat := stageBudget 8 (p2Family P)

theorem p2_all_stages_bound [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (q n : Nat) (pre post : Word α) (ph : P2Periodic.Layout Nat)
    (k : Nat) (hk : k≤8) :
    measure (project k (compileSystem q n s (P2Periodic.constraints P q n pre post
      (P2Periodic.endpoints ph))))≤p2AllStagesBudget P :=
  projection_stage_budget k 8 _ _ (p2_covered P s q n pre post ph) hk

/-- Every complete fixed-phase P2 decision has uniformly bounded
    projected syntax. The only unbounded numeric data are literals. -/
theorem p2_projection_bound [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (q n : Nat) (pre post : Word α) (ph : P2Periodic.Layout Nat) :
    measure (project 8 (compileSystem q n s (P2Periodic.constraints P q n pre post
      (P2Periodic.endpoints ph))))≤p2Budget P :=
  projection_budget _ _ _ (p2_covered P s q n pre post ph)

theorem p2_projection_branches [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (q n : Nat) (pre post : Word α) (ph : P2Periodic.Layout Nat) :
    (project 8 (compileSystem q n s (P2Periodic.constraints P q n pre post
      (P2Periodic.endpoints ph)))).length≤p2Budget P :=
  projection_branches _ _ _ (p2_covered P s q n pre post ph)

def p1Zero : P1Target.Layout Nat := ⟨0,0,0,0,0⟩

def p1TargetSystem (P : SevenDFA α) : Family :=
  systemFamily (P1Target.constraints P 1 0 0 [] (P1Target.endpoints p1Zero))

def p1TargetFamily (P : SevenDFA α) : Family :=
  [] :: combine (p1TargetSystem P)
    [eq (countShape (.var 0) (.var 1)) (.var 5)]

theorem p1_target_system_constant (P : SevenDFA α) (q n p : Nat)
    (post : Word α) (ph : P1Target.Layout Nat) :
    systemFamily (P1Target.constraints P q n p post (P1Target.endpoints ph))=
      p1TargetSystem P := rfl

theorem p1_target_covered [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (n q p rho : Nat) (post : Word α) (ph : P1Target.Layout Nat) :
    Covered (P1Target.formula P s n q p rho post ph) (p1TargetFamily P) := by
  unfold P1Target.formula
  dsimp only
  split
  · apply List.mem_cons.mpr
    right
    apply covered_both
    · rw [← p1_target_system_constant P q n p post ph]
      exact covered_system q n s _
    · unfold Covered
      rw [erase_eq,erase_count]
      exact List.mem_cons_self
  · exact List.mem_cons_self

def p1SourceStart : Aff := ((Aff.lit 0).sub (.lit 0)).sub (.var 0)

def p1SourceFamily (P : SevenDFA α) : Family :=
  [] :: combine (regulars P.A.stateCount (.lit 0) p1SourceStart)
    (orders p1SourceStart (.lit 0))

theorem p1_source_covered (P : SevenDFA α) (s : Nat→α)
    (n q a phase rho : Nat) (pre gap : Word α) :
    Covered (P1Source.formula P s n q a phase rho pre gap) (p1SourceFamily P) := by
  unfold P1Source.formula
  dsimp only
  split
  · apply List.mem_cons.mpr
    right
    exact covered_both _ _ _ _ (covered_regular q n s (Periodic.contextual P.A pre [])
      P2Periodic.zeroEndpoint (P1Source.start q a phase))
      (covered_order q n (P1Source.start q a phase) (P2Periodic.endEndpoint q a))
  · exact List.mem_cons_self

def p1SourceBudget (P : SevenDFA α) : Nat := budget 0 (p1SourceFamily P)
def p1TargetBudget (P : SevenDFA α) : Nat := budget 5 (p1TargetFamily P)

theorem p1_source_bound (P : SevenDFA α) (s : Nat→α)
    (n q a phase rho : Nat) (pre gap : Word α) :
    measure (P1Source.formula P s n q a phase rho pre gap)≤p1SourceBudget P :=
  projection_budget 0 _ _ (p1_source_covered P s n q a phase rho pre gap)

theorem p1_target_bound [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (n q p rho : Nat) (post : Word α) (ph : P1Target.Layout Nat) :
    measure (P1Target.projection P s n q p rho post ph)≤p1TargetBudget P :=
  projection_budget 5 _ _ (p1_target_covered P s n q p rho post ph)

theorem p1_source_branches (P : SevenDFA α) (s : Nat→α)
    (n q a phase rho : Nat) (pre gap : Word α) :
    (P1Source.formula P s n q a phase rho pre gap).length≤p1SourceBudget P :=
  Nat.le_trans (length_le_measure _) (p1_source_bound P s n q a phase rho pre gap)

theorem p1_target_branches [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (n q p rho : Nat) (post : Word α) (ph : P1Target.Layout Nat) :
    (P1Target.projection P s n q p rho post ph).length≤p1TargetBudget P :=
  Nat.le_trans (length_le_measure _) (p1_target_bound P s n q p rho post ph)

/-- One positive modulus works simultaneously for every source and
    target event generated for the same fixed P1 pattern. -/
def p1Modulus (P : SevenDFA α) : Nat :=
  commonModulus 0 (p1SourceFamily P)*commonModulus 5 (p1TargetFamily P)

theorem p1Modulus_pos (P : SevenDFA α) : 0<p1Modulus P :=
  Nat.mul_pos (commonModulus_pos _ _) (commonModulus_pos _ _)

theorem compatible_multiple (F : Formula) (K L : Nat)
    (h : ExponentIntervals.Compatible K F) (hd : K∣L) :
    ExponentIntervals.Compatible L F := by
  intro C hC a ha
  have hh := h C hC a ha
  cases a with
  | le t => trivial
  | dvd m t => exact Nat.dvd_trans hh hd

theorem p1_source_compatible (P : SevenDFA α) (s : Nat→α)
    (n q a phase rho : Nat) (pre gap : Word α) (h : Periodic.Period s n q) :
    ExponentIntervals.Compatible (p1Modulus P)
      (P1Source.formula P s n q a phase rho pre gap) :=
  compatible_multiple _ _ _
    (projection_compatible 0 _ _ (p1_source_covered P s n q a phase rho pre gap)
      (P1Source.formula_good P s n q a phase rho pre gap h))
    (Nat.dvd_mul_right _ _)

theorem p1_target_compatible [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (n q p rho : Nat) (post : Word α) (ph : P1Target.Layout Nat)
    (h : Periodic.LeastPeriod s n q) :
    ExponentIntervals.Compatible (p1Modulus P)
      (P1Target.projection P s n q p rho post ph) :=
  compatible_multiple _ _ _
    (projection_compatible 5 _ _ (p1_target_covered P s n q p rho post ph)
      (P1Target.formula_good P s n q p rho h post ph))
    (Nat.dvd_mul_left _ _)

theorem p1_source_windows (P : SevenDFA α) (s : Nat→α)
    (n q a phase rho N : Nat) (pre gap : Word α) :
    (ExponentIntervals.allWindows (p1Modulus P) N
      (P1Source.formula P s n q a phase rho pre gap)).length≤
        p1Modulus P*p1SourceBudget P := by
  rw [ExponentIntervals.allWindows_length]
  exact Nat.mul_le_mul_left _ (p1_source_branches P s n q a phase rho pre gap)

theorem p1_target_windows [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (n q p rho N : Nat) (post : Word α) (ph : P1Target.Layout Nat) :
    (ExponentIntervals.allWindows (p1Modulus P) N
      (P1Target.projection P s n q p rho post ph)).length≤
        p1Modulus P*p1TargetBudget P := by
  rw [ExponentIntervals.allWindows_length]
  exact Nat.mul_le_mul_left _ (p1_target_branches P s n q p rho post ph)

def p1TargetAllStagesBudget (P : SevenDFA α) : Nat := stageBudget 5 (p1TargetFamily P)

theorem p1_target_all_stages [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (n q p rho : Nat) (post : Word α) (ph : P1Target.Layout Nat)
    (k : Nat) (hk : k≤5) :
    measure (project k (P1Target.formula P s n q p rho post ph))≤
      p1TargetAllStagesBudget P :=
  projection_stage_budget k 5 _ _ (p1_target_covered P s n q p rho post ph) hk

end REWB.UniformPhaseBounds
