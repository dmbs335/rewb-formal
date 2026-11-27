import REWB.MaskedPeriodicModulus

/-! Pattern-only shape families for the three-branch compiler. Numeric
    run bounds occur only as literals. The covering families below are
    proof witnesses; phase queries do not enumerate them. Their common
    modulus is a fixed-pattern preprocessing constant shared by every
    tuple, rotation, branch and run with these three state counts.
-/
namespace REWB.MaskedPeriodic
open REWB.AffineProjection REWB.PhaseSolver REWB.UniformProjection

def branchFamily (b c e : Nat) (branch : Branch) : Family :=
  combine [LiteralShape.formula (boundsFormula branch 0)]
    (combine (descriptors b (LiteralShape.aff aExpr))
      (combine (descriptors c (LiteralShape.aff (gapExpr branch)))
        (descriptors e (LiteralShape.aff (tailExpr branch 0)))))

theorem boundsFormula_shape (branch : Branch) (N : Nat) :
    LiteralShape.formula (boundsFormula branch N)=
      LiteralShape.formula (boundsFormula branch 0) := by cases branch <;> rfl

theorem tailExpr_shape (branch : Branch) (N : Nat) :
    LiteralShape.aff (tailExpr branch N)=LiteralShape.aff (tailExpr branch 0) := by
  cases branch <;> rfl

theorem formula_branch_covered {b c e : Nat} (data : Data b c e) (branch : Branch) (N : Nat) :
    Covered (formula data branch N) (branchFamily b c e branch) := by
  unfold formula branchFamily
  apply covered_both
  · unfold Covered
    rw [boundsFormula_shape branch N]
    exact List.mem_cons_self
  · apply covered_both _ _ _ _ (data.capture.formula_covered _)
    apply covered_both _ _ _ _ (data.gap.formula_covered _)
    rw [←tailExpr_shape branch N]
    exact data.suffix.formula_covered _

def family (b c e : Nat) : Family :=
  branchFamily b c e .zero++(branchFamily b c e .interior++branchFamily b c e .ending)

theorem formula_covered {b c e : Nat} (data : Data b c e) (branch : Branch) (N : Nat) :
    Covered (formula data branch N) (family b c e) := by
  have hh := formula_branch_covered data branch N
  unfold Covered at *
  unfold family
  cases branch
  · exact List.mem_append.mpr (Or.inl hh)
  · exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl hh)))
  · exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr hh)))

def modulus (b c e : Nat) : Nat := Modulus.family 1 (family b c e)
def syntaxBudget (b c e : Nat) : Nat := budget 1 (family b c e)
def projectionBudget (b c e : Nat) : Nat := CountedProjection.stepsBudget 1 1 (family b c e)

/-- Compute once for a fixed pattern and pass K to the cached query
    entry points. The certificate is erased by executable code. -/
structure PreparedPattern (b c e : Nat) where
  K : Nat
  exact : K=modulus b c e

def preparePattern (b c e : Nat) : PreparedPattern b c e := ⟨modulus b c e,rfl⟩

theorem modulus_pos (b c e : Nat) : 0<modulus b c e := Modulus.family_pos _ _

theorem projection_compatible {b c e : Nat} (data : Data b c e) (branch : Branch) (N : Nat) :
    ExponentIntervals.Compatible (modulus b c e) (projection data branch N).1 := by
  rw [projection_value]
  exact Modulus.projection_compatible 1 _ _
    (formula_covered data branch N) (formula_good data branch N)

theorem projection_size {b c e : Nat} (data : Data b c e) (branch : Branch) (N : Nat) :
    measure (projection data branch N).1≤syntaxBudget b c e := by
  rw [projection_value]
  exact UniformProjection.projection_budget _ _ _ (formula_covered data branch N)

theorem projection_branches {b c e : Nat} (data : Data b c e) (branch : Branch) (N : Nat) :
    (projection data branch N).1.length≤syntaxBudget b c e :=
  Nat.le_trans (length_le_measure _) (projection_size data branch N)

/-- This is the counter returned by actual recursive elimination. The
    separate finite-orbit construction and interval compilation are not
    included in this projection-only counter. -/
theorem projection_steps {b c e : Nat} (data : Data b c e) (branch : Branch) (N : Nat) :
    (projection data branch N).2≤projectionBudget b c e := by
  have hh := CountedProjection.solve_uniform_steps 1 (formula data branch N)
    (family b c e) [0] (formula_covered data branch N)
  change (CountedProjection.project 1 (formula data branch N)).2≤_
  unfold CountedProjection.solve at hh
  change (CountedProjection.project 1 (formula data branch N)).2+
    (CountedProjection.decide [0] (CountedProjection.project 1 (formula data branch N)).1).2+1≤
      projectionBudget b c e at hh
  omega

def windows {b c e : Nat} (data : Data b c e) (branch : Branch) (N : Nat) :
    List (Nat×ExponentIntervals.Window) :=
  ExponentIntervals.allWindows (modulus b c e) N (projection data branch N).1

theorem windows_size {b c e : Nat} (data : Data b c e) (branch : Branch) (N : Nat) :
    (windows data branch N).length≤modulus b c e*syntaxBudget b c e := by
  rw [windows,ExponentIntervals.allWindows_length]
  exact Nat.mul_le_mul_left _ (projection_branches data branch N)

end REWB.MaskedPeriodic
