import REWB.Core

/-! Arithmetic of the proposed phase budgets. This does not construct the
    algorithms or establish that the algorithms incur these budgets. -/
namespace REWB.Cost

/-- Monotonicity in the exponent for an integer base at least one. -/
theorem pow_mono_exponent (x a b : Nat) (hx : 1 ≤ x) (hab : a ≤ b) :
    x ^ a ≤ x ^ b := by
  have hpos : ∀ d : Nat, 1 ≤ x ^ d := by
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
      rw [Nat.pow_succ]
      exact Nat.le_trans hx (by simpa using Nat.mul_le_mul_right x ih)
  have heq : b = a + (b - a) := by omega
  calc
    x ^ a = x ^ a * 1 := by simp
    _ ≤ x ^ a * x ^ (b - a) := Nat.mul_le_mul_left _ (hpos _)
    _ = x ^ b := by rw [← Nat.pow_add, ← heq]

inductive Phase where
  | index | short | disjoint | longGap | largePeriod | lowExponent | smallPeriod | linearQuery
  deriving Repr, DecidableEq

/-- Exponents after scaling n ~ t^30, s ~ t^3, Q ~ t^9, L=D₀ ~ t^10. -/
def p1Exponent : Phase → Nat
  | .index => 60 - 3
  | .short => 30 + 2 * 10
  | .disjoint => 60 + 2 * 3 - 10
  | .longGap => 60 + 2 * 3 - 10
  | .largePeriod => 60 + 2 * 3 - 9
  | .lowExponent => 30 + 10 + 2 * 3
  | .smallPeriod => 30 + 3 * 9
  | .linearQuery => 30 + 2 * 3

/-- Exponents after scaling n ~ t^39, s ~ t^3, Q ~ t^9, L=D₀ ~ t^13. -/
def p2Exponent : Phase → Nat
  | .index => 78 - 3
  | .short => 39 + 2 * 13
  | .disjoint => 78 + 2 * 3 - 13
  | .longGap => 78 + 2 * 3 - 13
  | .largePeriod => 78 + 2 * 3 - 9
  | .lowExponent => 39 + 13 + 2 * 3
  | .smallPeriod => 39 + 4 * 9
  | .linearQuery => 39 + 2 * 3

theorem p1Exponent_le (p : Phase) : p1Exponent p ≤ 57 := by
  cases p <;> decide

theorem p2Exponent_le (p : Phase) : p2Exponent p ≤ 75 := by
  cases p <;> decide

theorem p1Phase_le (p : Phase) (t : Nat) (ht : 1 ≤ t) :
    t ^ p1Exponent p ≤ t ^ 57 :=
  pow_mono_exponent t _ _ ht (p1Exponent_le p)

theorem p2Phase_le (p : Phase) (t : Nat) (ht : 1 ≤ t) :
    t ^ p2Exponent p ≤ t ^ 75 :=
  pow_mono_exponent t _ _ ht (p2Exponent_le p)

/-- 57/30 = 19/10; 75/39 = 25/13, and the latter dominates. -/
theorem ratios : 57 * 10 = 19 * 30 ∧ 75 * 13 = 25 * 39 ∧
    19 * 13 < 25 * 10 ∧ 25 < 2 * 13 := by decide

end REWB.Cost
