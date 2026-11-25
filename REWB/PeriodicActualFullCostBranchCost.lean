import REWB.PeriodicActualFullCostBranch

/-! All measured outer-periodic primitives, event/formula preparation and
actual chronological joins meet the same rounded target. The constants
are proof-only fixed-pattern envelopes; runtime uses the counters returned
by the actual calls. Machine bits and memory-management costs are separate. -/
namespace REWB.PeriodicActual.FullCost
open REWB.PeriodicAccounting
variable {σ : Nat}

namespace Long

def branchCoefficient (P : SevenDFA (Fin σ)) : Nat :=
  PeriodicActual.Long.branchCoefficient P+coefficient P+6

theorem solve_expr (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (solve P f n Q).2≤branchCoefficient P*(longExpr P).eval n Q := by
  have hh:=solve_work_le_base P f n Q
  have ho:=PeriodicActual.Long.solve_expr P f n Q
  have hp:=prepare_expr P f n Q
  have hi:=PeriodicActual.long_expr_input P n Q
  unfold branchCoefficient
  simp only [Nat.add_mul]
  omega

theorem solve_rounded (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n : Nat) :
    (solve P f n (ThresholdBudget.period n)).2≤
      (branchCoefficient P*(longExpr P).coeff)*(ThresholdBudget.base n)^75 := by
  have hb:=Expr.bound75 (longExpr P) (by rw [long_degree]; decide) n
  exact Nat.le_trans (solve_expr P f n (ThresholdBudget.period n))
    (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (branchCoefficient P) hb)

end Long

namespace Short

def branchCoefficient (P : SevenDFA (Fin σ)) : Nat :=
  PeriodicActual.Short.branchCoefficient P+coefficient P+6

theorem solve_expr (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (solve P f n Q).2≤branchCoefficient P*(shortExpr P).eval n Q := by
  have hh:=solve_work_le_base P f n Q
  have ho:=PeriodicActual.Short.solve_expr P f n Q
  have hp:=prepare_expr P f n Q
  have hi:=PeriodicActual.short_expr_input P n Q
  unfold branchCoefficient
  simp only [Nat.add_mul]
  omega

theorem solve_rounded (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n : Nat) :
    (solve P f n (ThresholdBudget.period n)).2≤
      (branchCoefficient P*(shortExpr P).coeff)*(ThresholdBudget.base n)^75 := by
  have hb:=Expr.bound75 (shortExpr P) (by rw [short_degree]; decide) n
  exact Nat.le_trans (solve_expr P f n (ThresholdBudget.period n))
    (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (branchCoefficient P) hb)

end Short

namespace Cubic

abbrev expr (P : SevenDFA (Fin σ)) : PeriodicAccounting.Expr := PeriodicActual.Cubic.expr P

def coefficient (P : SevenDFA (Fin σ)) : Nat :=
  Long.branchCoefficient P+Short.branchCoefficient P+9

theorem solve_expr (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (solve P f n Q).2≤coefficient P*(expr P).eval n Q := by
  have hl:=Long.solve_expr P f n Q
  have hr:=Short.solve_expr P f n Q
  have hll:=Nat.mul_le_mul_left (Long.branchCoefficient P)
    (show (longExpr P).eval n Q≤(expr P).eval n Q by change _≤_+_; omega)
  have hrr:=Nat.mul_le_mul_left (Short.branchCoefficient P)
    (show (shortExpr P).eval n Q≤(expr P).eval n Q by change _≤_+_; omega)
  have hi:=PeriodicActual.Cubic.expr_input P n Q
  rw [solve_work]
  unfold coefficient
  simp only [Nat.add_mul]
  omega

theorem solve_rounded (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n : Nat) :
    (solve P f n (ThresholdBudget.period n)).2≤
      (coefficient P*(expr P).coeff)*(ThresholdBudget.base n)^75 := by
  have hb:=Expr.bound75 (expr P) (by rw [PeriodicActual.Cubic.expr_degree]; decide) n
  exact Nat.le_trans (solve_expr P f n (ThresholdBudget.period n))
    (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (coefficient P) hb)

end Cubic

/-- The returned unit-cost ledger of all three actual external periodic
branches at the common integer threshold. -/
def roundedWork (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n : Nat) : Nat :=
  (Cubic.solve P f n (ThresholdBudget.period n)).2+
  (P2.solve P f n (ThresholdBudget.period n)).2

def roundedCoefficient (P : SevenDFA (Fin σ)) : Nat :=
  Cubic.coefficient P*(Cubic.expr P).coeff+
  P2.coefficient P*(p2Expr P).coeff+1

theorem rounded_bound (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n : Nat) :
    roundedWork P f n≤
      roundedCoefficient P*(ThresholdBudget.base n)^75*logHeight n := by
  have hc := Cubic.solve_rounded P f n
  have hp := P2.solve_rounded P f n
  have hh : 1≤logHeight n := by unfold logHeight; omega
  have hc' := Nat.le_trans hc (by
    simpa only [Nat.mul_one] using
      (Nat.mul_le_mul_left ((Cubic.coefficient P*(Cubic.expr P).coeff)*(ThresholdBudget.base n)^75) hh))
  simp only [roundedWork,roundedCoefficient,Nat.add_mul,Nat.one_mul]
  omega

def targetConstant (P : SevenDFA (Fin σ)) : Nat := (roundedCoefficient P)^13*(2^39)^25

set_option exponentiation.threshold 1024 in
theorem rounded_power (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n : Nat) :
    (roundedWork P f n)^13≤targetConstant P*(n+2)^25*(logHeight n)^13 := by
  have h := Nat.pow_le_pow_left (rounded_bound P f n) 13
  have he : ((ThresholdBudget.base n)^75)^13=((ThresholdBudget.base n)^39)^25 := by
    rw [← Nat.pow_mul,← Nat.pow_mul]
  rw [Nat.mul_pow,Nat.mul_pow,he] at h
  have hu := Nat.pow_le_pow_left (ThresholdBudget.rounded_upper n) 25
  rw [Nat.mul_pow] at hu
  exact Nat.le_trans h (by
    simpa only [targetConstant,Nat.mul_assoc] using
      Nat.mul_le_mul_right ((logHeight n)^13)
        (Nat.mul_le_mul_left ((roundedCoefficient P)^13) hu))

theorem rounded_target (P : SevenDFA (Fin σ)) (texts : Nat → Nat → Fin σ) :
    Spec.Target25Over13 (fun n => roundedWork P (texts n) n) := by
  refine ⟨targetConstant P,13,?_,?_⟩
  · apply Nat.mul_pos
    · apply Nat.pow_pos
      unfold roundedCoefficient
      omega
    · exact Nat.pow_pos (Nat.pow_pos (by decide))
  · intro n
    exact rounded_power P (texts n) n

end REWB.PeriodicActual.FullCost
