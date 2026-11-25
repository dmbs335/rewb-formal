import REWB.PeriodicActualFullCostP2

/-! The executed run/cache/context refinement changes only a fixed-pattern
coefficient. The complete run-enumerator construction is absorbed by the
same existing comparison envelope, including n=0 and Q=0. -/
namespace REWB.PeriodicActual.FullCost
open REWB.PeriodicAccounting
variable {α : Type} {σ : Nat}

def enumerationEnvelope (n Q : Nat) : Nat :=
  Q*(n+(n+1)*(2*Q*(Q+1)+1))

theorem period_le_enumeration (n Q : Nat) : Q≤enumerationEnvelope n Q := by
  have hm:=Nat.mul_le_mul_left (n+1) (by omega : 1≤2*Q*(Q+1)+1)
  simp only [Nat.mul_one] at hm
  have hp : 1≤n+(n+1)*(2*Q*(Q+1)+1) := by omega
  simpa only [enumerationEnvelope,Nat.mul_one] using Nat.mul_le_mul_left Q hp

theorem enumeration_work [DecidableEq α] (f : Nat→α) (n Q B : Nat)
    (he : enumerationEnvelope n Q≤B) (hn : n+1≤B) :
    (PeriodicConstruction.Runs.enumerate f n Q).2≤480*B := by
  have hq:=period_le_enumeration n Q
  have hm : enumerationEnvelope n Q+n+Q+1≤3*B := by omega
  have hh:=PeriodicConstruction.Runs.enumerate_work_closed f n Q
  change (PeriodicConstruction.Runs.enumerate f n Q).2≤
    160*(enumerationEnvelope n Q+n+Q+1) at hh
  have ht:=Nat.mul_le_mul_left 160 hm
  omega

namespace P2

theorem expr_enumeration (P : SevenDFA (Fin σ)) (n Q : Nat) :
    enumerationEnvelope n Q≤(p2Expr P).eval n Q := by
  change Q*(n+(n+1)*(2*Q*(Q+1)+1))≤
    Q*(n+(n+1)*(2*Q*(Q+1)+1))+(n+1)*(1+P.H.stateCount)+
    (FullyCachedP2.stateSum P*Q+Q^2)*(2*n)+
    (7+CountedProjection.p2Steps P)*(Q^4*(2*n))
  omega

theorem enumerate_expr (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (PeriodicConstruction.Runs.enumerate f n Q).2≤
      480*((p2Expr P).eval n Q*logHeight n) := by
  have hh:=enumeration_work f n Q ((p2Expr P).eval n Q)
    (expr_enumeration P n Q) (PeriodicActual.P2.expr_input P n Q)
  have hp : 1≤logHeight n := by unfold logHeight; omega
  have hm:=Nat.mul_le_mul_left ((p2Expr P).eval n Q) hp
  simp only [Nat.mul_one] at hm
  exact Nat.le_trans hh (Nat.mul_le_mul_left 480 hm)

def coefficient (P : SevenDFA (Fin σ)) : Nat :=
  solveFactor P*PeriodicActual.P2.coefficient P+480

theorem solve_expr (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (solve P f n Q).2≤coefficient P*((p2Expr P).eval n Q*logHeight n) := by
  have hh:=solve_work P f n Q
  have ho:=Nat.mul_le_mul_left (solveFactor P) (PeriodicActual.P2.solve_expr P f n Q)
  have he:=enumerate_expr P f n Q
  simp only [coefficient,Nat.add_mul,Nat.mul_assoc] at ho he ⊢
  omega

theorem solve_rounded (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n : Nat) :
    (solve P f n (ThresholdBudget.period n)).2≤
      (coefficient P*(p2Expr P).coeff)*(ThresholdBudget.base n)^75*logHeight n := by
  have hb:=Expr.bound75 (p2Expr P) (by rw [p2_degree]; exact Nat.le_refl _) n
  have hh:=Nat.mul_le_mul_left (coefficient P) (Nat.mul_le_mul_right (logHeight n) hb)
  exact Nat.le_trans (solve_expr P f n (ThresholdBudget.period n))
    (by simpa only [Nat.mul_assoc] using hh)

end P2
end REWB.PeriodicActual.FullCost
