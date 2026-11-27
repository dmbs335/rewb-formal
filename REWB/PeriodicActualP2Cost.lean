import REWB.PeriodicActualP2
import REWB.PeriodicAccounting

/-! The newly measured P2 descriptor/formula/schedule construction only
changes a fixed-pattern coefficient in the existing periodic expression.
No additional power of the run period is introduced by formula assembly. -/
namespace REWB.PeriodicActual.P2
open REWB.PeriodicAccounting
variable {σ : Nat}

def coefficient (P : SevenDFA (Fin σ)) : Nat := phaseBudget P+73

theorem expr_input (P : SevenDFA (Fin σ)) (n Q : Nat) :
    n+1≤(p2Expr P).eval n Q := by
  have hh : n+1≤(n+1)*(1+P.H.stateCount) := by
    simpa only [Nat.mul_one] using
      Nat.mul_le_mul_left (n+1) (show 1≤1+P.H.stateCount by omega)
  change n+1≤Q*(n+(n+1)*(2*Q*(Q+1)+1))+(n+1)*(1+P.H.stateCount)+
    (FullyCachedP2.stateSum P*Q+Q^2)*(2*n)+
    (7+CountedProjection.p2Steps P)*(Q^4*(2*n))
  omega

theorem solve_expr (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n Q : Nat) :
    (solve P f n Q).2≤coefficient P*((p2Expr P).eval n Q*logHeight n) := by
  let old := SmallPeriodP2.solve P f n Q
  let k := phaseBudget P+52
  let B := (p2Expr P).eval n Q*logHeight n
  have hn := solve_work P f n Q
  change (solve P f n Q).2≤old.runComparisons+old.contextEntries+old.cacheWork+
    k*old.phaseCalls+5*(2*n*DyadicIndex.heightFor n)+3*n+11 at hn
  have hk : 1≤k := by dsimp [k]; omega
  have hsum : old.runComparisons+old.contextEntries+old.cacheWork≤
      k*(old.runComparisons+old.contextEntries+old.cacheWork) := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right
      (old.runComparisons+old.contextEntries+old.cacheWork) hk
  have hpart : old.runComparisons+old.contextEntries+old.cacheWork+k*old.phaseCalls≤
      k*p2Work old := by
    have hfirst := Nat.add_le_add_right hsum (k*old.phaseCalls)
    rw [← Nat.mul_add] at hfirst
    have hinside : old.runComparisons+old.contextEntries+old.cacheWork+old.phaseCalls≤p2Work old := by
      unfold p2Work
      omega
    exact Nat.le_trans hfirst (Nat.mul_le_mul_left k hinside)
  have hold : p2Work old≤B := p2_bound P f n Q
  have hmain := Nat.le_trans hpart (Nat.mul_le_mul_left k hold)
  have hheight : 1≤logHeight n := by unfold logHeight; omega
  have hinput : (n+1)*logHeight n≤B := Nat.mul_le_mul_right _ (expr_input P n Q)
  have hinput' : n+1≤B := Nat.le_trans
    (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (n+1) hheight) hinput
  have hmass : 2*n*DyadicIndex.heightFor n≤2*B := by
    have hh := Nat.mul_le_mul_left (2*n) (height_le n)
    have hnb : n*logHeight n≤B := by
      have hx := Nat.mul_le_mul_right (logHeight n) (show n≤n+1 by omega)
      exact Nat.le_trans hx hinput
    have hh' := Nat.mul_le_mul_left 2 hnb
    rw [← Nat.mul_assoc] at hh'
    exact Nat.le_trans hh hh'
  have hextra := Nat.mul_le_mul_left 5 hmass
  have hlinear : 3*n+11≤11*B := by omega
  change (solve P f n Q).2≤(phaseBudget P+73)*B
  have he : (phaseBudget P+73)*B=k*B+21*B := by
    dsimp [k]
    simp only [Nat.add_mul]
    omega
  rw [he]
  omega

theorem solve_rounded (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n : Nat) :
    (solve P f n (ThresholdBudget.period n)).2≤
      (coefficient P*(p2Expr P).coeff)*(ThresholdBudget.base n)^75*logHeight n := by
  have hb := Expr.bound75 (p2Expr P) (by rw [p2_degree]; exact Nat.le_refl _) n
  have hh := Nat.mul_le_mul_left (coefficient P) (Nat.mul_le_mul_right (logHeight n) hb)
  have hs := solve_expr P f n (ThresholdBudget.period n)
  exact Nat.le_trans hs (by simpa only [Nat.mul_assoc] using hh)

end REWB.PeriodicActual.P2
