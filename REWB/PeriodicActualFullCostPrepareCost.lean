import REWB.PeriodicActualFullCostPrepare

/-! Complete periodic preparation construction changes fixed coefficients
of the existing degree-69 P1 expressions. The proof charges actual key
words/ranks and run enumeration, including their empty-input overhead.
Only canonical cubic-run packing is used for the key construction. -/
namespace REWB.PeriodicActual.FullCost
open REWB.PeriodicAccounting REWB.PeriodicConstruction
variable {σ : Nat}

theorem long_expr_enumeration (P : SevenDFA (Fin σ)) (n Q : Nat) :
    enumerationEnvelope n Q≤(longExpr P).eval n Q := by
  change enumerationEnvelope n Q≤enumerationEnvelope n Q+_+_+_+_+_+_+_+_+_+_+_
  omega

theorem short_expr_enumeration (P : SevenDFA (Fin σ)) (n Q : Nat) :
    enumerationEnvelope n Q≤(shortExpr P).eval n Q := by
  change enumerationEnvelope n Q≤enumerationEnvelope n Q+_+_+_+_+_+_+_+_+_+_+_
  omega

theorem long_expr_keys (P : SevenDFA (Fin σ)) (n Q : Nat) :
    ((3*σ+1)*Q+1)*(2*n*DyadicIndex.heightFor n)≤(longExpr P).eval n Q := by
  change ((3*σ+1)*Q+1)*(2*n*DyadicIndex.heightFor n)≤
    _+_+((3*σ+1)*Q+1)*(2*n*DyadicIndex.heightFor n)+_+_+_+_+_+_+_+_+_
  omega

theorem short_expr_keys (P : SevenDFA (Fin σ)) (n Q : Nat) :
    (P1ShortKeys.workConstant σ*Q^2+3*Q)*(2*n*DyadicIndex.heightFor n)≤(shortExpr P).eval n Q := by
  change (P1ShortKeys.workConstant σ*Q^2+3*Q)*(2*n*DyadicIndex.heightFor n)≤
    _+_+(_+(P1ShortKeys.workConstant σ*Q^2+3*Q)*(2*n*DyadicIndex.heightFor n))+
      _+_+_+_+_+_+_+_+_
  omega

namespace Long

theorem keys_expr (P : SevenDFA (Fin σ)) (R : ExactKeys.Registry σ)
    (f : Nat→Fin σ) (n Q : Nat) :
    (Keys.Rotation.tables R f (SmallPeriodRuns.cubic f n Q)).2≤98*(longExpr P).eval n Q := by
  let E:=(longExpr P).eval n Q
  let M:=2*n*DyadicIndex.heightFor n
  let c:=(3*σ+1)*Q+1
  have hkey : c*M≤E:=long_expr_keys P n Q
  have hq : Q≤c := by
    have h:=Nat.mul_le_mul_right Q (by omega : 1≤3*σ+1)
    simp only [Nat.one_mul] at h
    dsimp only [c]
    omega
  have hc : 1≤c := by dsimp only [c]; omega
  have hqM:=Nat.le_trans (Nat.mul_le_mul_right M hq) hkey
  have hM:=Nat.le_trans (Nat.mul_le_mul_right M hc) hkey
  simp only [Nat.one_mul] at hM
  have ht : Q*M+2*M≤3*E := by omega
  have hterm:=Nat.mul_le_mul_left 32 ht
  have hi:=PeriodicActual.long_expr_input P n Q
  change n+1≤E at hi
  have hk:=Keys.Rotation.concrete_work R f n Q
  change _≤(c+32*(Q+2))*M+1 at hk
  have he : (c+32*(Q+2))*M+1=c*M+32*(Q*M+2*M)+1 := by
    simp only [Nat.add_mul,Nat.mul_add,Nat.mul_assoc]
  rw [he] at hk
  change _≤98*E
  omega

def coefficient (P : SevenDFA (Fin σ)) : Nat :=
  P2.solveFactor P*PeriodicActual.Long.coefficient P+578

theorem prepare_expr (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (prepare P f n Q).2≤coefficient P*(longExpr P).eval n Q := by
  have hh:=prepare_work P f n Q
  have hp:=Nat.mul_le_mul_left (P2.solveFactor P) (PeriodicActual.Long.prepare_expr P f n Q)
  have he:=enumeration_work f n Q ((longExpr P).eval n Q)
    (long_expr_enumeration P n Q) (PeriodicActual.long_expr_input P n Q)
  have hk:=keys_expr P ExactKeys.initial f n Q
  simp only [coefficient,Nat.add_mul,Nat.mul_assoc] at hp ⊢
  omega

theorem prepare_rounded (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n : Nat) :
    (prepare P f n (ThresholdBudget.period n)).2≤
      (coefficient P*(longExpr P).coeff)*(ThresholdBudget.base n)^75 := by
  have hb:=Expr.bound75 (longExpr P) (by rw [long_degree]; decide) n
  exact Nat.le_trans (prepare_expr P f n (ThresholdBudget.period n))
    (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (coefficient P) hb)

end Long

namespace Short

theorem keys_expr (P : SevenDFA (Fin σ)) (R : ExactKeys.Registry σ)
    (f : Nat→Fin σ) (n Q : Nat) :
    (Keys.Short.tables R f (SmallPeriodRuns.cubic f n Q)).2≤1026*(shortExpr P).eval n Q := by
  let E:=(shortExpr P).eval n Q
  let M:=2*n*DyadicIndex.heightFor n
  let c:=P1ShortKeys.workConstant σ*Q^2+3*Q
  have hkey : c*M≤E:=short_expr_keys P n Q
  have hw : 1≤P1ShortKeys.workConstant σ := by unfold P1ShortKeys.workConstant; omega
  have hq2 : Q^2≤c := by
    have h:=Nat.mul_le_mul_right (Q^2) hw
    simp only [Nat.one_mul] at h
    dsimp only [c]
    omega
  have hq : Q≤c := by dsimp only [c]; omega
  have hq2M:=Nat.le_trans (Nat.mul_le_mul_right M hq2) hkey
  have hqM:=Nat.le_trans (Nat.mul_le_mul_right M hq) hkey
  have hM : M≤2*E:=PeriodicActual.mass_le_text n E (PeriodicActual.short_expr_text P n Q)
  have ht : Q^2*M+Q*M+M≤4*E := by omega
  have hterm:=Nat.mul_le_mul_left 256 ht
  have hi:=PeriodicActual.short_expr_input P n Q
  change n+1≤E at hi
  have hk:=Keys.Short.concrete_work R f n Q
  change _≤(c+256*(Q^2+Q+1))*M+1 at hk
  have he : (c+256*(Q^2+Q+1))*M+1=c*M+256*(Q^2*M+Q*M+M)+1 := by
    simp only [Nat.add_mul,Nat.mul_add,Nat.one_mul,Nat.mul_assoc]
  rw [he] at hk
  change _≤1026*E
  omega

def coefficient (P : SevenDFA (Fin σ)) : Nat :=
  P2.solveFactor P*PeriodicActual.Short.coefficient P+1506

theorem prepare_expr (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (prepare P f n Q).2≤coefficient P*(shortExpr P).eval n Q := by
  have hh:=prepare_work P f n Q
  have hp:=Nat.mul_le_mul_left (P2.solveFactor P) (PeriodicActual.Short.prepare_expr P f n Q)
  have he:=enumeration_work f n Q ((shortExpr P).eval n Q)
    (short_expr_enumeration P n Q) (PeriodicActual.short_expr_input P n Q)
  have hk:=keys_expr P
    (PeriodicActual.Short.sourceKeys ExactKeys.initial f
      (PeriodicActual.Short.sourceChoices n (3*Q)).1).1.registry f n Q
  simp only [coefficient,Nat.add_mul,Nat.mul_assoc] at hp ⊢
  omega

theorem prepare_rounded (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n : Nat) :
    (prepare P f n (ThresholdBudget.period n)).2≤
      (coefficient P*(shortExpr P).coeff)*(ThresholdBudget.base n)^75 := by
  have hb:=Expr.bound75 (shortExpr P) (by rw [short_degree]; decide) n
  exact Nat.le_trans (prepare_expr P f n (ThresholdBudget.period n))
    (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (coefficient P) hb)

end Short
end REWB.PeriodicActual.FullCost
