import REWB.MaskedPeriodicPhase
import REWB.ArrayText
import REWB.P1GlobalJoin

/-! Text identities behind the local periodic compiler. Every factor is
    derived from an actual periodic character accessor; no answer oracle
    or independently supplied factor words occur in the hypotheses.
-/
namespace REWB.MaskedPeriodic.Text
open REWB.Periodic
open REWB.P2Periodic (factor factor_split)
variable {α : Type}

theorem capture (f : Nat→α) (n q a rho : Nat) (hp : Period f n q)
    (hb : a*q+rho≤n) :
    factor f 0 (a*q+rho)=repeatWord (segment f 0 q) a++segment f 0 rho := by
  simp only [factor,Nat.sub_zero]
  rw [segment_append,segment_repeated hp 0 a (by omega)]
  have hs := segment_same_phase hp 0 a rho (by omega)
  simpa only [Nat.zero_add] using congrArg (List.append (repeatWord (segment f 0 q) a)) hs.symm

theorem zero_gap (f : Nat→α) (n q a k : Nat) (hp : Period f n q)
    (ha : a≤k) (hk : k*q≤n) :
    factor f (a*q) (k*q)=repeatWord (segment f 0 q) (k-a) := by
  have hm : a*q+(k-a)*q=k*q := by rw [←Nat.add_mul,Nat.add_sub_of_le ha]
  have hs := segment_same_phase hp 0 a ((k-a)*q) (by omega)
  simp only [Nat.zero_add] at hs
  rw [factor,←Nat.sub_mul,←hs,segment_repeated hp 0 (k-a) (by omega)]

theorem positive_gap (f : Nat→α) (n q a k rho : Nat) (hp : Period f n q)
    (hr : rho≤q) (ha : a+1≤k) (hk : k*q≤n) :
    factor f (a*q+rho) (k*q)=
      factor f rho q++repeatWord (segment f 0 q) (k-a-1) := by
  have hm := Nat.mul_le_mul_right q ha
  have he : (a+1)*q=a*q+q := by rw [Nat.add_mul,Nat.one_mul]
  have first : factor f (a*q+rho) ((a+1)*q)=factor f rho q := by
    have hs := segment_same_phase hp rho a (q-rho) (by omega)
    rw [factor,factor,show (a+1)*q-(a*q+rho)=q-rho by omega]
    rw [show a*q+rho=rho+a*q by omega]
    exact hs.symm
  rw [factor_split f (a*q+rho) ((a+1)*q) (k*q) (by omega) hm,
    first,zero_gap f n q (a+1) k hp ha hk,Nat.sub_add_eq]

theorem fragment (f : Nat→α) (n q N eta : Nat) (hp : Period f n q)
    (hb : N*q+eta≤n) :
    factor f (N*q) (N*q+eta)=segment f 0 eta := by
  rw [factor,show N*q+eta-N*q=eta by omega]
  have hs := segment_same_phase hp 0 N eta (by omega)
  simpa only [Nat.zero_add] using hs.symm

theorem zero_suffix (f : Nat→α) (n q u N eta : Nat) (hp : Period f n q)
    (hu : u≤N) (hb : N*q+eta≤n) :
    factor f (u*q) (N*q+eta)=
      repeatWord (segment f 0 q) (N-u)++segment f 0 eta := by
  rw [factor_split f (u*q) (N*q) (N*q+eta) (Nat.mul_le_mul_right q hu) (by omega),
    zero_gap f n q u N hp hu (by omega),fragment f n q N eta hp hb]

theorem interior_suffix (f : Nat→α) (n q u rho N eta : Nat) (hp : Period f n q)
    (hr : rho≤q) (hu : u+1≤N) (hb : N*q+eta≤n) :
    factor f (u*q+rho) (N*q+eta)=
      factor f rho q++repeatWord (segment f 0 q) (N-u-1)++segment f 0 eta := by
  have hm := Nat.mul_le_mul_right q hu
  rw [Nat.add_mul,Nat.one_mul] at hm
  rw [factor_split f (u*q+rho) (N*q) (N*q+eta) (by omega) (by omega),
    positive_gap f n q u N rho hp hr hu (by omega),fragment f n q N eta hp hb]

theorem ending_suffix (f : Nat→α) (n q rho N eta : Nat) (hp : Period f n q)
    (hr : rho≤eta) (hb : N*q+eta≤n) :
    factor f (N*q+rho) (N*q+eta)=factor f rho eta := by
  rw [factor,factor,show N*q+eta-(N*q+rho)=eta-rho by omega]
  have hs := segment_same_phase hp rho N (eta-rho) (by omega)
  rw [show N*q+rho=rho+N*q by omega]
  exact hs.symm

/-- The target copy equals the source copy because its offset is k*q.
    This is the actual text equality required by the backreference. -/
theorem equal_copies (f : Nat→α) (n q k L : Nat) (hp : Period f n q)
    (hb : k*q+L≤n) : factor f 0 L=factor f (k*q) (k*q+L) := by
  simp only [factor,Nat.sub_zero,show k*q+L-k*q=L by omega]
  simpa only [Nat.zero_add] using segment_same_phase hp 0 k L (by omega)

/-- Long copy lengths are exactly a*q+rho with a>=2 and rho<q. -/
theorem long_quotient (q L : Nat) (hq : 0<q) : 2*q≤L ↔ 2≤L/q := by
  exact (Nat.le_div_iff_mul_le hq).symm

theorem quotient_length (q L : Nat) : (L/q)*q+L%q=L := by
  rw [Nat.mul_comm (L/q) q,Nat.add_comm]
  exact Nat.mod_add_div L q

end REWB.MaskedPeriodic.Text
