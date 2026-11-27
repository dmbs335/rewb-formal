import REWB.ResidualCachedProfiles

/-! Integer parameter inequalities for the actual residual schedule.
The common choice is n+2≤t^39, s=t^3, Q=t^9 and L=D=t^13.
All logarithms remain explicit; no fractional powers or rounding
assumptions are used. -/
namespace REWB.ResidualCached.Rounded
open REWB.ResidualCached.Growth

theorem quotient (x t a b c : Nat) (hx : x≤c*t^a) (hb : b≤a) :
    x/t^b≤c*t^(a-b) := by
  apply Nat.div_le_of_le_mul
  have he : c*t^(a-b)*t^b=c*t^a := by
    rw [Nat.mul_assoc,←Nat.pow_add,Nat.sub_add_cancel hb]
  rw [Nat.mul_comm,he]
  exact hx

theorem power_le (t a b : Nat) (ht : 1≤t) (h : a≤b) : t^a≤t^b :=
  Nat.pow_le_pow_right ht h

theorem grid (n t : Nat) (ht : 1≤t) (hn : n+2≤t^39) :
    (n+2)*(n/t^3+2)≤3*t^75 := by
  have hd:=ThresholdBudget.quotient_bound n t 39 3 (by omega) (by decide)
  change n/t^3≤t^36 at hd
  have hp : 1≤t^36 := Nat.pow_pos (by omega)
  have hs : n/t^3+2≤3*t^36 := by omega
  have hh:=Nat.mul_le_mul hn hs
  have he : t^39*(3*t^36)=3*t^75 := by
    rw [Nat.mul_left_comm,←Nat.pow_add]
  rwa [he] at hh

theorem block (t : Nat) (ht : 1≤t) : (t^3+1)^2≤4*t^6 := by
  have hp : 1≤t^3 := Nat.pow_pos (by omega)
  have h : t^3+1≤2*t^3 := by omega
  have hh:=Nat.pow_le_pow_left h 2
  simpa only [Nat.mul_pow,←Nat.pow_mul,Nat.reduceMul,Nat.reducePow] using hh

theorem short (n t : Nat) (ht : 1≤t) (hn : n+2≤t^39) :
    (n+2)*(t^13+1)^2≤4*t^75 := by
  have hp : 1≤t^13 := Nat.pow_pos (by omega)
  have hs : t^13+1≤2*t^13 := by omega
  have hh:=Nat.mul_le_mul hn (Nat.pow_le_pow_left hs 2)
  have he : t^39*(2*t^13)^2=4*t^65 := by
    simp only [Nat.mul_pow,←Nat.pow_mul,Nat.reducePow,Nat.mul_left_comm,←Nat.pow_add]
  rw [he] at hh
  exact Nat.le_trans hh (Nat.mul_le_mul_left 4 (power_le t 65 75 ht (by decide)))

theorem strip (n t : Nat) (ht : 1≤t) (hn : n+2≤t^39) :
    ResidualDispatch.stripBudget n (t^13) (t^13)≤5*t^65 := by
  have hs : n^2≤t^78 := by
    have hh:=Nat.pow_le_pow_left (show n≤t^39 by omega) 2
    simpa only [←Nat.pow_mul] using hh
  have ha:=quotient (2*n^2) t 78 13 2 (Nat.mul_le_mul_left 2 hs) (by decide)
  have hb:=ThresholdBudget.quotient_bound (n^2) t 78 13 hs (by decide)
  change (2*n^2)/t^13≤2*t^65 at ha
  change n^2/t^13≤t^65 at hb
  unfold ResidualDispatch.stripBudget
  omega

theorem mass (n t : Nat) (ht : 1≤t) (hn : n+2≤t^39) :
    ResidualDispatch.runMassBudget n≤2*t^39*height n := by
  have hh:=PeriodicAccounting.height_le n
  change DyadicIndex.heightFor n≤height n at hh
  exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 (by omega : n≤t^39)) hh

theorem low (n t : Nat) (ht : 1≤t) (hn : n+2≤t^39) :
    ResidualDispatch.lowBudget n (t^13)≤4*t^52*height n := by
  have hp : 1≤t^13 := Nat.pow_pos (by omega)
  have hs : t^13+1≤2*t^13 := by omega
  have hh:=Nat.mul_le_mul hs (mass n t ht hn)
  change ResidualDispatch.lowBudget n (t^13)≤_ at hh
  have he : 2*t^13*(2*t^39*height n)=4*t^52*height n := by
    calc
      _=(2*2)*(t^13*t^39)*height n := by ac_rfl
      _=_ := by rw [←Nat.pow_add]
  rwa [he] at hh

theorem large (n t : Nat) (ht : 1≤t) (hn : n+2≤t^39) :
    ResidualDispatch.largeBudget n (t^9)≤6*t^69*height n := by
  have hh:=Nat.mul_le_mul (Nat.mul_le_mul_left 3 (by omega : n≤t^39)) (mass n t ht hn)
  have he : 3*t^39*(2*t^39*height n)=(6*t^69*height n)*t^9 := by
    calc
      _=(3*2)*(t^39*t^39)*height n := by ac_rfl
      _=(6*(t^69*t^9))*height n := by rw [←Nat.pow_add,←Nat.pow_add]
      _=_ := by ac_rfl
  rw [he] at hh
  unfold ResidualDispatch.largeBudget
  apply Nat.div_le_of_le_mul
  conv => rhs; rw [Nat.mul_comm]
  exact Nat.le_trans hh (Nat.mul_le_mul_left (6*t^69*height n) (Nat.le_succ _))

theorem windows (n t : Nat) (ht : 1≤t) (hn : n+2≤t^39) :
    ResidualDispatch.selectorBudget n (t^13) (t^13) (t^9)≤15*t^69*height n := by
  have hs:=strip n t ht hn
  have hl:=low n t ht hn
  have hg:=large n t ht hn
  have hH : 1≤height n := by unfold height; omega
  have h65:=Nat.mul_le_mul (Nat.mul_le_mul_left 5 (power_le t 65 69 ht (by decide))) hH
  have h52:=Nat.mul_le_mul_right (height n) (Nat.mul_le_mul_left 4 (power_le t 52 69 ht (by decide)))
  simp only [Nat.mul_one] at h65
  unfold ResidualDispatch.selectorBudget
  simp only [Nat.mul_assoc] at hs hl hg h65 h52 ⊢
  omega

theorem window_queries (n t : Nat) (ht : 1≤t) (hn : n+2≤t^39) :
    ResidualDispatch.selectorBudget n (t^13) (t^13) (t^9)*(t^3+1)^2≤60*t^75*height n := by
  have hh:=Nat.mul_le_mul (windows n t ht hn) (block t ht)
  have he : (15*t^69*height n)*(4*t^6)=60*t^75*height n := by
    calc
      _=(15*4)*(t^69*t^6)*height n := by ac_rfl
      _=_ := by rw [←Nat.pow_add]
  rwa [he] at hh

theorem selector_work (n t : Nat) (ht : 1≤t) (hn : n+2≤t^39) :
    ResidualDispatch.selectorWorkBudget n (t^13) (t^13) (t^9)≤549*t^75*height n := by
  have hw:=windows n t ht hn
  have hr:=mass n t ht hn
  have h69:=Nat.mul_le_mul_right (height n) (Nat.mul_le_mul_left 15 (power_le t 69 75 ht (by decide)))
  have h39:=Nat.mul_le_mul_right (height n) (Nat.mul_le_mul_left 2 (power_le t 39 75 ht (by decide)))
  have hpos : 1≤t^75*height n := Nat.mul_le_mul
    (show 1≤t^75 from Nat.pow_pos (by omega)) (show 1≤height n by unfold height; omega)
  have hh:=Nat.mul_le_mul_left 34 (Nat.le_trans hw h69)
  have hm:=Nat.mul_le_mul_left 12 (Nat.le_trans hr h39)
  unfold ResidualDispatch.selectorBudget at hh
  unfold ResidualDispatch.selectorWorkBudget
  simp only [Nat.mul_add,Nat.mul_assoc] at hh hm ⊢
  omega

theorem strip_extra (n t : Nat) (ht : 1≤t) (hn : n+2≤t^39) :
    13*((2*n^2)/t^13)+38*(n^2/t^13)+4≤68*t^75*height n := by
  have hs : n^2≤t^78 := by
    have hh:=Nat.pow_le_pow_left (show n≤t^39 by omega) 2
    simpa only [←Nat.pow_mul] using hh
  have ha:=quotient (2*n^2) t 78 13 2 (Nat.mul_le_mul_left 2 hs) (by decide)
  have hb:=ThresholdBudget.quotient_bound (n^2) t 78 13 hs (by decide)
  have hpow:=Nat.mul_le_mul (power_le t 65 75 ht (by decide)) (show 1≤height n by unfold height; omega)
  simp only [Nat.mul_one] at hpow
  change (2*n^2)/t^13≤2*t^65 at ha
  change n^2/t^13≤t^65 at hb
  have hp : 1≤t^65 := Nat.pow_pos (by omega)
  simp only [Nat.mul_assoc] at hpow ⊢
  omega

end REWB.ResidualCached.Rounded
