import REWB.Specifications

/-! Integer rounding for the explicit proposed phase ledger. This is a
    numeric theorem about the defined ledger; it does not assert that
    an REWB algorithm incurs that ledger. Missing index and dispatch
    costs must still be bounded independently before applying it. -/
namespace REWB.ThresholdBudget

def scale (n : Nat) : Nat := (n+2).log2/39+1
def base (n : Nat) : Nat := 2^(scale n)
def block (n : Nat) : Nat := (base n)^3
def period (n : Nat) : Nat := (base n)^9
def length (n : Nat) : Nat := (base n)^13

theorem base_pos (n : Nat) : 0<base n := Nat.pow_pos (by decide)

theorem rounded_lower (n : Nat) : n+2≤(base n)^39 := by
  have hm := Nat.mod_lt (n+2).log2 (show 0<39 by decide)
  have hd := Nat.mod_add_div (n+2).log2 39
  have he : (n+2).log2+1≤scale n*39 := by unfold scale; omega
  have hp := Nat.pow_le_pow_of_le (show 1<2 by decide) he
  rw [Nat.pow_mul] at hp
  exact Nat.le_trans (Nat.le_of_lt (Nat.lt_log2_self (n:=n+2))) hp

theorem rounded_upper (n : Nat) : (base n)^39≤2^39*(n+2) := by
  have hd := Nat.div_mul_le_self (n+2).log2 39
  have he : scale n*39≤(n+2).log2+39 := by unfold scale; omega
  have hp := Nat.pow_le_pow_of_le (show 1<2 by decide) he
  rw [Nat.pow_add,Nat.pow_mul] at hp
  have hn := Nat.log2_self_le (show n+2≠0 by omega)
  calc
    _ ≤ 2^(n+2).log2*2^39 := hp
    _ ≤ (n+2)*2^39 := Nat.mul_le_mul_right _ hn
    _ = _ := Nat.mul_comm _ _

/-- Division is rounded upward by adding one. This safely bounds each
    rational quotient and also includes the exact-division boundary. -/
def ledgerAt (n t : Nat) : Nat :=
  (n^2/t^3+1) + n*(t^13)^2 +
  (n^2*(t^3)^2/t^13+1) + (n^2*(t^3)^2/t^13+1) +
  (n^2*(t^3)^2/t^9+1) + n*t^13*(t^3)^2 + n*(t^3)^2 + n*(t^9)^4

def ledger (n : Nat) : Nat := ledgerAt n (base n)

theorem quotient_bound (x t a b : Nat) (hx : x≤t^a) (hb : b≤a) :
    x/t^b≤t^(a-b) := by
  apply Nat.div_le_of_le_mul
  rw [← Nat.pow_add,Nat.add_sub_of_le hb]
  exact hx

theorem ledgerAt_bound (n t : Nat) (ht : 1≤t) (hn : n≤t^39) :
    ledgerAt n t≤12*t^75 := by
  have h2 : n^2≤t^78 := by
    simpa only [← Nat.pow_mul] using Nat.pow_le_pow_left hn 2
  have h84 : n^2*(t^3)^2≤t^84 := by
    have h := Nat.mul_le_mul_right ((t^3)^2) h2
    simpa only [← Nat.pow_mul,← Nat.pow_add] using h
  have h1 := quotient_bound _ t 78 3 h2 (by decide)
  have h3 := quotient_bound _ t 84 13 h84 (by decide)
  have h4 := quotient_bound _ t 84 9 h84 (by decide)
  change n^2/t^3≤t^75 at h1
  change n^2*(t^3)^2/t^13≤t^71 at h3
  change n^2*(t^3)^2/t^9≤t^75 at h4
  have hshort : n*(t^13)^2≤t^65 := by
    calc
      _ ≤ t^39*(t^13)^2 := Nat.mul_le_mul_right _ hn
      _ = _ := by rw [← Nat.pow_mul,← Nat.pow_add]
  have hlow : n*t^13*(t^3)^2≤t^58 := by
    have h := Nat.mul_le_mul_right ((t^3)^2) (Nat.mul_le_mul_right (t^13) hn)
    simpa only [← Nat.pow_mul,← Nat.pow_add] using h
  have hlinear : n*(t^3)^2≤t^45 := by
    calc
      _ ≤ t^39*(t^3)^2 := Nat.mul_le_mul_right _ hn
      _ = _ := by rw [← Nat.pow_mul,← Nat.pow_add]
  have hsmall : n*(t^9)^4≤t^75 := by
    calc
      _ ≤ t^39*(t^9)^4 := Nat.mul_le_mul_right _ hn
      _ = _ := by rw [← Nat.pow_mul,← Nat.pow_add]
  have h65 := Cost.pow_mono_exponent t 65 75 ht (by decide)
  have h71 := Cost.pow_mono_exponent t 71 75 ht (by decide)
  have h58 := Cost.pow_mono_exponent t 58 75 ht (by decide)
  have h45 := Cost.pow_mono_exponent t 45 75 ht (by decide)
  have hpos : 1≤t^75 := Nat.pow_pos (by omega)
  unfold ledgerAt
  omega

def constant : Nat := 12^13*(2^39)^25

set_option exponentiation.threshold 1024 in
theorem ledger_power (n : Nat) : (ledger n)^13≤constant*(n+2)^25 := by
  have hbase : 1≤base n := base_pos n
  have hlo := rounded_lower n
  have h := Nat.pow_le_pow_left (ledgerAt_bound n (base n) hbase (by omega)) 13
  have he : ((base n)^75)^13=((base n)^39)^25 := by
    rw [← Nat.pow_mul,← Nat.pow_mul]
  rw [Nat.mul_pow,he] at h
  have hu := Nat.pow_le_pow_left (rounded_upper n) 25
  rw [Nat.mul_pow] at hu
  exact Nat.le_trans h (by
    simpa only [constant,Nat.mul_assoc] using Nat.mul_le_mul_left (12^13) hu)

/-- The explicit arithmetic ledger satisfies the target exponent.
    This is deliberately not a complexity assertion for FullMatcher. -/
theorem ledger_target : Spec.Target25Over13 ledger := by
  refine ⟨constant,0,?_,?_⟩
  · exact Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (Nat.pow_pos (by decide)))
  · intro n
    simpa only [Nat.pow_zero,Nat.mul_one] using ledger_power n

end REWB.ThresholdBudget
