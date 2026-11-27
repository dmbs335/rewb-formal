import Lean

/-! Explicit word-width witnesses from polynomial bounds.

These are arithmetic representation lemmas. A client must prove the
polynomial bound for its actual values, addresses and allocation trace;
this module does not assert such an invariant for the whole matcher. -/
namespace REWB.MachineWordBounds

def height (n : Nat) : Nat := (n+2).log2+1

def cap (coefficient degree n : Nat) : Nat := coefficient*(n+2)^degree

/-- The coefficient may be an arbitrarily large fixed-pattern constant. -/
def width (coefficient degree n : Nat) : Nat :=
  coefficient.log2+1+degree*height n

def bits (x : Nat) : Nat := x.log2+1

theorem height_positive (n : Nat) : 0<height n := by
  unfold height
  omega

theorem width_positive (coefficient degree n : Nat) : 0<width coefficient degree n := by
  unfold width
  omega

/-- Strict capacity includes the largest permitted value, not just
addresses strictly below it. -/
theorem cap_lt_two_pow_width (coefficient degree n : Nat) :
    cap coefficient degree n<2^(width coefficient degree n) := by
  have hn : 0<(n+2)^degree := Nat.pow_pos (by omega)
  have hbase : n+2≤2^(height n) := Nat.le_of_lt (Nat.lt_log2_self (n:=n+2))
  calc
    cap coefficient degree n<2^(coefficient.log2+1)*(n+2)^degree :=
      Nat.mul_lt_mul_of_pos_right (Nat.lt_log2_self (n:=coefficient)) hn
    _≤2^(coefficient.log2+1)*(2^(height n))^degree :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbase degree)
    _=2^(width coefficient degree n) := by
      rw [←Nat.pow_mul,←Nat.pow_add]
      simp only [width,Nat.mul_comm]

theorem value_fits {x coefficient degree n : Nat}
    (h : x≤cap coefficient degree n) : x<2^(width coefficient degree n) :=
  Nat.lt_of_le_of_lt h (cap_lt_two_pow_width coefficient degree n)

theorem address_fits {address cells coefficient degree n : Nat}
    (haddress : address<cells) (hcells : cells≤cap coefficient degree n) :
    address<2^(width coefficient degree n) :=
  value_fits (Nat.le_trans (Nat.le_of_lt haddress) hcells)

theorem bits_le_width {x coefficient degree n : Nat}
    (h : x≤cap coefficient degree n) : bits x≤width coefficient degree n := by
  by_cases hx : x=0
  · simp only [bits,hx,Nat.log2_zero]
    exact width_positive coefficient degree n
  · have hb := (Nat.log2_lt hx).mpr (value_fits h)
    unfold bits
    omega

/-- An explicit linear bound in log(n+2), without asymptotic notation. -/
theorem width_le_height (coefficient degree n : Nat) :
    width coefficient degree n≤(coefficient.log2+1+degree)*height n := by
  have h := Nat.mul_le_mul_left (coefficient.log2+1)
    (show 1≤height n from height_positive n)
  simp only [Nat.mul_one] at h
  unfold width
  rw [Nat.add_mul]
  omega

theorem bits_le_height {x coefficient degree n : Nat}
    (h : x≤cap coefficient degree n) :
    bits x≤(coefficient.log2+1+degree)*height n :=
  Nat.le_trans (bits_le_width h) (width_le_height coefficient degree n)

theorem family_fits {ι : Sort u} (values : ι→Nat) (coefficient degree n : Nat)
    (h : ∀i,values i≤cap coefficient degree n) :
    ∀i,values i<2^(width coefficient degree n) :=
  fun i=>value_fits (h i)

theorem exists_width (coefficient degree n : Nat) :
    ∃w,0<w ∧ cap coefficient degree n<2^w ∧
      w≤(coefficient.log2+1+degree)*height n :=
  ⟨width coefficient degree n,width_positive coefficient degree n,
    cap_lt_two_pow_width coefficient degree n,width_le_height coefficient degree n⟩

/-- This is a representation constructor, not a machine-state invariant. -/
def encode (x coefficient degree n : Nat) (h : x≤cap coefficient degree n) :
    Fin (2^(width coefficient degree n)) := ⟨x,value_fits h⟩

theorem encode_value (x coefficient degree n : Nat) (h : x≤cap coefficient degree n) :
    (encode x coefficient degree n h).val=x := rfl

theorem add_cap {x y first second degree n : Nat}
    (hx : x≤cap first degree n) (hy : y≤cap second degree n) :
    x+y≤cap (first+second) degree n := by
  simpa only [cap,Nat.add_mul] using Nat.add_le_add hx hy

theorem mul_cap {x y first second leftDegree rightDegree n : Nat}
    (hx : x≤cap first leftDegree n) (hy : y≤cap second rightDegree n) :
    x*y≤cap (first*second) (leftDegree+rightDegree) n := by
  have h := Nat.mul_le_mul hx hy
  simpa only [cap,Nat.pow_add,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using h

theorem sub_cap {x y coefficient degree n : Nat}
    (hx : x≤cap coefficient degree n) : x-y≤cap coefficient degree n :=
  Nat.le_trans (Nat.sub_le x y) hx

theorem div_cap {x y coefficient degree n : Nat}
    (hx : x≤cap coefficient degree n) : x/y≤cap coefficient degree n :=
  Nat.le_trans (Nat.div_le_self x y) hx

theorem mod_cap {x y coefficient degree n : Nat}
    (hx : x≤cap coefficient degree n) : x%y≤cap coefficient degree n :=
  Nat.le_trans (Nat.mod_le x y) hx

/-- A sign bit is charged explicitly for signed integer representations. -/
def signedBits (z : Int) : Nat := bits z.natAbs+1

theorem signed_bits_le_width {z : Int} {coefficient degree n : Nat}
    (h : z.natAbs≤cap coefficient degree n) :
    signedBits z≤width coefficient degree n+1 :=
  Nat.add_le_add_right (bits_le_width h) 1

theorem signed_bits_le_height {z : Int} {coefficient degree n : Nat}
    (h : z.natAbs≤cap coefficient degree n) :
    signedBits z≤(coefficient.log2+1+degree+1)*height n := by
  have hbits := bits_le_height h
  have hheight : 1≤height n := height_positive n
  unfold signedBits
  rw [Nat.add_mul,Nat.one_mul]
  omega

end REWB.MachineWordBounds
