import REWB.MaskedProgressionAP
import REWB.MaskedOrderedEraseQuery

/-! A bounded residue-major key for mutable fixed-step progressions.
Only physical positions are encoded. In particular the construction never
loops over the step or its residue classes, even when the step is huge.
The key universe is bounded by `(len+1)^2`, independently of the step. -/
namespace REWB.MaskedMutableProgression

def encode (len step i : Nat) : Nat := (i%step)*(len+1)+i/step

def decode (len step key : Nat) : Nat := key/(len+1)+(key%(len+1))*step

theorem div_mono (d a b : Nat) (hd : 0<d) (hab : a≤b) : a/d≤b/d :=
  (Nat.le_div_iff_mul_le hd).mpr (Nat.le_trans (Nat.div_mul_le_self a d) hab)

theorem quotient_lt (len step i : Nat) (hi : i<len) : i/step<len+1 := by
  have hh:=Nat.div_le_self i step
  omega

theorem encode_div (len step i : Nat) (hi : i<len) :
    encode len step i/(len+1)=i%step := by
  unfold encode
  rw [Nat.add_comm _ (i/step),Nat.add_mul_div_right _ _ (Nat.succ_pos len),
    Nat.div_eq_of_lt (quotient_lt len step i hi),Nat.zero_add]

theorem encode_mod (len step i : Nat) (hi : i<len) :
    encode len step i%(len+1)=i/step := by
  unfold encode
  rw [Nat.add_comm _ (i/step),Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt (quotient_lt len step i hi)]

theorem decode_encode (len step i : Nat) (hi : i<len) :
    decode len step (encode len step i)=i := by
  unfold decode
  rw [encode_div len step i hi,encode_mod len step i hi,Nat.mul_comm]
  exact Nat.mod_add_div i step

theorem encode_injective (len step i j : Nat) (hi : i<len) (hj : j<len)
    (he : encode len step i=encode len step j) : i=j := by
  have hh:=congrArg (decode len step) he
  simpa only [decode_encode len step i hi,decode_encode len step j hj] using hh

theorem encode_bound (len step i : Nat) (hi : i<len) :
    encode len step i<(len+1)*(len+1) := by
  have hr:=Nat.mod_le i step
  have hq:=quotient_lt len step i hi
  calc
    encode len step i < (i%step)*(len+1)+(len+1) := Nat.add_lt_add_left hq _
    _ = (i%step+1)*(len+1) := by rw [Nat.add_mul,Nat.one_mul]
    _ ≤ (len+1)*(len+1) := Nat.mul_le_mul_right _ (by omega)

/-- Twice a logarithmic level count avoids any dependence on `step`. -/
def height (len : Nat) : Nat := 2*((len+1).log2+1)

theorem square_capacity (len : Nat) : (len+1)*(len+1)≤2^(height len) := by
  have hl : len+1≤2^((len+1).log2+1):=Nat.le_of_lt Nat.lt_log2_self
  have hh:=Nat.mul_le_mul hl hl
  rw [show height len=((len+1).log2+1)+((len+1).log2+1) by unfold height; omega,
    Nat.pow_add]
  exact hh

theorem encode_capacity (len step i : Nat) (hi : i<len) :
    encode len step i<2^(height len) :=
  Nat.lt_of_lt_of_le (encode_bound len step i hi) (square_capacity len)

theorem encode_step (len step start t : Nat) (hs : 0<step) :
    encode len step (start+t*step)=encode len step start+t := by
  unfold encode
  rw [Nat.add_mul_mod_self_right,Nat.add_mul_div_right _ _ hs]
  omega

/-- Within one residue class the key order is exactly physical order. -/
theorem encode_le_same (len step a b : Nat) (hs : 0<step)
    (hm : a%step=b%step) : encode len step a≤encode len step b ↔ a≤b := by
  constructor
  · intro hk
    have hq : a/step≤b/step := by unfold encode at hk; rw [hm] at hk; omega
    have hh:=Nat.mul_le_mul_left step hq
    have ha:=Nat.mod_add_div a step
    have hb:=Nat.mod_add_div b step
    omega
  · intro hab
    have hq:=div_mono step a b hs hab
    unfold encode
    rw [hm]
    omega

theorem interval_residue (len step start last i : Nat)
    (ha : start<len) (hb : last<len) (hi : i<len)
    (hr : last%step=start%step)
    (hlo : encode len step start≤encode len step i)
    (hhi : encode len step i≤encode len step last) : i%step=start%step := by
  have hl:=div_mono (len+1) _ _ (Nat.succ_pos len) hlo
  have hu:=div_mono (len+1) _ _ (Nat.succ_pos len) hhi
  rw [encode_div len step start ha,encode_div len step i hi] at hl
  rw [encode_div len step i hi,encode_div len step last hb,hr] at hu
  omega

/-- A clipped grid occupies one contiguous interval of encoded keys.
No key from a different residue can fall inside that interval. -/
theorem grid_interval (len step start used i : Nat) (hs : 0<step)
    (hu : 0<used) (ha : start<len) (hi : i<len)
    (hlast : start+(used-1)*step<len) :
    (encode len step start≤encode len step i ∧
      encode len step i≤encode len step start+(used-1)) ↔
      ∃t,t<used ∧ i=start+t*step := by
  have hend:=encode_step len step start (used-1) hs
  have hmod : (start+(used-1)*step)%step=start%step:=Nat.add_mul_mod_self_right _ _ _
  constructor
  · rintro ⟨hlo,hhi⟩
    have hhi' : encode len step i≤encode len step (start+(used-1)*step) := by
      rw [hend]; exact hhi
    have hr:=interval_residue len step start _ i ha hlast hi hmod hlo hhi'
    have hab : start≤i := (encode_le_same len step start i hs hr.symm).mp hlo
    have hq:=div_mono step start i hs hab
    let t:=i/step-start/step
    have htadd : start/step+t=i/step := Nat.add_sub_of_le hq
    have hphys : i=start+t*step := by
      have he:=Nat.mod_add_div start step
      calc
        i = i%step+step*(i/step) := (Nat.mod_add_div i step).symm
        _ = start%step+step*(start/step+t) := by rw [hr,htadd]
        _ = start+t*step := by rw [Nat.mul_add,←Nat.add_assoc,he,Nat.mul_comm step t]
    refine ⟨t,?_,hphys⟩
    have hkey:=encode_step len step start t hs
    rw [←hphys] at hkey
    omega
  · rintro ⟨t,ht,rfl⟩
    rw [encode_step len step start t hs]
    omega

end REWB.MaskedMutableProgression
