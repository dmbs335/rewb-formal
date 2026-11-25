import REWB.MaskedReporting

/-! Stepped prefix counts for an immutable arbitrary mask.

    A run window is represented by `base` and `len`; no copy of the input
    mask is made.  One forward pass fills a preallocated Nat array, reading
    the earlier count at i-step when it exists.  The implementation never
    loops over residues or over step.  Slot counters charge input/count
    reads and count writes, including initial zero writes. Arithmetic
    counters charge fixed scalar operations per iteration. Unit array
    access (including bounds checking) and unit Nat arithmetic are the
    explicit abstract model. The scalar charge covers source operations
    such as +,-,*,/, comparisons, min/max and control; it excludes the
    counter bookkeeping itself and does not claim a bit-complexity bound.

    Reference count functions below occur in proofs, not in the executable
    builder or queries. No masked-index or complete matcher bound is claimed.
-/
namespace REWB.MaskedProgression

def readMask (mask : Array Bool) (i : Nat) : Bool := mask[i]?.getD false
def bit (b : Bool) : Nat := if b then 1 else 0

theorem bit_le (b : Bool) : bit b≤1 := by cases b <;> decide
theorem bit_pos (b : Bool) : 0<bit b ↔ b=true := by cases b <;> decide

def countAt (mask : Nat → Bool) (step : Nat) (hs : 0<step) (i : Nat) : Nat :=
  bit (mask i) + if _h : step≤i then countAt mask step hs (i-step) else 0
termination_by i
decreasing_by omega

theorem countAt_eq (mask : Nat → Bool) (step : Nat) (hs : 0<step) (i : Nat) :
    countAt mask step hs i =
      bit (mask i)+(if step≤i then countAt mask step hs (i-step) else 0) := by
  rw [countAt]
  by_cases hp : step≤i <;> simp [hp]

def before (mask : Nat → Bool) (step : Nat) (hs : 0<step) (i : Nat) : Nat :=
  if step≤i then countAt mask step hs (i-step) else 0

def tally (mask : Nat → Bool) (step start : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => tally mask step start n + bit (mask (start+n*step))

theorem tally_pos (mask : Nat → Bool) (step start n : Nat) :
    0<tally mask step start n ↔ ∃ t, t<n ∧ mask (start+t*step)=true := by
  induction n with
  | zero => simp [tally]
  | succ n ih =>
    rw [tally]
    have hb := bit_pos (mask (start+n*step))
    constructor
    · intro h
      by_cases hp : 0<tally mask step start n
      · obtain ⟨t,ht,hm⟩ := ih.mp hp
        exact ⟨t,by omega,hm⟩
      · exact ⟨n,by omega,hb.mp (by omega)⟩
    · rintro ⟨t,ht,hm⟩
      by_cases he : t=n
      · subst t
        have hh := hb.mpr hm
        omega
      · have hh := ih.mpr ⟨t,by omega,hm⟩
        omega

/-- Counts on one progression consist of the count before its start plus
    the exact marked positions subsequently visited on that progression. -/
theorem countAt_tally (mask : Nat → Bool) (step : Nat) (hs : 0<step)
    (start n : Nat) :
    countAt mask step hs (start+n*step)=
      before mask step hs start+tally mask step start (n+1) := by
  induction n with
  | zero =>
    rw [Nat.zero_mul,Nat.add_zero,countAt_eq]
    change bit (mask start)+(if step≤start then countAt mask step hs (start-step) else 0)=
      (if step≤start then countAt mask step hs (start-step) else 0)+(0+bit (mask (start+0*step)))
    simp only [Nat.zero_mul,Nat.add_zero,Nat.zero_add]
    omega
  | succ n ih =>
    have hp : step≤start+(n+1)*step := by
      rw [Nat.add_mul,Nat.one_mul]
      omega
    have he : start+(n+1)*step-step=start+n*step := by
      rw [Nat.add_mul,Nat.one_mul]
      omega
    rw [countAt_eq,if_pos hp,he,ih]
    change bit (mask (start+(n+1)*step))+
      (before mask step hs start+tally mask step start (n+1))=
      before mask step hs start+(tally mask step start (n+1)+bit (mask (start+(n+1)*step)))
    omega

theorem countAt_le (mask : Nat → Bool) (step : Nat) (hs : 0<step) (i : Nat) :
    countAt mask step hs i≤i+1 := by
  induction i using Nat.strongRecOn with
  | ind i ih =>
    rw [countAt_eq]
    have hb := bit_le (mask i)
    split
    next hp =>
      have hh := ih (i-step) (by omega)
      omega
    next hp => omega

def readCount (a : Array Nat) (i : Nat) : Nat := a[i]?.getD 0

structure Built where
  counts : Array Nat
  slots : Nat
  arithmetic : Nat
  deriving Repr

def fill (mask : Array Bool) (base step : Nat) :
    Nat → Nat → Array Nat → Nat → Nat → Built
  | 0,_,a,slots,arithmetic => ⟨a,slots,arithmetic⟩
  | remaining+1,i,a,slots,arithmetic =>
    let prev := if step≤i then readCount a (i-step) else 0
    let next := bit (readMask mask (base+i))+prev
    fill mask base step remaining (i+1) (a.setIfInBounds i next)
      (slots+2+(if step≤i then 1 else 0))
      (arithmetic+8+(if step≤i then 1 else 0))

theorem fill_size (mask : Array Bool) (base step remaining i : Nat)
    (a : Array Nat) (slots arithmetic : Nat) :
    (fill mask base step remaining i a slots arithmetic).counts.size=a.size := by
  induction remaining generalizing i a slots arithmetic with
  | zero => rfl
  | succ remaining ih => rw [fill,ih,Array.size_setIfInBounds]

theorem fill_slots (mask : Array Bool) (base step remaining i : Nat)
    (a : Array Nat) (slots arithmetic : Nat) :
    (fill mask base step remaining i a slots arithmetic).slots≤slots+3*remaining := by
  induction remaining generalizing i a slots arithmetic with
  | zero => exact Nat.le_refl _
  | succ remaining ih =>
    rw [fill]
    have hh := ih (i+1)
      (a.setIfInBounds i (bit (readMask mask (base+i))+
        if step≤i then readCount a (i-step) else 0))
      (slots+2+(if step≤i then 1 else 0))
      (arithmetic+8+(if step≤i then 1 else 0))
    by_cases hp : step≤i <;> simp only [hp,if_true,if_false] at hh ⊢ <;> omega

theorem fill_arithmetic (mask : Array Bool) (base step remaining i : Nat)
    (a : Array Nat) (slots arithmetic : Nat) :
    (fill mask base step remaining i a slots arithmetic).arithmetic≤arithmetic+9*remaining := by
  induction remaining generalizing i a slots arithmetic with
  | zero => exact Nat.le_refl _
  | succ remaining ih =>
    rw [fill]
    have hh := ih (i+1)
      (a.setIfInBounds i (bit (readMask mask (base+i))+
        if step≤i then readCount a (i-step) else 0))
      (slots+2+(if step≤i then 1 else 0))
      (arithmetic+8+(if step≤i then 1 else 0))
    by_cases hp : step≤i <;> simp only [hp,if_true,if_false] at hh ⊢ <;> omega

/-- Exactly one optional predecessor read is performed for each index
    in the visited range which is at least step. -/
theorem fill_slots_exact (mask : Array Bool) (base step remaining i : Nat)
    (a : Array Nat) (slots arithmetic : Nat) :
    (fill mask base step remaining i a slots arithmetic).slots=
      slots+2*remaining+((i+remaining-step)-(i-step)) := by
  induction remaining generalizing i a slots arithmetic with
  | zero => simp only [fill,Nat.mul_zero,Nat.add_zero,Nat.sub_self]
  | succ remaining ih =>
    rw [fill,ih]
    by_cases hp : step≤i <;> simp only [hp,if_true,if_false] <;> omega

theorem fill_arithmetic_exact (mask : Array Bool) (base step remaining i : Nat)
    (a : Array Nat) (slots arithmetic : Nat) :
    (fill mask base step remaining i a slots arithmetic).arithmetic=
      arithmetic+8*remaining+((i+remaining-step)-(i-step)) := by
  induction remaining generalizing i a slots arithmetic with
  | zero => simp only [fill,Nat.mul_zero,Nat.add_zero,Nat.sub_self]
  | succ remaining ih =>
    rw [fill,ih]
    by_cases hp : step≤i <;> simp only [hp,if_true,if_false] <;> omega

def PrefixGood (mask : Array Bool) (base step : Nat) (hs : 0<step)
    (a : Array Nat) (i : Nat) : Prop :=
  ∀ j, j<i → readCount a j=countAt (fun x => readMask mask (base+x)) step hs j

theorem fill_correct (mask : Array Bool) (base step : Nat) (hs : 0<step)
    (remaining i : Nat) (a : Array Nat) (slots arithmetic : Nat)
    (hbound : i+remaining≤a.size) (hg : PrefixGood mask base step hs a i) :
    PrefixGood mask base step hs
      (fill mask base step remaining i a slots arithmetic).counts (i+remaining) := by
  induction remaining generalizing i a slots arithmetic with
  | zero => simpa only [fill,Nat.add_zero] using hg
  | succ remaining ih =>
    let next := bit (readMask mask (base+i))+
      if step≤i then readCount a (i-step) else 0
    have hn : next=countAt (fun x => readMask mask (base+x)) step hs i := by
      rw [countAt_eq]
      dsimp only [next]
      congr 1
      split
      next hp => exact hg _ (by omega)
      next hp => rfl
    have hi : i<a.size := by omega
    have hnext : PrefixGood mask base step hs (a.setIfInBounds i next) (i+1) := by
      intro j hj
      by_cases he : i=j
      · subst j
        unfold readCount
        rw [Array.getElem?_setIfInBounds_self_of_lt hi]
        exact hn
      · unfold readCount
        rw [Array.getElem?_setIfInBounds_ne he]
        exact hg _ (by omega)
    have hh := ih (i+1) (a.setIfInBounds i next)
      (slots+2+(if step≤i then 1 else 0))
      (arithmetic+8+(if step≤i then 1 else 0))
      (by rw [Array.size_setIfInBounds]; omega) hnext
    simpa only [fill,show i+1+remaining=i+(remaining+1) by omega] using hh

def build (mask : Array Bool) (base len step : Nat) : Built :=
  fill mask base step len 0 (Array.replicate len 0) len 0

theorem build_size (mask : Array Bool) (base len step : Nat) :
    (build mask base len step).counts.size=len := by
  rw [build,fill_size,Array.size_replicate]

theorem build_correct (mask : Array Bool) (base len step : Nat) (hs : 0<step)
    (i : Nat) (hi : i<len) :
    readCount (build mask base len step).counts i=
      countAt (fun x => readMask mask (base+x)) step hs i := by
  exact fill_correct mask base step hs len 0 (Array.replicate len 0) len 0
    (by simp) (by intro j hj; omega) i (by omega)

theorem build_slots (mask : Array Bool) (base len step : Nat) :
    (build mask base len step).slots≤4*len := by
  have hh := fill_slots mask base step len 0 (Array.replicate len 0) len 0
  change (fill mask base step len 0 (Array.replicate len 0) len 0).slots≤_
  omega

theorem build_arithmetic (mask : Array Bool) (base len step : Nat) :
    (build mask base len step).arithmetic≤9*len := by
  simpa only [build,Nat.zero_add] using
    fill_arithmetic mask base step len 0 (Array.replicate len 0) len 0

theorem build_slots_exact (mask : Array Bool) (base len step : Nat) :
    (build mask base len step).slots=3*len+(len-step) := by
  rw [build,fill_slots_exact]
  omega

theorem build_arithmetic_exact (mask : Array Bool) (base len step : Nat) :
    (build mask base len step).arithmetic=8*len+(len-step) := by
  rw [build,fill_arithmetic_exact]
  omega

theorem build_work (mask : Array Bool) (base len step : Nat) :
    (build mask base len step).slots+(build mask base len step).arithmetic≤13*len := by
  have hs := build_slots mask base len step
  have ha := build_arithmetic mask base len step
  omega

theorem build_counts_le (mask : Array Bool) (base len step : Nat) (hs : 0<step)
    (i : Nat) (hi : i<len) : readCount (build mask base len step).counts i≤len := by
  rw [build_correct mask base len step hs i hi]
  have hh := countAt_le (fun x => readMask mask (base+x)) step hs i
  omega

end REWB.MaskedProgression
