import REWB.MaskedPeriodicTextTail

/-! A forward, tail-recursive scan of an actual source window. Source
and target masks are immutable; the output array is a separate union of
successful source positions. The callback is instantiated with the real
indexed periodic query in `MaskedPeriodicBatch`.

`queryWork` sums the existing query counters, whose compiler-construction
exclusions remain explicit. `scanWork` charges one source-mask read,
optional output write and a fixed scalar allowance per visited source.
-/
namespace REWB.MaskedPeriodic.Batch
open REWB.MaskedProgression

def queryCost (a : IndexedAnswer) : Nat :=
  a.result.slots+a.result.arithmetic+a.products+a.visits

structure State where
  hits : Array Bool
  calls : Nat := 0
  queryWork : Nat := 0
  scanWork : Nat := 0
  preparationWork : Nat := 0
  deriving Repr

def record (s : Nat) (a : IndexedAnswer) (out : State) : State :=
  {out with
    hits:=if a.result.answer then out.hits.setIfInBounds s true else out.hits
    calls:=out.calls+1
    queryWork:=out.queryWork+queryCost a
    scanWork:=out.scanWork+5+(if a.result.answer then 1 else 0)}

def scan (ask : Nat → IndexedAnswer) (source : Array Bool) : Nat → Nat → State → State
  | 0,_,out => out
  | len+1,s,out =>
    let next := if readMask source s then record s (ask s) out
      else {out with scanWork:=out.scanWork+3}
    scan ask source len (s+1) next

theorem record_size (s : Nat) (a : IndexedAnswer) (out : State) :
    (record s a out).hits.size=out.hits.size := by
  simp only [record]
  split <;> simp

theorem record_read (s i : Nat) (a : IndexedAnswer) (out : State) :
    readMask (record s a out).hits i=true ↔
      readMask out.hits i=true ∨ (i=s ∧ i<out.hits.size ∧ a.result.answer=true) := by
  by_cases ha : a.result.answer=true
  · simp only [record,ha,ite_true]
    by_cases hi : i=s
    · subst i
      by_cases hs : s<out.hits.size
      · simp only [readMask,Array.getElem?_setIfInBounds_self_of_lt hs,Option.getD_some,
          true_or,hs,and_self,or_true]
      · have hz : out.hits[s]?=none := Array.getElem?_eq_none (by omega)
        have hz' : (out.hits.setIfInBounds s true)[s]?=none :=
          Array.getElem?_eq_none (by rw [Array.size_setIfInBounds]; omega)
        simp only [readMask,hz,hz',Option.getD_none,Bool.false_eq_true,hs,false_and,
          and_false,or_self]
    · rw [readMask,Array.getElem?_setIfInBounds_ne (Ne.symm hi)]
      simp only [readMask,hi,false_and,or_false]
  · simp [record,ha]

theorem scan_size (ask : Nat → IndexedAnswer) (source : Array Bool) (len s : Nat) (out : State) :
    (scan ask source len s out).hits.size=out.hits.size := by
  induction len generalizing s out with
  | zero => rfl
  | succ len ih =>
    rw [scan,ih]
    split
    · exact record_size _ _ _
    · rfl

theorem scan_read (ask : Nat → IndexedAnswer) (source : Array Bool) (len s : Nat)
    (out : State) (i : Nat) :
    readMask (scan ask source len s out).hits i=true ↔
      readMask out.hits i=true ∨
        (s≤i ∧ i<s+len ∧ i<out.hits.size ∧ readMask source i=true ∧
          (ask i).result.answer=true) := by
  induction len generalizing s out with
  | zero =>
    simp only [scan,Nat.add_zero]
    constructor
    · exact Or.inl
    · rintro (h|⟨hlo,hhi,_⟩)
      · exact h
      · omega
  | succ len ih =>
    rw [scan,ih]
    by_cases hm : readMask source s=true
    · simp only [hm,ite_true,record_read,record_size]
      constructor
      · rintro ((hold|⟨he,hi,ha⟩)|⟨hlo,hhi,hi,hmask,ha⟩)
        · exact Or.inl hold
        · subst i
          exact Or.inr ⟨Nat.le_refl _,by omega,hi,hm,ha⟩
        · exact Or.inr ⟨by omega,by omega,hi,hmask,ha⟩
      · rintro (hold|⟨hlo,hhi,hi,hmask,ha⟩)
        · exact Or.inl (Or.inl hold)
        · by_cases he : i=s
          · subst i
            exact Or.inl (Or.inr ⟨rfl,hi,ha⟩)
          · exact Or.inr ⟨by omega,by omega,hi,hmask,ha⟩
    · simp only [hm,ite_false]
      constructor
      · rintro (hold|⟨hlo,hhi,hi,hmask,ha⟩)
        · exact Or.inl hold
        · exact Or.inr ⟨by omega,by omega,hi,hmask,ha⟩
      · rintro (hold|⟨hlo,hhi,hi,hmask,ha⟩)
        · exact Or.inl hold
        · have he : i≠s := by intro h; subst i; exact hm hmask
          exact Or.inr ⟨by omega,by omega,hi,hmask,ha⟩

theorem scan_calls (ask : Nat → IndexedAnswer) (source : Array Bool) (len s : Nat) (out : State) :
    (scan ask source len s out).calls≤out.calls+len := by
  induction len generalizing s out with
  | zero => exact Nat.le_refl _
  | succ len ih =>
    rw [scan]
    split
    · have hh:=ih (s+1) (record s (ask s) out)
      simp only [record] at hh ⊢
      omega
    · have hh:=ih (s+1) {out with scanWork:=out.scanWork+3}
      dsimp only at hh
      exact Nat.le_trans hh (by omega)

theorem scan_work (ask : Nat → IndexedAnswer) (source : Array Bool) (len s : Nat) (out : State) :
    (scan ask source len s out).scanWork≤out.scanWork+6*len := by
  induction len generalizing s out with
  | zero => exact Nat.le_refl _
  | succ len ih =>
    rw [scan]
    split
    · have hh:=ih (s+1) (record s (ask s) out)
      by_cases ha : (ask s).result.answer=true
      · simp [record,ha] at hh ⊢; omega
      · simp [record,ha] at hh ⊢; omega
    · have hh:=ih (s+1) {out with scanWork:=out.scanWork+3}
      dsimp only at hh
      omega

theorem scan_query_work (ask : Nat → IndexedAnswer) (source : Array Bool) (len s limit : Nat)
    (out : State) (hb : ∀ i,s≤i → i<s+len → queryCost (ask i)≤limit) :
    (scan ask source len s out).queryWork≤out.queryWork+limit*len := by
  induction len generalizing s out with
  | zero => exact Nat.le_refl _
  | succ len ih =>
    have ht : ∀ i,s+1≤i → i<s+1+len → queryCost (ask i)≤limit :=
      fun i hi hj=>hb i (by omega) (by omega)
    have hs:=hb s (Nat.le_refl _) (by omega)
    rw [scan]
    split
    · have hh:=ih (s+1) (record s (ask s) out) ht
      simp only [record] at hh ⊢
      rw [Nat.mul_succ]
      omega
    · have hh:=ih (s+1) {out with scanWork:=out.scanWork+3} ht
      dsimp only at hh
      rw [Nat.mul_succ]
      omega

theorem scan_preparation (ask : Nat → IndexedAnswer) (source : Array Bool) (len s : Nat)
    (out : State) : (scan ask source len s out).preparationWork=out.preparationWork := by
  induction len generalizing s out with
  | zero => rfl
  | succ len ih =>
    rw [scan,ih]
    split <;> rfl

end REWB.MaskedPeriodic.Batch
