import REWB.MaskedEmptyBatch

/-! The physical output bitmap and its reporting history. A successful
band only visits its newly reported sources; it does not rescan the text
or copy the accumulated history. The history is prepended in the same
order as the mutable source erasures. -/
namespace REWB.MaskedTraversalAnswers
open MaskedProgression (readMask)

structure State where
  bits : Array Bool
  history : List Nat
  count : Nat
  work : Nat
  deriving Repr

def fromBits (bits : Array Bool) : State :=
  let ps:=MaskedEmpty.SourceBatch.positions bits
  ⟨bits,ps,ps.length,16*bits.size⟩

def pushOne (p : Nat) (out : State) : State :=
  ⟨out.bits.setIfInBounds p true,p::out.history,out.count+1,out.work+6⟩

def push (ps : List Nat) (out : State) : State := ps.foldl (fun acc p=>pushOne p acc) out

theorem pushOne_size (p : Nat) (out : State) : (pushOne p out).bits.size=out.bits.size :=
  Array.size_setIfInBounds

theorem pushOne_read (p i : Nat) (out : State) :
    readMask (pushOne p out).bits i=true ↔ readMask out.bits i=true ∨ (i=p ∧ i<out.bits.size) := by
  by_cases hi : i=p
  · subst i
    by_cases hp : p<out.bits.size
    · simp only [pushOne,readMask,Array.getElem?_setIfInBounds_self_of_lt hp,Option.getD_some,
        true_or,hp,and_self,or_true]
    · have hz : out.bits[p]?=none := Array.getElem?_eq_none (by omega)
      have hz' : (out.bits.setIfInBounds p true)[p]?=none :=
        Array.getElem?_eq_none (by rw [Array.size_setIfInBounds]; omega)
      simp only [pushOne,readMask,hz,hz',Option.getD_none,Bool.false_eq_true,hp,
        and_false,or_self]
  · rw [show (pushOne p out).bits=out.bits.setIfInBounds p true from rfl,
      readMask,Array.getElem?_setIfInBounds_ne (Ne.symm hi)]
    simp only [readMask,hi,false_and,or_false]

theorem push_size (ps : List Nat) (out : State) : (push ps out).bits.size=out.bits.size := by
  induction ps generalizing out with
  | nil => rfl
  | cons p ps ih => exact (ih (pushOne p out)).trans (pushOne_size p out)

theorem push_history (ps : List Nat) (out : State) :
    (push ps out).history=ps.reverse++out.history := by
  induction ps generalizing out with
  | nil => rfl
  | cons p ps ih =>
    change (push ps (pushOne p out)).history=_
    rw [ih,List.reverse_cons,List.append_assoc,List.singleton_append]
    rfl

theorem push_count (ps : List Nat) (out : State) : (push ps out).count=out.count+ps.length := by
  induction ps generalizing out with
  | nil => rfl
  | cons p ps ih =>
    change (push ps (pushOne p out)).count=_
    rw [ih]
    simp only [pushOne,List.length_cons]
    omega

theorem push_work (ps : List Nat) (out : State) : (push ps out).work=out.work+6*ps.length := by
  induction ps generalizing out with
  | nil => simp [push]
  | cons p ps ih =>
    change (push ps (pushOne p out)).work=_
    rw [ih]
    simp only [pushOne,List.length_cons,Nat.mul_add,Nat.mul_one]
    omega

theorem push_read (ps : List Nat) (out : State) (i : Nat) :
    readMask (push ps out).bits i=true ↔ readMask out.bits i=true ∨ (i∈ps ∧ i<out.bits.size) := by
  induction ps generalizing out with
  | nil => simp only [push,List.foldl_nil,List.not_mem_nil,false_and,or_false]
  | cons p ps ih =>
    change readMask (push ps (pushOne p out)).bits i=true ↔ _
    rw [ih,pushOne_read,pushOne_size,List.mem_cons]
    constructor
    · rintro ((ho|⟨he,hb⟩)|⟨hm,hb⟩)
      · exact Or.inl ho
      · exact Or.inr ⟨Or.inl he,hb⟩
      · exact Or.inr ⟨Or.inr hm,hb⟩
    · rintro (ho|⟨he|hm,hb⟩)
      · exact Or.inl (Or.inl ho)
      · exact Or.inl (Or.inr ⟨he,hb⟩)
      · exact Or.inr ⟨hm,hb⟩

structure Valid (n : Nat) (P : Nat→Prop) (out : State) : Prop where
  size : out.bits.size=n+1
  nodup : out.history.Nodup
  represented : ∀p,p∈out.history ↔ readMask out.bits p=true
  counted : out.count=out.history.length
  sound : ∀p,p∈out.history→p≤n ∧ P p

theorem fromBits_valid (n : Nat) (P : Nat→Prop) (bits : Array Bool) (hs : bits.size=n+1)
    (hp : ∀p,readMask bits p=true→P p) : Valid n P (fromBits bits) := by
  refine ⟨hs,MaskedEmpty.SourceBatch.positions_nodup bits,MaskedEmpty.SourceBatch.positions_mem bits,rfl,?_⟩
  intro p hm
  have hb:=(MaskedEmpty.SourceBatch.positions_mem bits p).mp hm
  refine ⟨?_,hp p hb⟩
  by_cases hi : p<bits.size
  · omega
  · simp only [readMask,Array.getElem?_eq_none (show bits.size≤p by omega),Option.getD_none,
      Bool.false_eq_true] at hb

theorem pushOne_valid (n : Nat) (P : Nat→Prop) (out : State) (hv : Valid n P out) (p : Nat)
    (hb : p≤n) (hp : P p) (hf : p∉out.history) : Valid n P (pushOne p out) := by
  refine ⟨(pushOne_size p out).trans hv.size,List.nodup_cons.mpr ⟨hf,hv.nodup⟩,?_,?_,?_⟩
  · intro i
    rw [pushOne_read]
    change i∈p::out.history ↔ _
    rw [List.mem_cons,hv.represented i]
    constructor
    · rintro (he|ho)
      · exact Or.inr ⟨he,by rw [he,hv.size]; omega⟩
      · exact Or.inl ho
    · rintro (ho|⟨he,_⟩)
      · exact Or.inr ho
      · exact Or.inl he
  · change out.count+1=out.history.length+1
    rw [hv.counted]
  · intro i hm
    rcases List.mem_cons.mp hm with he|ho
    · subst i; exact ⟨hb,hp⟩
    · exact hv.sound i ho

theorem push_valid (n : Nat) (P : Nat→Prop) (ps : List Nat) (out : State) (hv : Valid n P out)
    (hd : ps.Nodup) (hp : ∀p,p∈ps→p≤n ∧ P p ∧ p∉out.history) : Valid n P (push ps out) := by
  induction ps generalizing out with
  | nil => exact hv
  | cons p ps ih =>
    obtain ⟨hnot,hdup⟩:=List.nodup_cons.mp hd
    obtain ⟨hb,hP,hfresh⟩:=hp p List.mem_cons_self
    apply ih (pushOne p out) (pushOne_valid n P out hv p hb hP hfresh) hdup
    intro i hi
    obtain ⟨hib,hiP,hif⟩:=hp i (List.mem_cons_of_mem p hi)
    refine ⟨hib,hiP,?_⟩
    intro hm
    rcases List.mem_cons.mp hm with he|ho
    · exact hnot (he ▸ hi)
    · exact hif ho

private theorem subset_length (xs ys : List Nat) (hd : xs.Nodup)
    (hs : ∀x,x∈xs→x∈ys) : xs.length≤ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hf,ht⟩:=List.nodup_cons.mp hd
    have hx:=hs x List.mem_cons_self
    have hh:=ih (ys.erase x) ht (fun y hy=>
      (List.mem_erase_of_ne (show y≠x from fun he=>hf (he ▸ hy))).mpr
        (hs y (List.mem_cons_of_mem x hy)))
    rw [List.length_erase_of_mem hx] at hh
    simp only [List.length_cons]
    have hz : 0<ys.length := List.length_pos_iff.mpr (by intro he; simp only [he,List.not_mem_nil] at hx)
    omega

theorem Valid.count_le {n : Nat} {P : Nat→Prop} {out : State} (hv : Valid n P out) : out.count≤n+1 := by
  rw [hv.counted]
  have hh:=subset_length out.history (List.range (n+1)) hv.nodup
    (fun p hp=>List.mem_range.mpr (by have hb:=(hv.sound p hp).1; omega))
  simpa only [List.length_range] using hh

end REWB.MaskedTraversalAnswers
