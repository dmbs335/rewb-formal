import REWB.MaskedEmpty

namespace REWB.MaskedEmpty
open MaskedProgression (readMask)
open MarkedDP (MarkedWord)
open Spec (slice)
variable {α : Type}

private theorem get_ofFn {n : Nat} (f : Fin n → Bool) (q : Fin n) :
    (Vector.ofFn f).get q = f q := by
  change (Vector.ofFn f)[q.val] = f q
  simp only [Vector.getElem_ofFn]

theorem compute_head (C E : DFA α) (mark : Bool) (xs : MarkedWord α) :
    (∀ q, (compute C E mark xs).head.suffix.get q =
      (MarkedDP.summarize C E mark xs).suffixAccept q) ∧
    (∀ q, (compute C E mark xs).head.gap.get q =
      (MarkedDP.summarize C E mark xs).canSwitch q) := by
  induction xs with
  | nil =>
    constructor <;> intro q <;>
      simp only [compute,terminal,terminalRow,MarkedDP.summarize,get_ofFn]
  | cons x xs ih =>
    rcases x with ⟨c,m⟩
    constructor <;> intro q
    · simp only [compute,step,nextRow,get_ofFn,ih.1,MarkedDP.summarize]
    · simp only [compute,step,nextRow,get_ofFn,ih.1,ih.2,MarkedDP.summarize]

theorem compute_length (C E : DFA α) (mark : Bool) (xs : MarkedWord α) :
    (compute C E mark xs).answers.length = xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (compute C E mark xs).answers.length+1=xs.length+1+1
    rw [ih]

theorem compute_get (C E : DFA α) (mark : Bool) (xs : MarkedWord α)
    (i : Nat) (hi : i≤xs.length) :
    (compute C E mark xs).answers[i]? =
      some ((MarkedDP.summarize C E mark (xs.drop i)).canSwitch C.initial) := by
  induction xs generalizing i with
  | nil =>
    have he : i=0 := by simpa only [List.length_nil,Nat.le_zero] using hi
    subst i
    simpa only [compute,terminal,List.getElem?_cons_zero,List.drop_zero] using
      congrArg some ((compute_head C E mark []).2 C.initial)
  | cons x xs ih =>
    cases i with
    | zero =>
      change some ((compute C E mark (x::xs)).head.gap.get C.initial)=_
      rw [(compute_head C E mark (x::xs)).2]
      rfl
    | succ i =>
      change (compute C E mark xs).answers[i]? =
        some ((MarkedDP.summarize C E mark (xs.drop i)).canSwitch C.initial)
      exact ih i (by simpa only [List.length_cons,Nat.add_le_add_iff_right] using hi)

theorem gate_size (accept : Bool) (source : Array Bool) (bits : List Bool) :
    (gate accept source bits).size=bits.length := by
  simp only [gate,List.size_toArray,List.length_map,List.length_zipIdx]

theorem gate_get (accept : Bool) (source : Array Bool) (bits : List Bool) (i : Nat) :
    (gate accept source bits)[i]? =
      bits[i]?.map (fun b => (accept && readMask source i) && b) := by
  simp only [gate,List.getElem?_toArray,List.getElem?_map,List.getElem?_zipIdx,
    Nat.zero_add,Option.map_map]
  rfl

theorem solve_size (B C E : DFA α) (w : Word α) (source target : Array Bool) :
    (solve B C E w source target).answers.size=w.length+1 := by
  simp only [solve,gate_size,compute_length,markWord_length]

theorem solve_at (B C E : DFA α) (w : Word α) (source target : Array Bool)
    (s : Nat) (hs : s≤w.length) :
    readMask (solve B C E w source target).answers s=true ↔
      readMask source s=true ∧ Witness B C E w target s := by
  have hlen : s≤(markWord target 0 w).length := by rwa [markWord_length]
  have hget := compute_get C E (readMask target w.length) (markWord target 0 w) s hlen
  rw [markWord_eq,IndexedMarked.decorate_drop,Nat.zero_add,
    ← MaskScan.slice_to_end w s hs] at hget
  unfold readMask
  change ((gate (B.final B.initial) source
    (compute C E (readMask target w.length) (markWord target 0 w)).answers)[s]?).getD false=true ↔ _
  rw [gate_get,markWord_eq,hget]
  simp only [Option.map,Option.getD,Bool.and_eq_true]
  rw [← MarkedTransfer.run_left,IndexedMarked.switch_iff_indices C E
    (readMask target) w s w.length C.initial hs (Nat.le_refl _)]
  change ((B.accepts [] ∧ readMask source s=true) ∧
    ∃ j, s≤j ∧ j≤w.length ∧ readMask target j=true ∧
      C.accepts (slice w s j) ∧ E.accepts (slice w j w.length)) ↔ _
  unfold Witness
  constructor
  · rintro ⟨⟨hb,hs⟩,h⟩
    exact ⟨hs,hb,h⟩
  · rintro ⟨hs,hb,h⟩
    exact ⟨⟨hb,hs⟩,h⟩

theorem solve_correct (B C E : DFA α) (w : Word α) (source target : Array Bool)
    (s : Nat) :
    readMask (solve B C E w source target).answers s=true ↔
      readMask source s=true ∧ Witness B C E w target s := by
  by_cases hs : s≤w.length
  · exact solve_at B C E w source target s hs
  · have ho : (solve B C E w source target).answers.size≤s := by
      rw [solve_size]
      omega
    simp only [readMask,Array.getElem?_eq_none ho,Option.getD,Bool.false_eq_true,
      false_iff]
    rintro ⟨_,_,j,hsj,hjn,_⟩
    omega

theorem witness_sound (B C E : DFA α) (w : Word α) (target : Array Bool)
    (s : Nat) (h : Witness B C E w target s) :
    Spec.maskedStart B C E w (readMask target) s := by
  rcases h with ⟨hb,j,hsj,hjn,hm,hc,he⟩
  refine ⟨s,j,j,Nat.le_refl _,hsj,Nat.le_refl _,hjn,hm,?_,?_,hc,he⟩
  · simp only [slice,Nat.sub_self,List.take_zero]
  · simpa only [slice,Nat.sub_self,List.take_zero] using hb

theorem solve_sound (B C E : DFA α) (w : Word α) (source target : Array Bool)
    (s : Nat) (h : readMask (solve B C E w source target).answers s=true) :
    readMask source s=true ∧ Spec.maskedStart B C E w (readMask target) s := by
  have hh := (solve_correct B C E w source target s).mp h
  exact ⟨hh.1,witness_sound B C E w target s hh.2⟩

def PositiveWitness (B C E : DFA α) (w : Word α) (target : Array Bool) (s : Nat) : Prop :=
  ∃ a j t, s<a ∧ a≤j ∧ j≤t ∧ t≤w.length ∧ readMask target j=true ∧
    slice w s a=slice w j t ∧ B.accepts (slice w s a) ∧
    C.accepts (slice w a j) ∧ E.accepts (slice w t w.length)

/-- The positive-length cluster machinery may require a strictly positive
    capture.  This partition proves that doing so loses no masked witness
    once solve has handled the empty branch. -/
theorem maskedStart_partition (B C E : DFA α) (w : Word α) (target : Array Bool)
    (s : Nat) :
    Spec.maskedStart B C E w (readMask target) s ↔
      Witness B C E w target s ∨ PositiveWitness B C E w target s := by
  constructor
  · rintro ⟨a,j,t,hsa,haj,hjt,htn,hm,heq,hb,hc,he⟩
    rcases Nat.lt_or_eq_of_le hsa with hpos | hzero
    · exact Or.inr ⟨a,j,t,hpos,haj,hjt,htn,hm,heq,hb,hc,he⟩
    · subst a
      have hlen := congrArg List.length heq
      rw [OuterColumn.slice_length w s s (Nat.le_refl _) (by omega),
        OuterColumn.slice_length w j t hjt htn] at hlen
      have htj : t=j := by omega
      subst t
      exact Or.inl ⟨by simpa only [slice,Nat.sub_self,List.take_zero] using hb,
        j,haj,htn,hm,hc,he⟩
  · intro h
    rcases h with hz | ⟨a,j,t,hsa,haj,hjt,htn,hm,heq,hb,hc,he⟩
    · exact witness_sound B C E w target s hz
    · exact ⟨a,j,t,Nat.le_of_lt hsa,haj,hjt,htn,hm,heq,hb,hc,he⟩

theorem solve_partition (B C E : DFA α) (w : Word α) (source target : Array Bool)
    (s : Nat) :
    (readMask source s=true ∧ Spec.maskedStart B C E w (readMask target) s) ↔
      readMask (solve B C E w source target).answers s=true ∨
        (readMask source s=true ∧ PositiveWitness B C E w target s) := by
  rw [maskedStart_partition,solve_correct]
  constructor
  · rintro ⟨hs,hz | hp⟩
    · exact Or.inl ⟨hs,hz⟩
    · exact Or.inr ⟨hs,hp⟩
  · rintro (⟨hs,hz⟩ | ⟨hs,hp⟩)
    · exact ⟨hs,Or.inl hz⟩
    · exact ⟨hs,Or.inr hp⟩

end REWB.MaskedEmpty
