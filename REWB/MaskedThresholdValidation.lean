import REWB.MaskedThresholdEvents

/-! Lazy cancellation against the actual completed occurrence tree.
An expired threshold reaches the repair list exactly when its pair is
still adjacent. The validation loop charges discarded records as well
as live ones; immutable target masks play no role in occurrence geometry.
-/
namespace REWB.MaskedThresholdEvents
open REWB.MaskedEventBudget (Threshold)
open REWB.MaskedThresholdQueue
open REWB.MaskedRunDiscovery (Adjacent)
variable {h : Nat}

def check (t : MaskedOrdered.Tree h) (cap : Nat) (e : Threshold) : Bool × Nat :=
  let first:=MaskedOrdered.Tree.contains t cap e.edge.1
  let next:=MaskedOrdered.Tree.succ t cap e.edge.1
  (first.1 && decide (next.1=some e.edge.2),first.2+next.2+4)

theorem check_correct (t : MaskedOrdered.Tree h) (cap : Nat) (e : Threshold)
    (hg : t.Good) (hf : t.Fits 0) (hc : cap=2^h) :
    (check t cap e).1=true ↔ Adjacent t.entries e.edge.1 e.edge.2 := by
  simp only [check,Bool.and_eq_true,decide_eq_true_eq]
  rw [MaskedOrdered.Tree.contains_correct t cap e.edge.1 hf hc]
  constructor
  · rintro ⟨hi,hs⟩
    have hn:=MaskedOrdered.Tree.succ_correct t cap e.edge.1 hg hf hc
    rw [hs] at hn
    refine ⟨hi,hn.1,hn.2.1,?_⟩
    intro k hk hik hkj
    have hh:=hn.2.2 k hk hik
    omega
  · intro ha
    refine ⟨ha.1,?_⟩
    apply MaskedOrdered.succ_unique t.entries e.edge.1 _ (some e.edge.2)
      (MaskedOrdered.Tree.succ_correct t cap e.edge.1 hg hf hc)
    refine ⟨ha.2.1,ha.2.2.1,?_⟩
    intro k hk hik
    by_cases he : e.edge.2≤k
    · exact he
    · exact False.elim (ha.2.2.2 k hk hik (by omega))

theorem check_work (t : MaskedOrdered.Tree h) (cap : Nat) (e : Threshold) :
    (check t cap e).2≤11*h+9 := by
  have hm:=MaskedOrdered.Tree.contains_work t cap e.edge.1
  have hs:=MaskedOrdered.Tree.succ_work t cap e.edge.1
  change (MaskedOrdered.Tree.contains t cap e.edge.1).2+
    (MaskedOrdered.Tree.succ t cap e.edge.1).2+4≤11*h+9
  omega

def validateLoop (t : MaskedOrdered.Tree h) (cap : Nat) :
    List (Entry Threshold) → List (Entry Threshold) → Nat → List (Entry Threshold) × Nat
  | [],acc,work => (acc.reverse,work+2*acc.length+1)
  | e::es,acc,work =>
    let ok:=check t cap e.value
    validateLoop t cap es (if ok.1 then e::acc else acc) (work+ok.2+4)

theorem validateLoop_mem (t : MaskedOrdered.Tree h) (cap : Nat)
    (es acc : List (Entry Threshold)) (work : Nat) (e : Entry Threshold) :
    e∈(validateLoop t cap es acc work).1 ↔ e∈acc ∨ e∈es ∧ (check t cap e.value).1=true := by
  induction es generalizing acc work with
  | nil => simp [validateLoop]
  | cons x es ih =>
    rw [validateLoop,ih]
    by_cases hx : (check t cap x.value).1=true
    · simp only [hx,ite_true,List.mem_cons]
      constructor
      · rintro ((he|ha)|⟨he,hc⟩)
        · subst e; exact Or.inr ⟨Or.inl rfl,hx⟩
        · exact Or.inl ha
        · exact Or.inr ⟨Or.inr he,hc⟩
      · rintro (ha|⟨he,hc⟩)
        · exact Or.inl (Or.inr ha)
        · rcases he with he|he
          · exact Or.inl (Or.inl he)
          · exact Or.inr ⟨he,hc⟩
    · simp only [hx,ite_false,List.mem_cons]
      constructor
      · rintro (ha|⟨he,hc⟩)
        · exact Or.inl ha
        · exact Or.inr ⟨Or.inr he,hc⟩
      · rintro (ha|⟨he,hc⟩)
        · exact Or.inl ha
        · rcases he with he|he
          · subst e; exact False.elim (hx hc)
          · exact Or.inr ⟨he,hc⟩

theorem validateLoop_work (t : MaskedOrdered.Tree h) (cap : Nat)
    (es acc : List (Entry Threshold)) (work : Nat) :
    (validateLoop t cap es acc work).2≤work+(11*h+15)*es.length+2*acc.length+1 ∧
      (validateLoop t cap es acc work).1.length≤es.length+acc.length := by
  induction es generalizing acc work with
  | nil => simp [validateLoop]
  | cons x es ih =>
    have ht:=ih (if (check t cap x.value).1 then x::acc else acc) (work+(check t cap x.value).2+4)
    have hw:=check_work t cap x.value
    simp only [validateLoop,List.length_cons,Nat.mul_succ]
    by_cases hx : (check t cap x.value).1=true
    · simp only [hx,ite_true,List.length_cons] at ht ⊢
      exact ⟨by omega,by omega⟩
    · simp only [hx,Bool.false_eq_true,ite_false] at ht ⊢
      exact ⟨by omega,by omega⟩

structure Ready where
  pending : Queue
  live : List (Entry Threshold)
  popped : Nat
  work : Nat
  deriving Repr

def shorten (height length : Nat) (t : MaskedOrdered.Tree h) (cap : Nat) (q : Queue) : Ready :=
  let out:=drain height length q
  let checked:=validateLoop t cap out.due [] 0
  ⟨out.rest,checked.1,out.popped,out.work+checked.2+3⟩

theorem shorten_correct (height length : Nat) (t : MaskedOrdered.Tree h) (cap : Nat)
    (q : Queue) (hg : t.Good) (hf : t.Fits 0) (hc : cap=2^h)
    (hq : Good height 0 q) (e : Entry Threshold) :
    e∈(shorten height length t cap q).live ↔
      e∈entries q ∧ length≤e.key ∧ Adjacent t.entries e.value.edge.1 e.value.edge.2 := by
  unfold shorten
  rw [validateLoop_mem]
  simp only [List.not_mem_nil,false_or]
  rw [drain_due_iff height length 0 q hq e,check_correct t cap e.value hg hf hc]
  exact and_assoc

theorem shorten_work (height length : Nat) (t : MaskedOrdered.Tree h) (cap : Nat)
    (q : Queue) (hq : Good height 0 q) :
    (shorten height length t cap q).work≤
      (10*height+11*h+31)*((shorten height length t cap q).popped+1) ∧
      (shorten height length t cap q).live.length≤(shorten height length t cap q).popped ∧
      (shorten height length t cap q).popped+count (shorten height length t cap q).pending=count q := by
  have hd:=drain_spec height length 0 q hq
  have hw:=drain_work height length 0 q hq
  have hv:=validateLoop_work t cap (drain height length q).due [] 0
  simp only [List.length_nil,Nat.zero_add,Nat.add_zero,Nat.mul_zero,hd.2.2.2.2.2] at hv
  dsimp only [shorten]
  refine ⟨?_,hv.2,hd.2.2.2.2.1⟩
  have he : 10*height+11*h+31=(10*height+12)+(11*h+15)+4 := by omega
  rw [he,Nat.add_mul,Nat.add_mul,Nat.mul_succ (11*h+15)]
  have hb:=hw.1
  have hv':=hv.1
  omega

end REWB.MaskedThresholdEvents
