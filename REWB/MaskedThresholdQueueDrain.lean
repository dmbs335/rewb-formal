import REWB.MaskedThresholdQueuePop

/-! Actual threshold draining. A persistent maximum extraction stops
as soon as its key is below the current length. The unneeded extracted
version is discarded on that stopping branch; the retained queue is
unchanged. The loop is tail-recursive, and every extracted record is
charged once. No cancellation or cluster-repair callback is hidden here.
-/
namespace REWB.MaskedThresholdQueue
variable {α : Type}

structure Drained (α : Type) where
  rest : Tree α
  due : List (Entry α)
  popped : Nat
  work : Nat
  deriving Repr

def drainLoop (h threshold : Nat) : Nat → Tree α → List (Entry α) → Nat → Nat → Drained α
  | 0,t,acc,popped,work => ⟨t,acc,popped,work+1⟩
  | fuel+1,t,acc,popped,work =>
    let found:=takeMax h t
    match found.item with
    | none => ⟨t,acc,popped,work+found.work+2⟩
    | some x =>
      if threshold≤x.key then
        drainLoop h threshold fuel found.rest (x::acc) (popped+1) (work+found.work+5)
      else ⟨t,acc,popped,work+found.work+3⟩

theorem drainLoop_spec (h threshold fuel lo : Nat) (t : Tree α) (acc : List (Entry α))
    (popped work : Nat) (hg : Good h lo t) (hf : count t≤fuel)
    (ha : ∀x,x∈acc → threshold≤x.key) :
    let out:=drainLoop h threshold fuel t acc popped work
    Good h lo out.rest ∧
      (out.due++entries out.rest).Perm (acc++entries t) ∧
      (∀x,x∈out.due → threshold≤x.key) ∧
      (∀x,x∈entries out.rest → x.key<threshold) ∧
      out.popped+count out.rest=popped+count t ∧ popped≤out.popped := by
  induction fuel generalizing t acc popped work with
  | zero =>
    have he:=empty_of_count h lo t hg (by omega)
    refine ⟨hg,List.Perm.refl _,ha,?_,rfl,Nat.le_refl _⟩
    intro x hx
    change x∈entries t at hx
    rw [he] at hx
    cases hx
  | succ fuel ih =>
    have ht:=takeMax_spec h lo t hg
    cases he : (takeMax h t).item with
    | none =>
      have hm:=ht.2.1
      simp only [Removal,he] at hm
      simp only [drainLoop,he]
      refine ⟨hg,List.Perm.refl _,ha,?_,by trivial,Nat.le_refl _⟩
      intro x hx
      rw [hm.1] at hx
      cases hx
    | some x =>
      have hm:=ht.2.1
      simp only [Removal,he] at hm
      by_cases hd : threshold≤x.key
      · have hacc : ∀y,y∈x::acc → threshold≤y.key := by
          intro y hy
          rcases List.mem_cons.mp hy with hy|hy
          · subst y; exact hd
          · exact ha y hy
        have hh:=ih (takeMax h t).rest (x::acc) (popped+1) (work+(takeMax h t).work+5)
          ht.1 (by have hc:=hm.2.1; omega) hacc
        simp only [drainLoop,he,if_pos hd]
        refine ⟨hh.1,?_,hh.2.2.1,hh.2.2.2.1,?_,?_⟩
        · have hp : ((x::acc)++entries (takeMax h t).rest).Perm (acc++entries t) := by
            change (x::(acc++entries (takeMax h t).rest)).Perm _
            exact List.perm_middle.symm.trans (hm.1.append_left acc)
          exact hh.2.1.trans hp
        · have hcount:=hh.2.2.2.2.1
          have hremove:=hm.2.1
          omega
        · have hcount:=hh.2.2.2.2.2
          omega
      · simp only [drainLoop,he,if_neg hd]
        refine ⟨hg,List.Perm.refl _,ha,?_,by trivial,Nat.le_refl _⟩
        intro y hy
        have hb:=hm.2.2 y hy
        omega

def popBudget (h : Nat) : Nat := 10*h+11

/-- Output-sensitive cost: even a stopped/empty search is charged. The
initial accounting invariant lets the tail-recursive loop retain the
same base allowance through every successful extraction. -/
theorem drainLoop_work (h threshold fuel lo : Nat) (t : Tree α) (acc : List (Entry α))
    (popped work base : Nat) (hg : Good h lo t) (hb : work≤base+popBudget h*popped) :
    let out:=drainLoop h threshold fuel t acc popped work
    out.work≤base+popBudget h*(out.popped+1) := by
  induction fuel generalizing t acc popped work with
  | zero =>
    dsimp only [drainLoop]
    rw [Nat.mul_succ]
    unfold popBudget at *
    omega
  | succ fuel ih =>
    have ht:=takeMax_spec h lo t hg
    cases he : (takeMax h t).item with
    | none =>
      simp only [drainLoop,he]
      rw [Nat.mul_succ]
      have hw:=ht.2.2
      unfold popBudget at *
      omega
    | some x =>
      by_cases hd : threshold≤x.key
      · simp only [drainLoop,he,if_pos hd]
        apply ih _ _ _ _ ht.1
        have hw:=ht.2.2
        rw [Nat.mul_succ]
        unfold popBudget at *
        omega
      · simp only [drainLoop,he,if_neg hd]
        rw [Nat.mul_succ]
        have hw:=ht.2.2
        unfold popBudget at *
        omega

def drain (h threshold : Nat) (t : Tree α) : Drained α :=
  let out:=drainLoop h threshold (count t) t [] 0 0
  {out with due:=out.due.reverse,work:=out.work+out.popped+1}

theorem drain_spec (h threshold lo : Nat) (t : Tree α) (hg : Good h lo t) :
    Good h lo (drain h threshold t).rest ∧
      ((drain h threshold t).due++entries (drain h threshold t).rest).Perm (entries t) ∧
      (∀x,x∈(drain h threshold t).due → threshold≤x.key) ∧
      (∀x,x∈entries (drain h threshold t).rest → x.key<threshold) ∧
      (drain h threshold t).popped+count (drain h threshold t).rest=count t ∧
      (drain h threshold t).due.length=(drain h threshold t).popped := by
  let out:=drainLoop h threshold (count t) t [] 0 0
  have hh:=drainLoop_spec h threshold (count t) lo t [] 0 0 hg (Nat.le_refl _) (by simp)
  change Good h lo out.rest ∧ (out.due++entries out.rest).Perm ([]++entries t) ∧ _ at hh
  simp only [List.nil_append,Nat.zero_add] at hh
  have hl:=hh.2.1.length_eq
  rw [List.length_append,←good_count h lo out.rest hh.1,←good_count h lo t hg] at hl
  have hc:=hh.2.2.2.2.1
  change out.popped+count out.rest=count t at hc
  dsimp only [drain]
  refine ⟨hh.1,?_,?_,hh.2.2.2.1,hc,?_⟩
  · exact ((List.reverse_perm out.due).append_right (entries out.rest)).trans hh.2.1
  · intro x hx
    exact hh.2.2.1 x (List.mem_reverse.mp hx)
  · rw [List.length_reverse]
    change out.due.length=out.popped
    omega

theorem drain_due_iff (h threshold lo : Nat) (t : Tree α) (hg : Good h lo t) (x : Entry α) :
    x∈(drain h threshold t).due ↔ x∈entries t ∧ threshold≤x.key := by
  have hs:=drain_spec h threshold lo t hg
  constructor
  · intro hx
    exact ⟨hs.2.1.mem_iff.mp (List.mem_append.mpr (Or.inl hx)),hs.2.2.1 x hx⟩
  · rintro ⟨hx,hkey⟩
    have hm:=List.mem_append.mp (hs.2.1.mem_iff.mpr hx)
    rcases hm with hm|hm
    · exact hm
    · have he:=hs.2.2.2.1 x hm
      omega

theorem drain_pending_iff (h threshold lo : Nat) (t : Tree α) (hg : Good h lo t) (x : Entry α) :
    x∈entries (drain h threshold t).rest ↔ x∈entries t ∧ x.key<threshold := by
  have hs:=drain_spec h threshold lo t hg
  constructor
  · intro hx
    exact ⟨hs.2.1.mem_iff.mp (List.mem_append.mpr (Or.inr hx)),hs.2.2.2.1 x hx⟩
  · rintro ⟨hx,hkey⟩
    have hm:=List.mem_append.mp (hs.2.1.mem_iff.mpr hx)
    rcases hm with hm|hm
    · have he:=hs.2.2.1 x hm
      omega
    · exact hm

theorem drain_work (h threshold lo : Nat) (t : Tree α) (hg : Good h lo t) :
    (drain h threshold t).work≤(10*h+12)*((drain h threshold t).popped+1) ∧
      (drain h threshold t).popped≤count t := by
  have hw:=drainLoop_work h threshold (count t) lo t [] 0 0 0 hg (by simp)
  have hc:=(drain_spec h threshold lo t hg).2.2.2.2.1
  dsimp only [drain]
  dsimp only at hw
  dsimp only [drain] at hc
  simp only [Nat.zero_add] at hw
  constructor
  · have he : (10*h+12)=(popBudget h)+1 := by unfold popBudget; omega
    rw [he,Nat.add_mul,Nat.one_mul]
    omega
  · omega

end REWB.MaskedThresholdQueue
