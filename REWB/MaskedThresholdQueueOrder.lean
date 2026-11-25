import REWB.MaskedThresholdQueueDrain

namespace REWB.MaskedThresholdQueue
variable {α : Type}

def Descending (xs : List (Entry α)) : Prop := xs.Pairwise (fun a b=>b.key≤a.key)

theorem drainLoop_order (h threshold fuel lo : Nat) (t : Tree α) (acc : List (Entry α))
    (popped work : Nat) (hg : Good h lo t) (hs : Descending acc.reverse)
    (hb : ∀a,a∈acc → ∀b,b∈entries t → b.key≤a.key) :
    Descending (drainLoop h threshold fuel t acc popped work).due.reverse := by
  induction fuel generalizing t acc popped work with
  | zero => exact hs
  | succ fuel ih =>
    have ht:=takeMax_spec h lo t hg
    cases he : (takeMax h t).item with
    | none => simpa only [drainLoop,he] using hs
    | some x =>
      have hm:=ht.2.1
      simp only [Removal,he] at hm
      by_cases hd : threshold≤x.key
      · have hx : x∈entries t := hm.1.mem_iff.mp List.mem_cons_self
        have hsorted : Descending (x::acc).reverse := by
          simp only [List.reverse_cons]
          apply List.pairwise_append.mpr
          refine ⟨hs,by simp,?_⟩
          intro a ha b hb'
          have heq:=List.mem_singleton.mp hb'
          subst b
          exact hb a (List.mem_reverse.mp ha) x hx
        have hbound : ∀a,a∈x::acc → ∀b,b∈entries (takeMax h t).rest → b.key≤a.key := by
          intro a ha b hb'
          have hbefore:=hm.1.mem_iff.mp (List.mem_cons_of_mem x hb')
          rcases List.mem_cons.mp ha with heq|ha
          · subst a
            exact hm.2.2 b hbefore
          · exact hb a ha b hbefore
        simpa only [drainLoop,he,if_pos hd] using
          ih (takeMax h t).rest (x::acc) (popped+1) (work+(takeMax h t).work+5)
            ht.1 hsorted hbound
      · simpa only [drainLoop,he,if_neg hd] using hs

/-- Events are returned in descending threshold order, including ties.
This permits processing compressed-edge intervals before their lower
endpoint merge, rather than losing intervening lengths. -/
theorem drain_order (h threshold lo : Nat) (t : Tree α) (hg : Good h lo t) :
    Descending (drain h threshold t).due :=
  drainLoop_order h threshold (count t) lo t [] 0 0 hg (by simp [Descending]) (by simp)

theorem drain_twice_bound (h a b lo : Nat) (t : Tree α) (hg : Good h lo t) :
    (drain h a t).popped+(drain h b (drain h a t).rest).popped≤count t := by
  have ha:=drain_spec h a lo t hg
  have hb:=drain_spec h b lo (drain h a t).rest ha.1
  have hca:=ha.2.2.2.2.1
  have hcb:=hb.2.2.2.2.1
  omega

/-- A consumed record cannot reappear in any later drain unless a
caller explicitly inserts another record. No distinct-key premise is
needed: threshold partitioning also handles duplicate-key buckets. -/
theorem drain_no_replay (h a b lo : Nat) (t : Tree α) (hg : Good h lo t) (x : Entry α)
    (hx : x∈(drain h a t).due) : x∉(drain h b (drain h a t).rest).due := by
  have ha:=drain_spec h a lo t hg
  have hkey:=ha.2.2.1 x hx
  intro hy
  have hb:=(drain_due_iff h b lo (drain h a t).rest ha.1 x).mp hy
  have hl:=ha.2.2.2.1 x hb.1
  omega

end REWB.MaskedThresholdQueue
