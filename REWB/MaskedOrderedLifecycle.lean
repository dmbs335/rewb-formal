import REWB.MaskedOrderedSchedule

/-! Event provenance and retirement for the actual persistent schedule.
The lists in the specifications below are not evaluated by the schedule.
Every light-child adjacency is retired once at its right endpoint, and
any newly live adjacency has an emitted fresh-generation record. -/
namespace REWB.MaskedOrdered
open REWB.MaskedEventBudget (Edge edges MergeTree size leaves lightVolume)
variable {h : Nat}

theorem pred_first (t : Tree h) (cap a : Nat) (xs : List Nat)
    (hg : t.Good) (hf : t.Fits 0) (hc : cap=2^h) (he : t.entries=a::xs) :
    (Tree.pred t cap a).1=none := by
  apply pred_unique t.entries a _ none (Tree.pred_correct t cap a hg hf hc)
  intro r hr
  have hs:=Tree.ordered t 0 hf
  rw [he] at hs hr
  rcases List.mem_cons.mp hr with he|hr
  · omega
  · have hh:=(List.pairwise_cons.mp hs).1 r hr
    omega

theorem pred_adjacent (t : Tree h) (cap a b : Nat) (pre post : List Nat)
    (hg : t.Good) (hf : t.Fits 0) (hc : cap=2^h)
    (he : t.entries=pre++a::b::post) : (Tree.pred t cap b).1=some a := by
  have hs:=Tree.ordered t 0 hf
  rw [he] at hs
  have hp:=List.pairwise_append.mp hs
  have hab:=(List.pairwise_cons.mp hp.2.1).1 b (by simp)
  apply pred_unique t.entries b _ (some a) (Tree.pred_correct t cap b hg hf hc)
  refine ⟨?_,hab,?_⟩
  · rw [he]
    exact List.mem_append_right _ (by simp)
  · intro r hr hrb
    rw [he,List.mem_append] at hr
    rcases hr with hr|hr
    · have hh:=hp.2.2 r hr a (by simp)
      omega
    · rcases List.mem_cons.mp hr with he|hr
      · omega
      · rcases List.mem_cons.mp hr with he|hr
        · omega
        · have hh:=(List.pairwise_cons.mp (List.pairwise_cons.mp hp.2.1).2).1 r hr
          omega

def discardedAll (t : Tree h) (cap : Nat) (ps : List Nat) : List Edge :=
  ps.flatMap (fun p=>discarded p (Tree.pred t cap p).1)

theorem discarded_tail (t : Tree h) (cap : Nat) (xs : List Nat)
    (hg : t.Good) (hf : t.Fits 0) (hc : cap=2^h) :
    ∀pre a,t.entries=pre++a::xs → discardedAll t cap xs=edges (a::xs) := by
  induction xs with
  | nil => intro pre a he; rfl
  | cons b bs ih =>
    intro pre a he
    have hp:=pred_adjacent t cap a b pre bs hg hf hc he
    have hh:=ih (pre++[a]) b (by simpa only [List.append_assoc,List.singleton_append] using he)
    simp only [discardedAll,List.flatMap_cons,hp,discarded,List.singleton_append,edges]
    exact congrArg (List.cons (a,b)) hh

theorem discarded_entries (t : Tree h) (cap : Nat) (hg : t.Good) (hf : t.Fits 0)
    (hc : cap=2^h) : discardedAll t cap t.entries=edges t.entries := by
  cases he : t.entries with
  | nil => rfl
  | cons a xs =>
    have hp:=pred_first t cap a xs hg hf hc he
    have hh:=discarded_tail t cap xs hg hf hc [] a he
    simp only [discardedAll,List.flatMap_cons,hp,discarded,List.nil_append]
    exact hh

theorem discarded_positions (s : State h) (cap : Nat) (hs : s.Valid) (hc : cap=2^h) :
    (discardedAll s.tree cap s.positions).Perm (edges s.tree.entries) := by
  have hp:=hs.2.2.flatMap_right (fun p=>discarded p (Tree.pred s.tree cap p).1)
  change (discardedAll s.tree cap s.positions).Perm (discardedAll s.tree cap s.tree.entries) at hp
  rw [discarded_entries s.tree cap hs.1 hs.2.1 hc] at hp
  exact hp

theorem insert_balance (t : Tree h) (cap p : Nat) (hg : t.Good) (hf : t.Fits 0)
    (hc : cap=2^h) (hp : p<2^h) :
    (insert t cap p).fresh.length+(edges t.entries).length=
      (edges (insert t cap p).tree.entries).length+(insert t cap p).retired.length := by
  obtain ⟨pre,post,hn,ho⟩:=insert_edge_repair t cap p hg hf hc hp
  have hnl:=congrArg List.length hn
  have hol:=congrArg List.length ho
  simp only [List.length_append] at hnl hol
  omega

theorem importLoop_balance (light : Tree h) (cap : Nat) (ps : List Nat)
    (dst : State h) (ledger : Ledger) (hd : dst.Valid) (hc : cap=2^h)
    (hb : ∀p,p∈ps→p<2^h) :
    (importLoop light cap ps dst ledger).2.freshCount+(edges dst.tree.entries).length+
      ledger.retiredCount+(discardedAll light cap ps).length=
    (edges (importLoop light cap ps dst ledger).1.tree.entries).length+
      (importLoop light cap ps dst ledger).2.retiredCount+ledger.freshCount := by
  induction ps generalizing dst ledger with
  | nil => simp [importLoop,discardedAll,Nat.add_comm,Nat.add_left_comm]
  | cons p ps ih =>
    have hp:=hb p (by simp)
    have hs:=insert_balance dst.tree cap p hd.1 hd.2.1 hc hp
    have hr:=ih (importOne light cap p dst ledger).1 (importOne light cap p dst ledger).2
      (importOne_valid _ _ _ _ _ hd hc hp) (fun q hq=>hb q (by simp [hq]))
    simp only [importOne,add] at hr
    simp only [importLoop,discardedAll,List.flatMap_cons,List.length_append]
    change _+(edges dst.tree.entries).length+ledger.retiredCount+
      ((discarded p (Tree.pred light cap p).1).length+
        (discardedAll light cap ps).length)=_
    dsimp only [importOne,add]
    omega

theorem merge_balance (cap : Nat) (a b : State h) (ledger : Ledger)
    (ha : a.Valid) (hb : b.Valid) (hc : cap=2^h) :
    (merge cap a b ledger).2.freshCount+(edges a.tree.entries).length+
      (edges b.tree.entries).length+ledger.retiredCount=
    (edges (merge cap a b ledger).1.tree.entries).length+
      (merge cap a b ledger).2.retiredCount+ledger.freshCount := by
  simp only [merge]
  split
  · have hh:=importLoop_balance a.tree cap a.positions b {ledger with work:=ledger.work+1}
      hb hc (State.bounded a ha)
    rw [(discarded_positions a cap ha hc).length_eq] at hh
    dsimp only at hh
    omega
  · have hh:=importLoop_balance b.tree cap b.positions a {ledger with work:=ledger.work+1}
      ha hc (State.bounded b hb)
    rw [(discarded_positions b cap hb hc).length_eq] at hh
    dsimp only at hh
    omega

theorem execute_balance (cap : Nat) (t : MergeTree) (ledger : Ledger)
    (hc : cap=2^h) (hb : Bounded h t) :
    (execute (h:=h) cap t ledger).2.freshCount+ledger.retiredCount=
    (edges (execute (h:=h) cap t ledger).1.tree.entries).length+
      (execute (h:=h) cap t ledger).2.retiredCount+ledger.freshCount := by
  induction t generalizing ledger with
  | leaf p =>
    have hh:=insert_reference (State.empty h).tree cap p True.intro
      (State.empty_valid h).2.1 hc (hb p (by simp [leaves])) (by simp [State.empty,Tree.entries])
    change ledger.freshCount+ledger.retiredCount=
      (edges (insert (State.empty h).tree cap p).tree.entries).length+
      ledger.retiredCount+ledger.freshCount
    rw [hh.1]
    simp [State.empty,Tree.entries,MaskedEventBudget.insert,edges,Nat.add_comm]
  | node a b ia ib =>
    have ha:=bounded_left a b hb
    have hb':=bounded_right a b hb
    have hwa:=ia ledger ha
    have hwb:=ib (execute (h:=h) cap a ledger).2 hb'
    have hwm:=merge_balance cap (execute (h:=h) cap a ledger).1
      (execute (h:=h) cap b (execute (h:=h) cap a ledger).2).1
      (execute (h:=h) cap b (execute (h:=h) cap a ledger).2).2
      (execute_valid _ _ _ hc ha) (execute_valid _ _ _ hc hb') hc
    simp only [execute]
    omega

theorem run_balance (h : Nat) (t : MergeTree) (hb : Bounded h t) :
    (run h t).2.fresh.length=(edges (run h t).1.tree.entries).length+
      (run h t).2.retired.length := by
  have hh:=execute_balance (capacity h).1 t {work:=(capacity h).2} (capacity_value h) hb
  have hg:=run_ledger h t
  have hf:=hg.1
  have hr:=hg.2
  change (run h t).2.freshCount+0=(edges (run h t).1.tree.entries).length+
    (run h t).2.retiredCount+0 at hh
  omega

theorem insert_live_edge (t : Tree h) (cap p : Nat) (hg : t.Good) (hf : t.Fits 0)
    (hc : cap=2^h) (hp : p<2^h) (e : Edge)
    (he : e∈edges (insert t cap p).tree.entries) :
    e∈edges t.entries ∨ e∈(insert t cap p).fresh := by
  obtain ⟨pre,post,hn,ho⟩:=insert_edge_repair t cap p hg hf hc hp
  rw [hn] at he
  rcases List.mem_append.mp he with he|he
  · rcases List.mem_append.mp he with he|he
    · exact Or.inl (by rw [ho]; simp [he])
    · exact Or.inr he
  · exact Or.inl (by rw [ho]; simp [he])

theorem importLoop_fresh_mono (light : Tree h) (cap : Nat) (ps : List Nat)
    (dst : State h) (ledger : Ledger) (e : Edge) (he : e∈ledger.fresh) :
    e∈(importLoop light cap ps dst ledger).2.fresh := by
  induction ps generalizing dst ledger with
  | nil => exact he
  | cons p ps ih =>
    apply ih
    exact List.mem_append_right _ he

theorem importLoop_live_edge (light : Tree h) (cap : Nat) (ps : List Nat)
    (dst : State h) (ledger : Ledger) (hd : dst.Valid) (hc : cap=2^h)
    (hb : ∀p,p∈ps→p<2^h) (e : Edge)
    (he : e∈edges (importLoop light cap ps dst ledger).1.tree.entries) :
    e∈edges dst.tree.entries ∨ e∈(importLoop light cap ps dst ledger).2.fresh := by
  induction ps generalizing dst ledger with
  | nil => exact Or.inl he
  | cons p ps ih =>
    have hp:=hb p (by simp)
    have hh:=ih (importOne light cap p dst ledger).1 (importOne light cap p dst ledger).2
      (importOne_valid _ _ _ _ _ hd hc hp) (fun q hq=>hb q (by simp [hq])) he
    rcases hh with hh|hh
    · rcases insert_live_edge dst.tree cap p hd.1 hd.2.1 hc hp e hh with hh|hh
      · exact Or.inl hh
      · exact Or.inr (importLoop_fresh_mono light cap ps _ _ e (List.mem_append_left _ hh))
    · exact Or.inr hh

theorem merge_new_edge (cap : Nat) (a b : State h) (ledger : Ledger)
    (ha : a.Valid) (hb : b.Valid) (hc : cap=2^h) (e : Edge)
    (he : e∈edges (merge cap a b ledger).1.tree.entries)
    (hea : e∉edges a.tree.entries) (heb : e∉edges b.tree.entries) :
    e∈(merge cap a b ledger).2.fresh := by
  by_cases hab : a.tree.count≤b.tree.count
  · simp only [merge,hab,if_true] at he ⊢
    exact (importLoop_live_edge _ _ _ _ _ hb hc (State.bounded a ha) e he).resolve_left heb
  · simp only [merge,hab,if_false] at he ⊢
    exact (importLoop_live_edge _ _ _ _ _ ha hc (State.bounded b hb) e he).resolve_left hea

end REWB.MaskedOrdered
