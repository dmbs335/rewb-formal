import REWB.MaskedClusterLeaderInsert

/-! Every live adjacency retains each not-yet-crossed threshold. This is
preserved by the actual insertion and drain operations, including records
that are born already due. It supplies the missing-threshold premise for
leader repair from a concrete operation stream. -/
namespace REWB.MaskedClusterLeaders
open REWB.MaskedOrdered REWB.MaskedEventBudget
open REWB.MaskedThresholdEvents (pack)
variable {h : Nat}

def Future (length : Nat) (s : State h) : Prop :=
  ∀ edge,edge∈edges s.occurrences.entries →
    ∀ event,event∈thresholds edge → event.level<length →
      pack event∈MaskedThresholdQueue.entries s.queue

theorem inserted_edge (t : Tree h) (capacity p : Nat) (edge : Edge)
    (hg : t.Good) (hf : t.Fits 0) (hc : capacity=2^h) (hp : p<2^h)
    (he : edge∈edges (MaskedOrdered.insert t capacity p).tree.entries) :
    edge∈(MaskedOrdered.insert t capacity p).fresh ∨ edge∈edges t.entries := by
  obtain ⟨pre,post,hn,ho⟩:=MaskedOrdered.insert_edge_repair t capacity p hg hf hc hp
  rw [hn,List.mem_append,List.mem_append] at he
  rcases he with (hpre|hfresh)|hpost
  · exact Or.inr (by rw [ho]; exact List.mem_append_left _ (List.mem_append_left _ hpre))
  · exact Or.inl hfresh
  · exact Or.inr (by rw [ho]; exact List.mem_append_right _ hpost)

theorem add_future (capacity length p : Nat) (s : State h)
    (hi : Invariant length s) (hf : Future length s) (hc : capacity=2^h) (hp : p<capacity) :
    Future length (add capacity length p s).state := by
  have hqueue:=MaskedThresholdEvents.add_spec h capacity p s.occurrences s.queue
    hi.occGood hi.occFits hc hp hi.queueGood
  intro edge hedge event hevent hlevel
  have he : edge∈edges (MaskedOrdered.insert s.occurrences capacity p).tree.entries := hedge
  have hnew:=inserted_edge s.occurrences capacity p edge hi.occGood hi.occFits hc (by omega) he
  apply hqueue.2.1.mem_iff.mpr
  rcases hnew with hn|ho
  · apply List.mem_append_left
    apply List.mem_map.mpr
    refine ⟨event,?_,rfl⟩
    exact List.mem_flatMap.mpr ⟨edge,hn,hevent⟩
  · exact List.mem_append_right _ (hf edge ho event hevent hlevel)

theorem leader_shorten (xs : List Nat) (old fresh p : Nat) (hf : fresh≤old)
    (hp : Leader xs old p) : Leader xs fresh p := by
  refine ⟨hp.1,?_⟩
  intro q hq hqp
  have hh:=hp.2 q hq hqp
  omega

theorem predecessor_adjacent (xs : List Nat) (p q : Nat) (hp : p∈xs)
    (hq : Tree.PredSpec xs p (some q)) : MaskedRunDiscovery.Adjacent xs q p := by
  refine ⟨hq.1,hp,hq.2.1,?_⟩
  intro x hx hqx hxp
  have hh:=hq.2.2 x hx hxp
  omega

/-- Every newly created leader is the right endpoint of an actual live
density record returned by shortening. No occurrence scan supplies it. -/
theorem changed_leader_record (capacity old fresh p : Nat) (s : State h)
    (hi : Invariant old s) (hf : Future old s) (hc : capacity=2^h)
    (hp : Leader s.occurrences.entries fresh p) (hn : ¬Leader s.occurrences.entries old p) :
    ∃ e,e∈(MaskedThresholdEvents.shorten (h+1) fresh s.occurrences capacity s.queue).live ∧
      e.value.edge.2=p ∧ e.value.kind=.density := by
  have hpred:=Tree.pred_correct s.occurrences capacity p hi.occGood hi.occFits hc
  cases he : (Tree.pred s.occurrences capacity p).1 with
  | none =>
    rw [he] at hpred
    have hold : Leader s.occurrences.entries old p :=
      ⟨hp.1,(beforeAllows_correct _ old p none hpred).mp rfl⟩
    exact False.elim (hn hold)
  | some q =>
    rw [he] at hpred
    have hnew : fresh<2*(p-q) := hp.2 q hpred.1 hpred.2.1
    have hold : 2*(p-q)≤old := by
      by_cases hh : old<2*(p-q)
      · have hallow : beforeAllows old p (some q)=true := by simp [beforeAllows,hh]
        exact False.elim (hn ⟨hp.1,(beforeAllows_correct _ old p _ hpred).mp hallow⟩)
      · omega
    have hadj:=predecessor_adjacent _ p q hp.1 hpred
    have hedge:=MaskedRunDiscovery.adjacent_edge _ q p
      (Tree.ordered s.occurrences 0 hi.occFits) hadj
    let event : Threshold:=⟨(q,p),.density,2*(p-q)-1⟩
    have hin : event∈thresholds (q,p) := by simp [event,thresholds]
    have hlevel : event.level<old := by
      dsimp only [event]
      have hqp:=hpred.2.1
      omega
    have hqueue:=hf (q,p) hedge event hin hlevel
    refine ⟨pack event,?_,rfl,rfl⟩
    apply (MaskedThresholdEvents.shorten_correct (h+1) fresh s.occurrences capacity s.queue
      hi.occGood hi.occFits hc hi.queueGood (pack event)).mpr
    refine ⟨hqueue,?_,hadj⟩
    dsimp only [pack,event]
    omega

theorem live_bound (capacity old fresh : Nat) (s : State h)
    (hi : Invariant old s) (hc : capacity=2^h) (e : MaskedThresholdQueue.Entry Threshold)
    (he : e∈(MaskedThresholdEvents.shorten (h+1) fresh s.occurrences capacity s.queue).live) :
    e.value.edge.2<2^h := by
  have ha:=((MaskedThresholdEvents.shorten_correct (h+1) fresh s.occurrences capacity s.queue
    hi.occGood hi.occFits hc hi.queueGood e).mp he).2.2
  have hb:=Tree.within s.occurrences 0 hi.occFits _ ha.2.1
  omega

def empty (h : Nat) : State h := ⟨.empty,.empty,.empty⟩

theorem empty_invariant (h length : Nat) : Invariant length (empty h) := by
  refine ⟨True.intro,(by cases h <;> exact True.intro),True.intro,
    (by cases h <;> exact True.intro),?_,True.intro⟩
  intro p
  simp [empty,Tree.entries,Leader]

theorem empty_future (h length : Nat) : Future length (empty h) := by
  intro edge he
  simp [empty,Tree.entries,edges] at he

end REWB.MaskedClusterLeaders
