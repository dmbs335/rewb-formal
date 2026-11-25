import REWB.MaskedClusterLeaderFuture

/-! Actual threshold consumption repairs exactly the dense-component
leaders at a shorter length. This is independent of source/target masks
and does not yet repair local anchors or cached transfer banks. -/
namespace REWB.MaskedClusterLeaders
open REWB.MaskedOrdered REWB.MaskedEventBudget
variable {h : Nat}

abbrev Record := MaskedThresholdQueue.Entry Threshold

def Targets (es : List Record) (p : Nat) : Prop :=
  ∃ e,e∈es ∧ e.value.edge.2=p

theorem targets_cons (e : Record) (es : List Record) (p : Nat) :
    Targets (e::es) p ↔ e.value.edge.2=p ∨ Targets es p := by
  simp [Targets]

def repairLive (occurrences : Tree h) (capacity length : Nat) :
    List Record→Tree h→Nat→Tree h×Nat
  | [],leaders,work => (leaders,work)
  | e::es,leaders,work =>
    let next:=refresh occurrences leaders capacity length e.value.edge.2
    repairLive occurrences capacity length es next.1 (work+next.2+3)

theorem repairLive_good (occurrences leaders : Tree h) (capacity length work : Nat)
    (es : List Record) (hg : leaders.Good) :
    (repairLive occurrences capacity length es leaders work).1.Good := by
  induction es generalizing leaders work with
  | nil => exact hg
  | cons e es ih => rw [repairLive]; exact ih _ _ (refresh_good _ _ _ _ _ hg)

theorem repairLive_fits (occurrences leaders : Tree h) (capacity length work : Nat)
    (es : List Record) (hf : leaders.Fits 0) (hc : capacity=2^h)
    (hb : ∀ e,e∈es → e.value.edge.2<2^h) :
    (repairLive occurrences capacity length es leaders work).1.Fits 0 := by
  induction es generalizing leaders work with
  | nil => exact hf
  | cons e es ih =>
    rw [repairLive]
    exact ih _ _ (refresh_fits _ _ _ _ _ hf hc (hb e List.mem_cons_self))
      (fun a ha=>hb a (List.mem_cons_of_mem e ha))

theorem repairLive_mem (occurrences leaders : Tree h) (capacity length work x : Nat)
    (es : List Record) (hg : occurrences.Good) (hf : occurrences.Fits 0)
    (hl : leaders.Fits 0) (hc : capacity=2^h) (hb : ∀ e,e∈es → e.value.edge.2<2^h) :
    x∈(repairLive occurrences capacity length es leaders work).1.entries ↔
      (Targets es x ∧ Leader occurrences.entries length x) ∨
        (¬Targets es x ∧ x∈leaders.entries) := by
  induction es generalizing leaders work with
  | nil => simp [repairLive,Targets]
  | cons e es ih =>
    rw [repairLive,ih _ _ (refresh_fits _ _ _ _ _ hl hc (hb e List.mem_cons_self))
      (fun a ha=>hb a (List.mem_cons_of_mem e ha)),
      refresh_mem _ _ _ _ _ _ hg hf hl hc (hb e List.mem_cons_self),targets_cons]
    by_cases he : x=e.value.edge.2 <;> by_cases ht : Targets es x <;> simp_all [eq_comm]

theorem repairLive_work (occurrences leaders : Tree h) (capacity length work : Nat)
    (es : List Record) :
    (repairLive occurrences capacity length es leaders work).2≤work+(23*h+18)*es.length := by
  induction es generalizing leaders work with
  | nil => simp [repairLive]
  | cons e es ih =>
    have hr:=refresh_work occurrences leaders capacity length e.value.edge.2
    have ht:=ih (refresh occurrences leaders capacity length e.value.edge.2).1
      (work+(refresh occurrences leaders capacity length e.value.edge.2).2+3)
    simp only [repairLive,List.length_cons,Nat.mul_succ]
    omega

structure Shortened (h : Nat) where
  state : State h
  live : List Record
  popped : Nat
  work : Nat
  deriving Repr

def shorten (capacity fresh : Nat) (s : State h) : Shortened h :=
  let ready:=MaskedThresholdEvents.shorten (h+1) fresh s.occurrences capacity s.queue
  let fixed:=repairLive s.occurrences capacity fresh ready.live s.leaders 0
  ⟨⟨s.occurrences,fixed.1,ready.pending⟩,ready.live,ready.popped,ready.work+fixed.2+4⟩

theorem shorten_invariant (capacity old fresh : Nat) (s : State h)
    (hi : Invariant old s) (hf : Future old s) (hc : capacity=2^h) (hle : fresh≤old) :
    Invariant fresh (shorten capacity fresh s).state := by
  have hb:=live_bound capacity old fresh s hi hc
  have hq:=MaskedThresholdQueue.drain_spec (h+1) fresh 0 s.queue hi.queueGood
  refine ⟨hi.occGood,hi.occFits,repairLive_good _ _ _ _ _ _ hi.leadGood,
    repairLive_fits _ _ _ _ _ _ hi.leadFits hc hb,?_,hq.1⟩
  intro x
  change x∈(repairLive s.occurrences capacity fresh
    (MaskedThresholdEvents.shorten (h+1) fresh s.occurrences capacity s.queue).live s.leaders 0).1.entries ↔ _
  rw [repairLive_mem _ _ _ _ _ _ _ hi.occGood hi.occFits hi.leadFits hc hb]
  constructor
  · rintro (⟨_,hl⟩|⟨_,hm⟩)
    · exact hl
    · exact leader_shorten _ old fresh x hle ((hi.represented x).mp hm)
  · intro hl
    classical
    by_cases ht : Targets (MaskedThresholdEvents.shorten (h+1) fresh s.occurrences capacity s.queue).live x
    · exact Or.inl ⟨ht,hl⟩
    · refine Or.inr ⟨ht,(hi.represented x).mpr ?_⟩
      by_cases hold : Leader s.occurrences.entries old x
      · exact hold
      · obtain ⟨e,he,hex,_⟩:=changed_leader_record capacity old fresh x s hi hf hc hl hold
        exact False.elim (ht ⟨e,he,hex⟩)

theorem shorten_future (capacity old fresh : Nat) (s : State h)
    (hi : Invariant old s) (hf : Future old s) (hle : fresh≤old) :
    Future fresh (shorten capacity fresh s).state := by
  intro edge he event hev hlevel
  have hold:=hf edge he event hev (by omega)
  apply (MaskedThresholdQueue.drain_pending_iff (h+1) fresh 0 s.queue hi.queueGood
    (MaskedThresholdEvents.pack event)).mpr
  exact ⟨hold,hlevel⟩

theorem shorten_work (capacity old fresh : Nat) (s : State h) (hi : Invariant old s) :
    (shorten capacity fresh s).work≤(44*h+63)*((shorten capacity fresh s).popped+1) ∧
    (shorten capacity fresh s).popped+
      MaskedThresholdQueue.count (shorten capacity fresh s).state.queue=
        MaskedThresholdQueue.count s.queue := by
  have hq:=MaskedThresholdEvents.shorten_work (h+1) fresh s.occurrences capacity s.queue hi.queueGood
  have hr:=repairLive_work s.occurrences s.leaders capacity fresh 0
    (MaskedThresholdEvents.shorten (h+1) fresh s.occurrences capacity s.queue).live
  have hm:=Nat.mul_le_mul_left (23*h+18) hq.2.1
  simp only [shorten]
  refine ⟨?_,hq.2.2⟩
  simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.one_mul,Nat.zero_add,Nat.mul_assoc] at hq hr hm ⊢
  omega

end REWB.MaskedClusterLeaders
