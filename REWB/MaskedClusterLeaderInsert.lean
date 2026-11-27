import REWB.MaskedClusterLeaders

/-! Occurrence insertion updates at most two dense-component leader bits.
The same actual insertion supplies the fresh threshold records. No old
occurrence list, cluster span, or unchanged adjacency list is scanned. -/
namespace REWB.MaskedClusterLeaders
open REWB.MaskedOrdered
variable {h : Nat}

def repair (occurrences leaders : Tree h) (capacity length p : Nat)
    (after : Option Nat) : Tree h×Nat :=
  let first:=refresh occurrences leaders capacity length p
  match after with
  | none => (first.1,first.2+1)
  | some q =>
    let second:=refresh occurrences first.1 capacity length q
    (second.1,first.2+second.2+2)

theorem repair_good (occurrences leaders : Tree h) (capacity length p : Nat)
    (after : Option Nat) (hg : Tree.Good leaders) :
    Tree.Good (repair occurrences leaders capacity length p after).1 := by
  cases after with
  | none => exact refresh_good _ _ _ _ _ hg
  | some q => exact refresh_good _ _ _ _ _ (refresh_good _ _ _ _ _ hg)

theorem repair_fits (occurrences leaders : Tree h) (capacity length p : Nat)
    (after : Option Nat) (hf : Tree.Fits leaders 0) (hc : capacity=2^h) (hp : p<2^h)
    (ha : ∀ q,after=some q → q<2^h) :
    Tree.Fits (repair occurrences leaders capacity length p after).1 0 := by
  cases after with
  | none => exact refresh_fits _ _ _ _ _ hf hc hp
  | some q => exact refresh_fits _ _ _ _ _ (refresh_fits _ _ _ _ _ hf hc hp) hc (ha q rfl)

theorem repair_mem (occurrences leaders : Tree h) (capacity length p x : Nat)
    (after : Option Nat) (hg : Tree.Good occurrences) (hf : Tree.Fits occurrences 0)
    (hl : Tree.Fits leaders 0) (hc : capacity=2^h) (hp : p<2^h)
    (ha : ∀ q,after=some q → q<2^h) :
    x∈(repair occurrences leaders capacity length p after).1.entries ↔
      ((x=p ∨ after=some x) ∧ Leader occurrences.entries length x) ∨
        (x≠p ∧ after≠some x ∧ x∈leaders.entries) := by
  cases after with
  | none =>
    change x∈(refresh occurrences leaders capacity length p).1.entries ↔ _
    rw [refresh_mem _ _ _ _ _ _ hg hf hl hc hp]
    by_cases hx : x=p <;> simp [hx]
  | some q =>
    change x∈(refresh occurrences
      (refresh occurrences leaders capacity length p).1 capacity length q).1.entries ↔ _
    rw [refresh_mem _ _ _ _ _ _ hg hf (refresh_fits _ _ _ _ _ hl hc hp) hc (ha q rfl),
      refresh_mem _ _ _ _ _ _ hg hf hl hc hp]
    by_cases hx : x=p <;> by_cases hy : x=q <;> simp_all [eq_comm]

theorem repair_work (occurrences leaders : Tree h) (capacity length p : Nat)
    (after : Option Nat) : (repair occurrences leaders capacity length p after).2≤46*h+32 := by
  have hh:=refresh_work occurrences leaders capacity length p
  cases after with
  | none => simp only [repair]; omega
  | some q =>
    have ht:=refresh_work occurrences (refresh occurrences leaders capacity length p).1 capacity length q
    simp only [repair]
    omega

structure State (h : Nat) where
  occurrences : Tree h
  leaders : Tree h
  queue : MaskedThresholdEvents.Queue
  deriving Repr

structure Invariant (length : Nat) (s : State h) : Prop where
  occGood : s.occurrences.Good
  occFits : s.occurrences.Fits 0
  leadGood : s.leaders.Good
  leadFits : s.leaders.Fits 0
  represented : Represents s.occurrences s.leaders length
  queueGood : MaskedThresholdQueue.Good (h+1) 0 s.queue

structure Added (h : Nat) where
  state : State h
  generated : Nat
  work : Nat
  deriving Repr

def add (capacity length p : Nat) (s : State h) : Added h :=
  let after:=Tree.succ s.occurrences capacity p
  let inserted:=MaskedThresholdEvents.add h capacity p s.occurrences s.queue
  let fixed:=repair inserted.insertion.tree s.leaders capacity length p after.1
  ⟨⟨inserted.insertion.tree,fixed.1,inserted.queue⟩,inserted.generated,
    after.2+inserted.work+fixed.2+4⟩

theorem add_invariant (capacity length p : Nat) (s : State h)
    (hi : Invariant length s) (hc : capacity=2^h) (hp : p<capacity) :
    Invariant length (add capacity length p s).state := by
  have hpow : p<2^h := by omega
  have hgood:=MaskedOrdered.insert_good s.occurrences capacity p hi.occGood
  have hfit:=MaskedOrdered.insert_fits s.occurrences capacity p hi.occFits hc hpow
  have hs:=Tree.succ_correct s.occurrences capacity p hi.occGood hi.occFits hc
  have ha : ∀ q,(Tree.succ s.occurrences capacity p).1=some q → q<2^h := by
    intro q hq
    rw [hq] at hs
    have hqmem:=hs.1
    have hb:=Tree.within s.occurrences 0 hi.occFits q hqmem
    omega
  have hqueue:=MaskedThresholdEvents.add_spec h capacity p s.occurrences s.queue
    hi.occGood hi.occFits hc hp hi.queueGood
  refine ⟨hgood,hfit,repair_good _ _ _ _ _ _ hi.leadGood,
    repair_fits _ _ _ _ _ _ hi.leadFits hc hpow ha,?_,hqueue.1⟩
  intro x
  change x∈(repair (MaskedOrdered.insert s.occurrences capacity p).tree s.leaders
    capacity length p (Tree.succ s.occurrences capacity p).1).1.entries ↔ _
  rw [repair_mem _ _ _ _ _ _ _ hgood hfit hi.leadFits hc hpow ha]
  constructor
  · rintro (⟨_,hleader⟩|⟨hxp,hxa,hm⟩)
    · exact hleader
    · exact (insert_away s.occurrences.entries (MaskedOrdered.insert s.occurrences capacity p).tree.entries
        length p x _ (fun q=>MaskedOrdered.insert_mem s.occurrences capacity p q hi.occFits hc hpow)
        hs hxp hxa).mpr ((hi.represented x).mp hm)
  · intro hleader
    by_cases hx : x=p ∨ (Tree.succ s.occurrences capacity p).1=some x
    · exact Or.inl ⟨hx,hleader⟩
    · have hxp : x≠p := fun he=>hx (Or.inl he)
      have hxa : (Tree.succ s.occurrences capacity p).1≠some x := fun he=>hx (Or.inr he)
      exact Or.inr ⟨hxp,hxa,(hi.represented x).mpr
        ((insert_away s.occurrences.entries (MaskedOrdered.insert s.occurrences capacity p).tree.entries
          length p x _ (fun q=>MaskedOrdered.insert_mem s.occurrences capacity p q hi.occFits hc hpow)
          hs hxp hxa).mp hleader)⟩

theorem add_work (capacity length p : Nat) (s : State h)
    (hi : Invariant length s) (hc : capacity=2^h) (hp : p<capacity) :
    (add capacity length p s).work≤129*h+149 ∧ (add capacity length p s).generated≤4 := by
  have ha:=Tree.succ_work s.occurrences capacity p
  have hb:=MaskedThresholdEvents.add_spec h capacity p s.occurrences s.queue
    hi.occGood hi.occFits hc hp hi.queueGood
  have hr:=repair_work (MaskedOrdered.insert s.occurrences capacity p).tree s.leaders
    capacity length p (Tree.succ s.occurrences capacity p).1
  change (repair (MaskedThresholdEvents.add h capacity p s.occurrences s.queue).insertion.tree s.leaders
    capacity length p (Tree.succ s.occurrences capacity p).1).2≤46*h+32 at hr
  simp only [add]
  change _≤_ ∧ (MaskedThresholdEvents.add h capacity p s.occurrences s.queue).generated≤4
  exact ⟨by omega,hb.2.2.2.1⟩

end REWB.MaskedClusterLeaders
