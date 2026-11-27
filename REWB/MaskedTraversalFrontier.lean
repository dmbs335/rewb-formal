import REWB.MaskedTraversalEdgeCost
import REWB.MaskedOrderedMerge

/-! Executable occurrence/leader/queue frontiers for bottom-up traversal.
The maintained positions list is updated only for a genuinely new key,
using two cached counts.  It is never reconstructed by scanning a tree.
Local-anchor banks are intentionally absent from this geometric layer. -/
namespace REWB.MaskedTraversalFrontier
open REWB.MaskedClusterLeaders
variable {h : Nat}

structure Frontier (h : Nat) where
  state : MaskedClusterLeaders.State h
  positions : List Nat
  deriving Repr

def Frontier.ordered (s : Frontier h) : MaskedOrdered.State h :=
  ⟨s.state.occurrences,s.positions⟩

structure Frontier.Valid (length : Nat) (s : Frontier h) : Prop where
  invariant : Invariant length s.state
  future : Future length s.state
  positions : s.positions.Perm s.state.occurrences.entries

theorem Frontier.Valid.ordered {length : Nat} {s : Frontier h} (hv : s.Valid length) :
    s.ordered.Valid := ⟨hv.invariant.occGood,hv.invariant.occFits,hv.positions⟩

theorem Frontier.Valid.count {length : Nat} {s : Frontier h} (hv : s.Valid length) :
    s.state.occurrences.count=s.positions.length :=
  MaskedOrdered.State.count_eq s.ordered hv.ordered

theorem Frontier.Valid.bounded {length : Nat} {s : Frontier h} (hv : s.Valid length)
    (p : Nat) (hp : p∈s.positions) : p<2^h :=
  MaskedOrdered.State.bounded s.ordered hv.ordered p hp

def empty (h : Nat) : Frontier h := ⟨MaskedClusterLeaders.empty h,[]⟩

theorem empty_valid (h length : Nat) : (empty h).Valid length :=
  ⟨empty_invariant h length,empty_future h length,List.Perm.refl _⟩

structure Inserted (h : Nat) where
  frontier : Frontier h
  generated : Nat
  work : Nat
  deriving Repr

def insert (capacity length p : Nat) (s : Frontier h) : Inserted h :=
  let out:=MaskedClusterLeaders.add capacity length p s.state
  let ps:=if s.state.occurrences.count<out.state.occurrences.count then p::s.positions else s.positions
  ⟨⟨out.state,ps⟩,out.generated,out.work+4⟩

theorem insert_ordered (capacity length p : Nat) (s : Frontier h)
    (hv : s.Valid length) (hc : capacity=2^h) (hp : p<capacity) :
    (insert capacity length p s).frontier.ordered=(MaskedOrdered.add s.ordered capacity p).1 := by
  have ht:=MaskedOrdered.insert_count s.state.occurrences capacity p
    hv.invariant.occGood hv.invariant.occFits hc (by omega)
  change (⟨(MaskedOrdered.insert s.state.occurrences capacity p).tree,
      if s.state.occurrences.count<(MaskedOrdered.insert s.state.occurrences capacity p).tree.count
        then p::s.positions else s.positions⟩ : MaskedOrdered.State h)=
    ⟨(MaskedOrdered.insert s.state.occurrences capacity p).tree,
      if (MaskedOrdered.insert s.state.occurrences capacity p).inserted then p::s.positions else s.positions⟩
  rw [ht]
  cases he : (MaskedOrdered.insert s.state.occurrences capacity p).inserted <;> simp

theorem insert_valid (capacity length p : Nat) (s : Frontier h)
    (hv : s.Valid length) (hc : capacity=2^h) (hp : p<capacity) :
    (insert capacity length p s).frontier.Valid length := by
  have ho:=MaskedOrdered.add_valid s.ordered capacity p hv.ordered hc (by omega)
  rw [←insert_ordered capacity length p s hv hc hp] at ho
  exact ⟨add_invariant capacity length p s.state hv.invariant hc hp,
    add_future capacity length p s.state hv.invariant hv.future hc hp,ho.2.2⟩

theorem insert_mem (capacity length p x : Nat) (s : Frontier h)
    (hv : s.Valid length) (hc : capacity=2^h) (hp : p<capacity) :
    x∈(insert capacity length p s).frontier.state.occurrences.entries ↔
      x=p ∨ x∈s.state.occurrences.entries :=
  MaskedOrdered.insert_mem s.state.occurrences capacity p x hv.invariant.occFits hc (by omega)

theorem insert_measured (capacity length p : Nat) (s : Frontier h)
    (hv : s.Valid length) (hc : capacity=2^h) (hp : p<capacity) :
    (insert capacity length p s).work≤129*h+153 ∧
    (insert capacity length p s).generated≤4 ∧
    MaskedThresholdQueue.count (insert capacity length p s).frontier.state.queue=
      MaskedThresholdQueue.count s.state.queue+(insert capacity length p s).generated := by
  have hw:=add_work capacity length p s.state hv.invariant hc hp
  have hq:=MaskedThresholdEvents.add_spec h capacity p s.state.occurrences s.state.queue
    hv.invariant.occGood hv.invariant.occFits hc hp hv.invariant.queueGood
  refine ⟨?_,hw.2,hq.2.2.1⟩
  change (MaskedClusterLeaders.add capacity length p s.state).work+4≤129*h+153
  omega

structure Lowered (h : Nat) where
  frontier : Frontier h
  edge : MaskedTraversalEdge.Scheduled h
  deriving Repr

def lower (capacity floor high : Nat) (s : Frontier h) : Lowered h :=
  let edge:=MaskedTraversalEdge.run capacity floor high s.state
  ⟨⟨edge.path.state,s.positions⟩,edge⟩

theorem lower_valid (capacity floor high : Nat) (s : Frontier h)
    (hv : s.Valid high) (hc : capacity=2^h) (hle : floor≤high) :
    (lower capacity floor high s).frontier.Valid floor := by
  by_cases hh : floor<high
  · have hs:=MaskedTraversalEdge.run_valid capacity floor high s.state hh hv.invariant hv.future hc
    refine ⟨hs.invariant,hs.future,?_⟩
    change s.positions.Perm (MaskedTraversalEdge.run capacity floor high s.state).path.state.occurrences.entries
    rw [MaskedTraversalEdge.run_occurrences]
    exact hv.positions
  · have he : high=floor := by omega
    subst high
    simpa only [lower,MaskedTraversalEdge.run_equal] using hv

theorem lower_occurrences (capacity floor high : Nat) (s : Frontier h) :
    (lower capacity floor high s).frontier.state.occurrences=s.state.occurrences :=
  MaskedTraversalEdge.run_occurrences capacity floor high s.state

theorem lower_positions (capacity floor high : Nat) (s : Frontier h) :
    (lower capacity floor high s).frontier.positions=s.positions := rfl

end REWB.MaskedTraversalFrontier
