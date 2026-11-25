import REWB.MaskedTraversalAggregateClipCells

/-! Source erasure at the current aggregate length. A raw stored bank may
have been created at a longer length before lazy shortening. Rebuilding
that old configuration would restore a stale leaf. This operation writes
the current length into the selected configuration before compiling and
replacing the leaf; retained anchors and immutable targets are preserved.
The source batch's own fanout ledger is kept separately in `sources`.
-/
namespace REWB.MaskedTraversalAggregate
open REWB.MaskedCluster REWB.MaskedFiniteAction
variable {α : Type} {h : Nat}

structure SourceChange (C E : DFA α) (h : Nat) where
  store : Mutable.Store.State C E
  tree : BankTree C E h
  ready : Bool
  work : Nat
  calls : Nat

def refreshCurrent (env : Clip.Env C E) (first old : Nat)
    (st : Mutable.Store.State C E) (tree : BankTree C E h) : SourceChange C E h :=
  match st.slots[first]?.join with
  | none=>⟨st,tree,false,3,0⟩
  | some entry=>
    let cfg:=withLength entry.config old
    let bank:=Clip.compiled env st cfg
    match bank.1 with
    | none=>⟨st,tree,false,bank.2+6,1⟩
    | some value=>
      let replaced:=Tree.replace tree first value
      let next:={st with
        slots:=st.slots.setIfInBounds first (some ⟨cfg,value⟩)
        repairWork:=st.repairWork+bank.2+8
        rebuilds:=st.rebuilds+1
        writes:=st.writes+1}
      ⟨next,replaced.1,true,bank.2+replaced.2+12,1⟩

def eraseCurrent (env : Clip.Env C E) (partition : MaskedClusterLeaders.State h)
    (capacity old p : Nat) (st : Mutable.Store.State C E) (tree : BankTree C E h) : SourceChange C E h :=
  let owner:=MaskedClusterDescriptor.locate partition capacity p
  let next:={st with
    sources:=MaskedMutableProgression.Batch.eraseSource p st.sources
    repairWork:=st.repairWork+owner.2+2}
  match owner.1 with
  | none=>⟨next,tree,true,owner.2+2,0⟩
  | some first=>
    let out:=refreshCurrent env first old next tree
    {out with work:=out.work+owner.2+3}

theorem refreshCurrent_sources (env : Clip.Env C E) (first old : Nat)
    (st : Mutable.Store.State C E) (tree : BankTree C E h) :
    (refreshCurrent env first old st tree).store.sources=st.sources := by
  unfold refreshCurrent
  split
  · rfl
  · dsimp only; split <;> rfl

theorem eraseCurrent_sources (env : Clip.Env C E) (partition : MaskedClusterLeaders.State h)
    (capacity old p : Nat) (st : Mutable.Store.State C E) (tree : BankTree C E h) :
    (eraseCurrent env partition capacity old p st tree).store.sources=
      MaskedMutableProgression.Batch.eraseSource p st.sources := by
  unfold eraseCurrent
  dsimp only
  split
  · rfl
  · exact refreshCurrent_sources env _ old _ tree

theorem refreshCurrent_good (env : Clip.Env C E) (first old : Nat)
    (st : Mutable.Store.State C E) (tree : BankTree C E h) (hg : tree.Good) :
    (refreshCurrent env first old st tree).tree.Good := by
  unfold refreshCurrent
  split
  · exact hg
  · dsimp only
    split
    · exact hg
    · exact Tree.replace_good tree hg first _

theorem eraseCurrent_good (env : Clip.Env C E) (partition : MaskedClusterLeaders.State h)
    (capacity old p : Nat) (st : Mutable.Store.State C E) (tree : BankTree C E h) (hg : tree.Good) :
    (eraseCurrent env partition capacity old p st tree).tree.Good := by
  unfold eraseCurrent
  dsimp only
  split
  · exact hg
  · exact refreshCurrent_good env _ old _ tree hg

theorem refreshCurrent_calls (env : Clip.Env C E) (first old : Nat)
    (st : Mutable.Store.State C E) (tree : BankTree C E h) :
    (refreshCurrent env first old st tree).calls≤1 := by
  unfold refreshCurrent
  split
  · exact Nat.zero_le 1
  · dsimp only; split <;> exact Nat.le_refl 1

theorem eraseCurrent_calls (env : Clip.Env C E) (partition : MaskedClusterLeaders.State h)
    (capacity old p : Nat) (st : Mutable.Store.State C E) (tree : BankTree C E h) :
    (eraseCurrent env partition capacity old p st tree).calls≤1 := by
  unfold eraseCurrent
  dsimp only
  split
  · exact Nat.zero_le 1
  · exact refreshCurrent_calls env _ old _ tree

theorem refreshCurrent_selected (env : Clip.Env C E) (first old : Nat)
    (st : Mutable.Store.State C E) (tree : BankTree C E h)
    (ok : (refreshCurrent env first old st tree).ready=true) :
    ∃before bank,st.slots[first]?.join=some before ∧
      (Clip.compiled env st (withLength before.config old)).1=some bank ∧
      (refreshCurrent env first old st tree).store.slots[first]?.join=some ⟨withLength before.config old,bank⟩ ∧
      (refreshCurrent env first old st tree).tree.leaves=tree.leaves.set first bank.view := by
  cases hs : st.slots[first]?.join with
  | none => simp only [refreshCurrent,hs] at ok; cases ok
  | some before =>
    cases hb : (Clip.compiled env st (withLength before.config old)).1 with
    | none => simp only [refreshCurrent,hs,hb] at ok; cases ok
    | some bank =>
      have hbound : first<st.slots.size := by
        by_cases hh : first<st.slots.size
        · exact hh
        · have hn:=Array.getElem?_eq_none (xs:=st.slots) (i:=first) (by omega)
          simp only [hn,Option.join,Option.bind] at hs
          cases hs
      refine ⟨before,bank,rfl,hb,?_,?_⟩
      · simp only [refreshCurrent,hs,hb]
        rw [Array.getElem?_setIfInBounds_self_of_lt hbound]
        rfl
      · simp only [refreshCurrent,hs,hb,Tree.replace_leaves]

def selectedCurrentWork (env : Clip.Env C E) (first old : Nat) (st : Mutable.Store.State C E) : Nat :=
  match st.slots[first]?.join with
  | none=>0
  | some entry=>(Clip.compiled env st (withLength entry.config old)).2

theorem refreshCurrent_work (env : Clip.Env C E) (first old : Nat)
    (st : Mutable.Store.State C E) (tree : BankTree C E h) :
    (refreshCurrent env first old st tree).work≤selectedCurrentWork env first old st+
      (h+1)*Tree.replaceBudget (2*ReplayMaps.count C.stateCount E.stateCount)
        (2*(MaskedClusterStage.dfa C E).stateCount)+12 := by
  cases hs : st.slots[first]?.join with
  | none => simp only [refreshCurrent,selectedCurrentWork,hs]; omega
  | some entry =>
    cases hb : (Clip.compiled env st (withLength entry.config old)).1 with
    | none => simp only [refreshCurrent,selectedCurrentWork,hs,hb]; omega
    | some bank =>
      have hw:=Tree.replace_steps tree first bank
      simp only [refreshCurrent,selectedCurrentWork,hs,hb]
      omega

end REWB.MaskedTraversalAggregate
