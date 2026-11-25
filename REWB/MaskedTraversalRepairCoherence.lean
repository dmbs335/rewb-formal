import REWB.MaskedTraversalAggregateMeaning
import REWB.MaskedTraversalContextCost

/-! One actual complete-band repair operation: reset all selected anchors,
compile primary banks, refresh the current successors while retaining
their own anchors, then replace exactly those sparse aggregate leaves.
The active leaf list used by the proofs is not built at runtime.
-/
namespace REWB.MaskedTraversalRepairCoherence
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedTraversalAggregate
variable {α : Type} {C E : DFA α} {h h' n : Nat}

structure Env (C E : DFA α) (n h' : Nat) where
  shared : Clip.Env C E
  window : SourceWindow
  catalog : MaskedRunCatalog.Index
  classes : MaskedSuffixClass.Index n h'

def resetBanks (env : Env C E n h') (partition : MaskedClusterLeaders.State h) (capacity L : Nat)
    (anchors : Array (Option Nat)) (dirty : MaskedTraversalDirty.Marked h)
    (st : Mutable.Store.State C E) : MaskedTraversalRepair.Reset C E :=
  MaskedTraversalRepair.reset C E env.shared.book env.shared.prepared env.shared.cRanges env.shared.eRanges
    partition capacity L anchors env.window env.catalog env.classes env.shared.target dirty st

def contextKeys (partition : MaskedClusterLeaders.State h) (capacity : Nat)
    (dirty : MaskedTraversalDirty.Marked h) : MaskedTraversalDirty.Marked h :=
  MaskedTraversalContext.successors partition.leaders capacity dirty.keys.positions (MaskedTraversalDirty.empty h)

def contextBanks (env : Env C E n h') (partition : MaskedClusterLeaders.State h) (capacity L : Nat)
    (anchors : Array (Option Nat)) (keys : List Nat) (st : Mutable.Store.State C E) : Mutable.Store.State C E :=
  MaskedTraversalContext.applyLoop C E env.shared.book env.shared.prepared env.shared.cRanges env.shared.eRanges
    partition capacity L anchors env.shared.target keys st

structure Result (C E : DFA α) (h : Nat) where
  anchors : Array (Option Nat)
  store : Mutable.Store.State C E
  tree : BankTree C E h
  contexts : MaskedTraversalDirty.Marked h
  work : Nat

def apply (env : Env C E n h') (partition : MaskedClusterLeaders.State h) (capacity L : Nat)
    (anchors : Array (Option Nat)) (dirty : MaskedTraversalDirty.Marked h)
    (st : Mutable.Store.State C E) (tree : BankTree C E h) : Result C E h :=
  let reset:=resetBanks env partition capacity L anchors dirty st
  let contexts:=contextKeys partition capacity dirty
  let priorWork:=reset.store.repairWork
  let done:=contextBanks env partition capacity L reset.anchors contexts.keys.positions reset.store
  let first:=refreshMany done dirty.keys.positions tree
  let second:=refreshMany done contexts.keys.positions first.1
  ⟨reset.anchors,done,second.1,contexts,
    reset.work+contexts.work+(done.repairWork-priorWork)+first.2+second.2+7⟩

theorem apply_sources (env : Env C E n h') (partition : MaskedClusterLeaders.State h) (capacity L : Nat)
    (anchors : Array (Option Nat)) (dirty : MaskedTraversalDirty.Marked h)
    (st : Mutable.Store.State C E) (tree : BankTree C E h) :
    (apply env partition capacity L anchors dirty st tree).store.sources=st.sources := by
  unfold apply contextBanks
  rw [MaskedTraversalContext.applyLoop_sources]
  exact MaskedTraversalRepair.reset_sources C E env.shared.book env.shared.prepared env.shared.cRanges env.shared.eRanges
    partition capacity L anchors env.window env.catalog env.classes env.shared.target dirty st

theorem apply_good (env : Env C E n h') (partition : MaskedClusterLeaders.State h) (capacity L : Nat)
    (anchors : Array (Option Nat)) (dirty : MaskedTraversalDirty.Marked h)
    (st : Mutable.Store.State C E) (tree : BankTree C E h) (hg : tree.Good) :
    (apply env partition capacity L anchors dirty st tree).tree.Good :=
  refreshMany_good _ _ _ (refreshMany_good _ _ _ hg)

def model (env : Env C E n h') (partition : MaskedClusterLeaders.State h) (capacity L : Nat)
    (anchors : Array (Option Nat)) (dirty : MaskedTraversalDirty.Marked h)
    (st : Mutable.Store.State C E) (tree : BankTree C E h)
    (entries : List (Option (Mutable.Store.Entry C E))) : List (Option (Mutable.Store.Entry C E)) :=
  let out:=apply env partition capacity L anchors dirty st tree
  Cells.refreshEntries out.store out.contexts.keys.positions
    (Cells.refreshEntries out.store dirty.keys.positions entries)

theorem apply_represents (env : Env C E n h') (partition : MaskedClusterLeaders.State h) (capacity L : Nat)
    (anchors : Array (Option Nat)) (dirty : MaskedTraversalDirty.Marked h)
    (st : Mutable.Store.State C E) (tree : BankTree C E h)
    (entries : List (Option (Mutable.Store.Entry C E))) (hr : Cells.Represents tree entries) :
    Cells.Represents (apply env partition capacity L anchors dirty st tree).tree
      (model env partition capacity L anchors dirty st tree entries) :=
  Cells.refreshMany_represents _ _ _ _ (Cells.refreshMany_represents _ _ _ _ hr)

end REWB.MaskedTraversalRepairCoherence
