import REWB.MaskedTraversalRepairCoherenceReset

/-! Indexed proof model for the two actual sparse aggregate replacements.
All length/get lemmas describe `refreshEntries`; no production operation
enumerates the complete position domain or an occurrence cluster.
-/
namespace REWB.MaskedTraversalRepairCoherence
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedTraversalAggregate
open REWB.MaskedTraversalBankReady REWB.MaskedTraversalContext REWB.MaskedClusterDescriptor
variable {α : Type} {C E : DFA α} {h n h' : Nat}

theorem refreshEntries_length (st : Mutable.Store.State C E) (ps : List Nat)
    (entries : List (Option (Mutable.Store.Entry C E))) :
    (Cells.refreshEntries st ps entries).length=entries.length := by
  induction ps generalizing entries with
  | nil => rfl
  | cons p ps ih =>
    rw [Cells.refreshEntries,List.foldl_cons]
    simpa only [List.length_set] using ih (entries.set p (st.slots[p]?.join))

theorem refreshEntries_get (st : Mutable.Store.State C E) (ps : List Nat)
    (entries : List (Option (Mutable.Store.Entry C E))) (first : Nat) (hb : first<entries.length) :
    (Cells.refreshEntries st ps entries)[first]?=
      if first∈ps then some (st.slots[first]?.join) else entries[first]? := by
  induction ps generalizing entries with
  | nil => simp [Cells.refreshEntries]
  | cons p ps ih =>
    change (Cells.refreshEntries st ps (entries.set p (st.slots[p]?.join)))[first]?=_
    rw [ih _ (by simpa only [List.length_set] using hb)]
    by_cases ht : first∈ps
    · simp only [ht,if_true,List.mem_cons,or_true]
    · simp only [ht,if_false,List.mem_cons,or_false]
      by_cases he : p=first
      · subst p
        simp only [if_pos rfl,if_true,List.getElem?_set_self hb]
      · simp only [Ne.symm he,if_false,List.getElem?_set_ne he]

theorem model_length (env : Env C E n h') (partition : MaskedClusterLeaders.State h) (capacity L : Nat)
    (anchors : Array (Option Nat)) (dirty : MaskedTraversalDirty.Marked h)
    (st : Mutable.Store.State C E) (tree : BankTree C E h) (entries : List (Option (Mutable.Store.Entry C E))) :
    (model env partition capacity L anchors dirty st tree entries).length=entries.length := by
  simp only [model,refreshEntries_length]

theorem model_get (env : Env C E n h') (partition : MaskedClusterLeaders.State h) (capacity L : Nat)
    (anchors : Array (Option Nat)) (dirty : MaskedTraversalDirty.Marked h)
    (st : Mutable.Store.State C E) (tree : BankTree C E h) (entries : List (Option (Mutable.Store.Entry C E)))
    (first : Nat) (hb : first<entries.length) :
    (model env partition capacity L anchors dirty st tree entries)[first]?=
      if first∈dirty.keys.positions ∨ first∈(contextKeys partition capacity dirty).keys.positions then
        some ((apply env partition capacity L anchors dirty st tree).store.slots[first]?.join)
      else entries[first]? := by
  unfold model
  rw [refreshEntries_get _ _ _ first (by rw [refreshEntries_length]; exact hb),refreshEntries_get _ _ _ first hb]
  change (if first∈(contextKeys partition capacity dirty).keys.positions then _ else if first∈dirty.keys.positions then _ else _)=_
  by_cases hp : first∈dirty.keys.positions <;>
    by_cases hq : first∈(contextKeys partition capacity dirty).keys.positions <;> simp only [hp,hq,if_true,if_false,true_or,or_true,false_or]

theorem contextKeys_member (partition : MaskedClusterLeaders.State h) (capacity L first : Nat)
    (dirty : MaskedTraversalDirty.Marked h) (hi : MaskedClusterLeaders.Invariant L partition) (hc : capacity=2^h)
    (hp : first∈(contextKeys partition capacity dirty).keys.positions) : first∈partition.leaders.entries := by
  have hs:=successors_spec partition.leaders capacity dirty.keys.positions (MaskedTraversalDirty.empty h)
    hi.leadGood hi.leadFits hc (MaskedOrdered.State.empty_valid h)
  have hh:=(hs.2.1 first).mp (hs.1.2.2.mem_iff.mp hp)
  rcases hh with ⟨p,_,_,hn⟩|hm
  · have hq:=MaskedOrdered.Tree.succ_correct partition.leaders capacity p hi.leadGood hi.leadFits hc
    rw [hn] at hq
    exact hq.1
  · have hn:=(MaskedOrdered.State.empty_valid h).2.2.mem_iff.mpr hm
    cases hn

theorem contextKeys_valid (partition : MaskedClusterLeaders.State h) (capacity L : Nat)
    (dirty : MaskedTraversalDirty.Marked h) (hi : MaskedClusterLeaders.Invariant L partition) (hc : capacity=2^h) :
    (contextKeys partition capacity dirty).keys.Valid :=
  (successors_spec partition.leaders capacity dirty.keys.positions (MaskedTraversalDirty.empty h)
    hi.leadGood hi.leadFits hc (MaskedOrdered.State.empty_valid h)).1

theorem refreshLoop_size (env : Clip.Env C E) (partition : MaskedClusterLeaders.State h) (capacity L : Nat)
    (anchors : Array (Option Nat)) (ps : List Nat) (st : Mutable.Store.State C E) :
    (refreshLoop env partition capacity L anchors ps st).slots.size=st.slots.size := by
  induction ps generalizing st with
  | nil => rfl
  | cons p ps ih =>
    change (refreshLoop env partition capacity L anchors ps
      {refreshBank env partition capacity L p anchors st with
        repairWork:=(refreshBank env partition capacity L p anchors st).repairWork+3}).slots.size=_
    rw [ih]
    exact Array.size_setIfInBounds

theorem resetBanks_size (env : Env C E n h') (partition : MaskedClusterLeaders.State h) (capacity L : Nat)
    (anchors : Array (Option Nat)) (dirty : MaskedTraversalDirty.Marked h) (st : Mutable.Store.State C E) :
    (resetBanks env partition capacity L anchors dirty st).store.slots.size=st.slots.size :=
  MaskedTraversalRepair.banksLoop_size C E env.shared.book env.shared.prepared env.shared.cRanges env.shared.eRanges
    partition capacity L _ env.window env.catalog env.classes env.shared.target dirty.keys.positions st

theorem apply_size (env : Env C E n h') (partition : MaskedClusterLeaders.State h) (capacity L : Nat)
    (anchors : Array (Option Nat)) (dirty : MaskedTraversalDirty.Marked h) (st : Mutable.Store.State C E)
    (tree : BankTree C E h) : (apply env partition capacity L anchors dirty st tree).store.slots.size=st.slots.size :=
  (refreshLoop_size env.shared partition capacity L _ _ _).trans (resetBanks_size env partition capacity L anchors dirty st)

theorem apply_other (env : Env C E n h') (partition : MaskedClusterLeaders.State h) (capacity L first : Nat)
    (anchors : Array (Option Nat)) (dirty : MaskedTraversalDirty.Marked h) (st : Mutable.Store.State C E)
    (tree : BankTree C E h) (hp : first∉dirty.keys.positions)
    (hq : first∉(contextKeys partition capacity dirty).keys.positions) :
    (apply env partition capacity L anchors dirty st tree).store.slots[first]?=st.slots[first]? :=
  (refreshLoop_other env.shared partition capacity L first _ _ _ hq).trans
    (resetBanks_other env partition capacity L first anchors dirty st hp)

theorem slot_bound (st : Mutable.Store.State C E) (first : Nat) (entry : Mutable.Store.Entry C E)
    (hs : st.slots[first]?.join=some entry) : first<st.slots.size := by
  by_cases hb : first<st.slots.size
  · exact hb
  · have hn:=Array.getElem?_eq_none (xs:=st.slots) (i:=first) (by omega)
    simp only [hn,Option.join,Option.bind] at hs
    cases hs

theorem entry_transfer (env : Clip.Env C E) (before after : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity L first : Nat) (entry : Mutable.Store.Entry C E)
    (he : Cells.EntryState env before partition capacity L first entry)
    (hs : after.sources=before.sources) (hp : after.slots[first]?=before.slots[first]?) :
    Cells.EntryState env after partition capacity L first entry := by
  refine ⟨he.descriptor,he.current,?_,?_⟩
  · change (Mutable.Store.compile C E env.book env.prepared env.cRanges env.eRanges after.sources env.target entry.config).1=some entry.bank
    rw [hs]
    exact he.compiled
  · obtain ⟨raw,hr,hcfg⟩:=he.raw
    exact ⟨raw,by rw [hp]; exact hr,hcfg⟩

theorem linked_unmarked (env : Env C E n h') (partition : MaskedClusterLeaders.State h) (capacity L first : Nat)
    (anchors : Array (Option Nat)) (dirty : MaskedTraversalDirty.Marked h) (st : Mutable.Store.State C E)
    (tree : BankTree C E h) (cfg : Mutable.Store.Config)
    (hi : MaskedClusterLeaders.Invariant L partition) (hc : capacity=2^h) (hm : first∈partition.leaders.entries)
    (hp : first∉dirty.keys.positions) (hq : first∉(contextKeys partition capacity dirty).keys.positions)
    (hl : Cells.Linked env.shared st partition capacity L first anchors cfg) :
    Cells.Linked env.shared (apply env partition capacity L anchors dirty st tree).store partition capacity L first
      (apply env partition capacity L anchors dirty st tree).anchors cfg := by
  have hv:=contextKeys_valid partition capacity L dirty hi hc
  have hnot : first∉(contextKeys partition capacity dirty).keys.tree.entries := fun hh=>hq (hv.2.2.mem_iff.mpr hh)
  have hin:=incoming_unchanged partition capacity L first anchors dirty.keys.positions hi hc hm hnot
  refine ⟨?_,?_,?_,?_⟩
  · change cfg.anchor=readAnchor (MaskedTraversalRepair.anchorsLoop L dirty.keys.positions anchors 0).1 first L
    rw [MaskedTraversalRepair.anchorsLoop_read,if_neg hp]
    exact hl.anchor
  · change cfg.incoming=(incoming partition capacity first L (MaskedTraversalRepair.anchorsLoop L dirty.keys.positions anchors 0).1).cursor
    rw [hin]
    exact hl.incoming
  · change cfg.incomingEnabled=(incoming partition capacity first L (MaskedTraversalRepair.anchorsLoop L dirty.keys.positions anchors 0).1).enabled
    rw [hin]
    exact hl.enabled
  · rw [apply_sources]
    exact hl.run

end REWB.MaskedTraversalRepairCoherence
