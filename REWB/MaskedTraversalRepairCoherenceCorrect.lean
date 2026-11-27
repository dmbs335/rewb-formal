import REWB.MaskedTraversalRepairCoherenceModel

/-! Complete-band repair preserves the actual active-frontier model.
`Setup` records constructed shared indexes, current source history and
the complete occurrence class. `Pending` scopes the input invariant to
unmarked cells; dirty descriptors/cursors are allowed to be stale.

The pending set itself is produced by the separate actual add/merge/live
threshold collectors. Their descriptor/anchor/incoming transport theorems
provide these scoped premises. This file does not assert the remaining
whole-Driver induction or reporting/amortization theorem.
-/
namespace REWB.MaskedTraversalRepairCoherence
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedTraversalAggregate
open REWB.MaskedTraversalBankReady REWB.MaskedTraversalContext REWB.MaskedClusterDescriptor
variable {α : Type} {C E : DFA α} {h σ n h' : Nat}

structure Setup (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool) (removed : List Nat)
    (env : Env C E text.size (MaskedSuffixClass.height text.size))
    (partition : MaskedClusterLeaders.State h) (capacity L base : Nat) (st : Mutable.Store.State C E) : Prop where
  modulus_pos : 0<env.shared.prepared.K
  catalog : env.catalog=MaskedRunCatalog.ofBatch env.shared.target
    (MaskedMutableProgression.Batch.prepare text fallback source env.shared.prepared.K)
  classes : env.classes=MaskedSuffixClass.prepare text fallback
  sources : st.sources=MaskedMutableProgression.Batch.run text fallback source env.shared.prepared.K removed
  invariant : MaskedClusterLeaders.Invariant L partition
  capacity_eq : capacity=2^h
  complete : MaskedRunDiscovery.Complete (ArrayText.read text fallback) text.size base L partition.occurrences.entries
  positive : 0<L
  slot_size : text.size<st.slots.size

theorem Setup.valid {text : Array (Fin σ)} {fallback : Fin σ} {source : Array Bool} {removed : List Nat}
    {env : Env C E text.size (MaskedSuffixClass.height text.size)}
    {partition : MaskedClusterLeaders.State h} {capacity L base : Nat} {st : Mutable.Store.State C E}
    (hs : Setup text fallback source removed env partition capacity L base st) :
    MaskedMutableProgression.Batch.Valid source removed st.sources := by
  rw [hs.sources]
  exact MaskedMutableProgression.Batch.run_valid text fallback source env.shared.prepared.K hs.modulus_pos removed

theorem Setup.modulus {text : Array (Fin σ)} {fallback : Fin σ} {source : Array Bool} {removed : List Nat}
    {env : Env C E text.size (MaskedSuffixClass.height text.size)}
    {partition : MaskedClusterLeaders.State h} {capacity L base : Nat} {st : Mutable.Store.State C E}
    (hs : Setup text fallback source removed env partition capacity L base st) :
    st.sources.modulus=env.shared.prepared.K := by
  rw [hs.sources]
  exact MaskedMutableProgression.Batch.eraseMany_modulus removed _

structure Pending (env : Env C E n h') (partition : MaskedClusterLeaders.State h) (capacity L : Nat)
    (anchors : Array (Option Nat)) (dirty : MaskedTraversalDirty.Marked h) (st : Mutable.Store.State C E)
    (entries : List (Option (Mutable.Store.Entry C E))) : Prop where
  raw : RawAway env.shared st partition capacity L anchors dirty.keys.positions
  coherent : ∀first,first∉dirty.keys.positions→∀entry,entries[first]?=some (some entry)→
    Cells.EntryState env.shared st partition capacity L first entry
  complete : ∀first,first∈partition.leaders.entries→first∉dirty.keys.positions→
    ∃entry,entries[first]?=some (some entry)
  linked : ∀first,first∉dirty.keys.positions→first∉(contextKeys partition capacity dirty).keys.positions→
    ∀entry,entries[first]?=some (some entry)→Cells.Linked env.shared st partition capacity L first anchors entry.config

theorem setup_reset_raw (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool) (removed : List Nat)
    (env : Env C E text.size (MaskedSuffixClass.height text.size))
    (partition : MaskedClusterLeaders.State h) (capacity L base : Nat) (st : Mutable.Store.State C E)
    (hs : Setup text fallback source removed env partition capacity L base st)
    (anchors : Array (Option Nat)) (dirty : MaskedTraversalDirty.Marked h)
    (hr : RawAway env.shared st partition capacity L anchors dirty.keys.positions) :
    RawComplete env.shared (resetBanks env partition capacity L anchors dirty st).store partition capacity L
      (resetBanks env partition capacity L anchors dirty st).anchors :=
  resetBanks_raw text fallback source removed env hs.modulus_pos hs.catalog hs.classes partition capacity L base
    anchors dirty st hs.sources hs.invariant hs.capacity_eq hs.complete hs.positive hs.slot_size hr

theorem apply_raw (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool) (removed : List Nat)
    (env : Env C E text.size (MaskedSuffixClass.height text.size))
    (partition : MaskedClusterLeaders.State h) (capacity L base : Nat) (st : Mutable.Store.State C E)
    (hs : Setup text fallback source removed env partition capacity L base st)
    (anchors : Array (Option Nat)) (dirty : MaskedTraversalDirty.Marked h) (tree : BankTree C E h)
    (hr : RawAway env.shared st partition capacity L anchors dirty.keys.positions) :
    RawComplete env.shared (apply env partition capacity L anchors dirty st tree).store partition capacity L
      (apply env partition capacity L anchors dirty st tree).anchors := by
  apply refreshLoop_raw env.shared partition capacity L _ _ _
    (setup_reset_raw text fallback source removed env partition capacity L base st hs anchors dirty hr) source removed
  · rw [resetBanks_sources]
    exact hs.valid
  · rw [resetBanks_sources]
    exact hs.modulus

theorem apply_selected (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool) (removed : List Nat)
    (env : Env C E text.size (MaskedSuffixClass.height text.size))
    (partition : MaskedClusterLeaders.State h) (capacity L base first : Nat) (st : Mutable.Store.State C E)
    (hs : Setup text fallback source removed env partition capacity L base st)
    (anchors : Array (Option Nat)) (dirty : MaskedTraversalDirty.Marked h) (tree : BankTree C E h)
    (hr : RawAway env.shared st partition capacity L anchors dirty.keys.positions)
    (hp : first∈dirty.keys.positions ∨ first∈(contextKeys partition capacity dirty).keys.positions)
    (entry : Mutable.Store.Entry C E)
    (he : (apply env partition capacity L anchors dirty st tree).store.slots[first]?.join=some entry) :
    GoodSlot env.shared (apply env partition capacity L anchors dirty st tree).store partition capacity L first
      (apply env partition capacity L anchors dirty st tree).anchors entry := by
  by_cases hq : first∈(contextKeys partition capacity dirty).keys.positions
  · have hready:=setup_reset_raw text fallback source removed env partition capacity L base st hs anchors dirty hr
    have hv : MaskedMutableProgression.Batch.Valid source removed (resetBanks env partition capacity L anchors dirty st).store.sources := by
      rw [resetBanks_sources]; exact hs.valid
    have hK : (resetBanks env partition capacity L anchors dirty st).store.sources.modulus=env.shared.prepared.K := by
      rw [resetBanks_sources]; exact hs.modulus
    obtain ⟨value,hvalue⟩:=refreshLoop_selected env.shared partition capacity L first _ _ _ hready source removed hv hK hq
      (contextKeys_member partition capacity L first dirty hs.invariant hs.capacity_eq hq)
    have hsame : value=entry := Option.some.inj (hvalue.slot.symm.trans he)
    subst value
    exact hvalue
  · have hprimary:=hp.resolve_right hq
    have hslot:=refreshLoop_other env.shared partition capacity L first
      (resetBanks env partition capacity L anchors dirty st).anchors
      (contextKeys partition capacity dirty).keys.positions (resetBanks env partition capacity L anchors dirty st).store hq
    have hbefore : (resetBanks env partition capacity L anchors dirty st).store.slots[first]?.join=some entry := by
      change (refreshLoop env.shared partition capacity L (resetBanks env partition capacity L anchors dirty st).anchors
        (contextKeys partition capacity dirty).keys.positions (resetBanks env partition capacity L anchors dirty st).store).slots[first]?.join=some entry at he
      simpa only [hslot] using he
    have hb:=slot_bound _ first entry hbefore
    rw [resetBanks_size] at hb
    have hgood:=resetBanks_selected text fallback source removed env hs.catalog hs.classes partition capacity L first base
      anchors dirty st hs.sources hs.invariant hs.capacity_eq hs.complete hs.positive hprimary hb entry hbefore
    exact hgood.transfer (refreshLoop_sources env.shared partition capacity L _ _ _) hslot

theorem apply_present (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool) (removed : List Nat)
    (env : Env C E text.size (MaskedSuffixClass.height text.size))
    (partition : MaskedClusterLeaders.State h) (capacity L base first : Nat) (st : Mutable.Store.State C E)
    (hs : Setup text fallback source removed env partition capacity L base st)
    (anchors : Array (Option Nat)) (dirty : MaskedTraversalDirty.Marked h) (tree : BankTree C E h)
    (hr : RawAway env.shared st partition capacity L anchors dirty.keys.positions)
    (hp : first∈dirty.keys.positions ∨ first∈(contextKeys partition capacity dirty).keys.positions)
    (hm : first∈partition.leaders.entries) :
    ∃entry,GoodSlot env.shared (apply env partition capacity L anchors dirty st tree).store partition capacity L first
      (apply env partition capacity L anchors dirty st tree).anchors entry := by
  by_cases hq : first∈(contextKeys partition capacity dirty).keys.positions
  · apply refreshLoop_selected env.shared partition capacity L first _ _ _
      (setup_reset_raw text fallback source removed env partition capacity L base st hs anchors dirty hr) source removed _ _ hq hm
    · rw [resetBanks_sources]; exact hs.valid
    · rw [resetBanks_sources]; exact hs.modulus
  · have hprimary:=hp.resolve_right hq
    have hb:=((hs.complete first).mp ((hs.invariant.represented first).mp hm).1).1
    have hn:=hs.slot_size
    obtain ⟨entry,hentry⟩:=resetBanks_present text fallback source removed env hs.modulus_pos hs.catalog hs.classes
      partition capacity L first base anchors dirty st hs.sources hs.invariant hs.capacity_eq hs.complete hs.positive hprimary (by omega) hm
    exact ⟨entry,hentry.transfer (refreshLoop_sources env.shared partition capacity L _ _ _)
      (refreshLoop_other env.shared partition capacity L first _ _ _ hq)⟩

theorem apply_coherent (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool) (removed : List Nat)
    (env : Env C E text.size (MaskedSuffixClass.height text.size))
    (partition : MaskedClusterLeaders.State h) (capacity L base : Nat) (st : Mutable.Store.State C E)
    (hs : Setup text fallback source removed env partition capacity L base st)
    (anchors : Array (Option Nat)) (dirty : MaskedTraversalDirty.Marked h) (tree : BankTree C E h)
    (entries : List (Option (Mutable.Store.Entry C E))) (hp : Pending env partition capacity L anchors dirty st entries) :
    Cells.Coherent env.shared (apply env partition capacity L anchors dirty st tree).store partition capacity L
      (model env partition capacity L anchors dirty st tree entries) := by
  intro first entry he
  have hb:=(List.getElem?_eq_some_iff.mp he).1
  rw [model_length] at hb
  rw [model_get env partition capacity L anchors dirty st tree entries first hb] at he
  by_cases hsel : first∈dirty.keys.positions ∨ first∈(contextKeys partition capacity dirty).keys.positions
  · simp only [if_pos hsel,Option.some.injEq] at he
    exact (apply_selected text fallback source removed env partition capacity L base first st hs anchors dirty tree hp.raw hsel entry he).coherent
  · simp only [if_neg hsel] at he
    have hn := not_or.mp hsel
    exact entry_transfer env.shared st _ partition capacity L first entry (hp.coherent first hn.1 entry he)
      (apply_sources env partition capacity L anchors dirty st tree)
      (apply_other env partition capacity L first anchors dirty st tree hn.1 hn.2)

theorem apply_linked (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool) (removed : List Nat)
    (env : Env C E text.size (MaskedSuffixClass.height text.size))
    (partition : MaskedClusterLeaders.State h) (capacity L base : Nat) (st : Mutable.Store.State C E)
    (hs : Setup text fallback source removed env partition capacity L base st)
    (anchors : Array (Option Nat)) (dirty : MaskedTraversalDirty.Marked h) (tree : BankTree C E h)
    (entries : List (Option (Mutable.Store.Entry C E))) (hp : Pending env partition capacity L anchors dirty st entries) :
    Cells.LinkedEntries env.shared (apply env partition capacity L anchors dirty st tree).store partition capacity L
      (apply env partition capacity L anchors dirty st tree).anchors
      (model env partition capacity L anchors dirty st tree entries) := by
  intro first entry he
  have hb:=(List.getElem?_eq_some_iff.mp he).1
  rw [model_length] at hb
  rw [model_get env partition capacity L anchors dirty st tree entries first hb] at he
  by_cases hsel : first∈dirty.keys.positions ∨ first∈(contextKeys partition capacity dirty).keys.positions
  · simp only [if_pos hsel,Option.some.injEq] at he
    exact (apply_selected text fallback source removed env partition capacity L base first st hs anchors dirty tree hp.raw hsel entry he).linked
  · simp only [if_neg hsel] at he
    have hn := not_or.mp hsel
    have hdesc:=(hp.coherent first hn.1 entry he).descriptor
    have hd:=describeLeader_sound partition capacity L first hs.invariant hs.capacity_eq entry.config.descriptor hdesc
    have hm : first∈partition.leaders.entries := by simpa only [hd.1] using hd.2.firstLeader
    exact linked_unmarked env partition capacity L first anchors dirty st tree entry.config hs.invariant hs.capacity_eq hm
      hn.1 hn.2 (hp.linked first hn.1 hn.2 entry he)

theorem apply_complete (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool) (removed : List Nat)
    (env : Env C E text.size (MaskedSuffixClass.height text.size))
    (partition : MaskedClusterLeaders.State h) (capacity L base : Nat) (st : Mutable.Store.State C E)
    (hs : Setup text fallback source removed env partition capacity L base st)
    (anchors : Array (Option Nat)) (dirty : MaskedTraversalDirty.Marked h) (tree : BankTree C E h)
    (entries : List (Option (Mutable.Store.Entry C E))) (hp : Pending env partition capacity L anchors dirty st entries)
    (hl : entries.length=2^h) :
    Cells.CompleteModel partition (model env partition capacity L anchors dirty st tree entries) := by
  intro first hm
  have hb:=MaskedOrdered.Tree.within partition.leaders 0 hs.invariant.leadFits first hm
  have hbound : first<entries.length := by rw [hl]; omega
  by_cases hsel : first∈dirty.keys.positions ∨ first∈(contextKeys partition capacity dirty).keys.positions
  · obtain ⟨entry,hentry⟩:=apply_present text fallback source removed env partition capacity L base first st hs anchors dirty tree hp.raw hsel hm
    exact ⟨entry,by rw [model_get env partition capacity L anchors dirty st tree entries first hbound,if_pos hsel,hentry.slot]⟩
  · have hn:=not_or.mp hsel
    obtain ⟨entry,hentry⟩:=hp.complete first hm hn.1
    exact ⟨entry,by rw [model_get env partition capacity L anchors dirty st tree entries first hbound,if_neg hsel]; exact hentry⟩

theorem apply_anchors (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool) (removed : List Nat)
    (env : Env C E text.size (MaskedSuffixClass.height text.size))
    (partition : MaskedClusterLeaders.State h) (capacity L base : Nat) (st : Mutable.Store.State C E)
    (hs : Setup text fallback source removed env partition capacity L base st)
    (anchors : Array (Option Nat)) (dirty : MaskedTraversalDirty.Marked h) (tree : BankTree C E h)
    (ha : MaskedTraversalRetained.Away partition capacity (ArrayText.read text fallback) text.size L anchors dirty.keys.positions)
    (hb : text.size<anchors.size) :
    MaskedTraversalRetained.Away partition capacity (ArrayText.read text fallback) text.size L
      (apply env partition capacity L anchors dirty st tree).anchors [] :=
  MaskedTraversalRetained.reset_all partition capacity text.size base L (ArrayText.read text fallback) anchors dirty.keys.positions
    hs.invariant hs.capacity_eq hs.complete hs.positive hb ha

end REWB.MaskedTraversalRepairCoherence
