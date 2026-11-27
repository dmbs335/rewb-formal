import REWB.MaskedTraversalRepairCoherenceContext

/-! The primary reset pass obtains every dense run ID from the actual
shared catalog. Canonical-index equalities below are proof invariants of
the shared environment; the repair operation does not rebuild indexes.
The old raw-slot readiness premise is scoped to unmarked leaders only.
-/
namespace REWB.MaskedTraversalRepairCoherence
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedTraversalAggregate
open REWB.MaskedTraversalBankReady REWB.MaskedTraversalContext REWB.MaskedClusterDescriptor
variable {α : Type} {C E : DFA α} {h σ : Nat}

def RawAway (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity L : Nat) (anchors : Array (Option Nat))
    (keys : List Nat) : Prop :=
  ∀first,first∈partition.leaders.entries→first∉keys→∃entry,RawReady env st partition capacity L first anchors entry

theorem resetBanks_sources (env : Env C E n h') (partition : MaskedClusterLeaders.State h) (capacity L : Nat)
    (anchors : Array (Option Nat)) (dirty : MaskedTraversalDirty.Marked h) (st : Mutable.Store.State C E) :
    (resetBanks env partition capacity L anchors dirty st).store.sources=st.sources :=
  MaskedTraversalRepair.reset_sources C E env.shared.book env.shared.prepared env.shared.cRanges env.shared.eRanges
    partition capacity L anchors env.window env.catalog env.classes env.shared.target dirty st

theorem resetBanks_other (env : Env C E n h') (partition : MaskedClusterLeaders.State h) (capacity L first : Nat)
    (anchors : Array (Option Nat)) (dirty : MaskedTraversalDirty.Marked h) (st : Mutable.Store.State C E)
    (hp : first∉dirty.keys.positions) :
    (resetBanks env partition capacity L anchors dirty st).store.slots[first]?=st.slots[first]? :=
  MaskedTraversalRepair.reset_other C E env.shared.book env.shared.prepared env.shared.cRanges env.shared.eRanges
    partition capacity L anchors env.window env.catalog env.classes env.shared.target dirty st first hp

theorem resetBanks_compiled (env : Env C E n h') (partition : MaskedClusterLeaders.State h) (capacity L first : Nat)
    (anchors : Array (Option Nat)) (dirty : MaskedTraversalDirty.Marked h) (st : Mutable.Store.State C E)
    (hp : first∈dirty.keys.positions) (hb : first<st.slots.size) :
    (resetBanks env partition capacity L anchors dirty st).store.slots[first]?.join=
      (MaskedTraversalBankReady.compile C E env.shared.book env.shared.prepared env.shared.cRanges env.shared.eRanges
        partition capacity first L (resetBanks env partition capacity L anchors dirty st).anchors
        env.window env.catalog env.classes st.sources env.shared.target).1 := by
  unfold resetBanks MaskedTraversalRepair.reset
  rw [MaskedTraversalRepair.banksLoop_selected C E env.shared.book env.shared.prepared env.shared.cRanges env.shared.eRanges
    partition capacity L _ env.window env.catalog env.classes env.shared.target dirty.keys.positions st first hp hb]
  rfl

theorem resetBanks_selected (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool) (removed : List Nat)
    (env : Env C E text.size (MaskedSuffixClass.height text.size))
    (hcat : env.catalog=MaskedRunCatalog.ofBatch env.shared.target
      (MaskedMutableProgression.Batch.prepare text fallback source env.shared.prepared.K))
    (hclasses : env.classes=MaskedSuffixClass.prepare text fallback)
    (partition : MaskedClusterLeaders.State h) (capacity L first base : Nat)
    (anchors : Array (Option Nat)) (dirty : MaskedTraversalDirty.Marked h) (st : Mutable.Store.State C E)
    (hsrc : st.sources=MaskedMutableProgression.Batch.run text fallback source env.shared.prepared.K removed)
    (hi : MaskedClusterLeaders.Invariant L partition) (hc : capacity=2^h)
    (hfull : MaskedRunDiscovery.Complete (ArrayText.read text fallback) text.size base L partition.occurrences.entries)
    (hL : 0<L) (hp : first∈dirty.keys.positions) (hb : first<st.slots.size)
    (entry : Mutable.Store.Entry C E)
    (he : (resetBanks env partition capacity L anchors dirty st).store.slots[first]?.join=some entry) :
    GoodSlot env.shared (resetBanks env partition capacity L anchors dirty st).store partition capacity L first
      (resetBanks env partition capacity L anchors dirty st).anchors entry := by
  have hcompile := (resetBanks_compiled env partition capacity L first anchors dirty st hp hb).symm.trans he
  obtain ⟨hprep,hbank⟩:=MaskedTraversalBankReady.compile_selected C E env.shared.book env.shared.prepared env.shared.cRanges
    env.shared.eRanges partition capacity first L _ env.window env.catalog env.classes st.sources env.shared.target entry hcompile
  have hd:=prepare_descriptor partition capacity first L _ env.window env.catalog env.classes entry.config hprep
  have hanchor : readAnchor (resetBanks env partition capacity L anchors dirty st).anchors first L=L := by
    change readAnchor (MaskedTraversalRepair.anchorsLoop L dirty.keys.positions anchors 0).1 first L=L
    rw [MaskedTraversalRepair.anchorsLoop_read,if_pos hp]
  refine ⟨he,⟨hd.1,hd.2.1,?_⟩,⟨hd.2.2.1,hd.2.2.2.1,hd.2.2.2.2.1,?_⟩⟩
  · change (Mutable.Store.compile C E env.shared.book env.shared.prepared env.shared.cRanges env.shared.eRanges
      (resetBanks env partition capacity L anchors dirty st).store.sources env.shared.target entry.config).1=some entry.bank
    rw [resetBanks_sources]
    exact hbank
  · rw [resetBanks_sources,hsrc]
    apply reset_runBacked text fallback source env.shared.target env.shared.prepared.K partition capacity L first base
      _ env.window hi hc hfull hL hanchor entry.config _ removed
    simpa only [hcat,hclasses] using hprep

theorem resetBanks_present (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool) (removed : List Nat)
    (env : Env C E text.size (MaskedSuffixClass.height text.size)) (hK : 0<env.shared.prepared.K)
    (hcat : env.catalog=MaskedRunCatalog.ofBatch env.shared.target
      (MaskedMutableProgression.Batch.prepare text fallback source env.shared.prepared.K))
    (hclasses : env.classes=MaskedSuffixClass.prepare text fallback)
    (partition : MaskedClusterLeaders.State h) (capacity L first base : Nat)
    (anchors : Array (Option Nat)) (dirty : MaskedTraversalDirty.Marked h) (st : Mutable.Store.State C E)
    (hsrc : st.sources=MaskedMutableProgression.Batch.run text fallback source env.shared.prepared.K removed)
    (hi : MaskedClusterLeaders.Invariant L partition) (hc : capacity=2^h)
    (hfull : MaskedRunDiscovery.Complete (ArrayText.read text fallback) text.size base L partition.occurrences.entries)
    (hL : 0<L) (hp : first∈dirty.keys.positions) (hb : first<st.slots.size)
    (hm : first∈partition.leaders.entries) :
    ∃entry,GoodSlot env.shared (resetBanks env partition capacity L anchors dirty st).store partition capacity L first
      (resetBanks env partition capacity L anchors dirty st).anchors entry := by
  obtain ⟨d,hd,_,_⟩:=describeLeader_exists partition capacity L first hi hc hm
  have hanchor : readAnchor (resetBanks env partition capacity L anchors dirty st).anchors first L=L := by
    change readAnchor (MaskedTraversalRepair.anchorsLoop L dirty.keys.positions anchors 0).1 first L=L
    rw [MaskedTraversalRepair.anchorsLoop_read,if_pos hp]
  have hpres:=compile_reset_present C E env.shared.book env.shared.prepared hK env.shared.cRanges env.shared.eRanges
    text fallback source env.shared.target removed partition capacity L first base _ env.window hi hc d hd hfull hL hanchor
  have hslot:=resetBanks_compiled env partition capacity L first anchors dirty st hp hb
  rw [hcat,hclasses,hsrc] at hslot
  cases he : (resetBanks env partition capacity L anchors dirty st).store.slots[first]?.join with
  | none => rw [he] at hslot; rw [←hslot] at hpres; cases hpres
  | some entry => exact ⟨entry,resetBanks_selected text fallback source removed env hcat hclasses partition capacity L first base
      anchors dirty st hsrc hi hc hfull hL hp hb entry he⟩

theorem resetBanks_raw (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool) (removed : List Nat)
    (env : Env C E text.size (MaskedSuffixClass.height text.size)) (hK : 0<env.shared.prepared.K)
    (hcat : env.catalog=MaskedRunCatalog.ofBatch env.shared.target
      (MaskedMutableProgression.Batch.prepare text fallback source env.shared.prepared.K))
    (hclasses : env.classes=MaskedSuffixClass.prepare text fallback)
    (partition : MaskedClusterLeaders.State h) (capacity L base : Nat)
    (anchors : Array (Option Nat)) (dirty : MaskedTraversalDirty.Marked h) (st : Mutable.Store.State C E)
    (hsrc : st.sources=MaskedMutableProgression.Batch.run text fallback source env.shared.prepared.K removed)
    (hi : MaskedClusterLeaders.Invariant L partition) (hc : capacity=2^h)
    (hfull : MaskedRunDiscovery.Complete (ArrayText.read text fallback) text.size base L partition.occurrences.entries)
    (hL : 0<L) (hsize : text.size<st.slots.size)
    (hr : RawAway env.shared st partition capacity L anchors dirty.keys.positions) :
    RawComplete env.shared (resetBanks env partition capacity L anchors dirty st).store partition capacity L
      (resetBanks env partition capacity L anchors dirty st).anchors := by
  intro first hm
  by_cases hp : first∈dirty.keys.positions
  · have hbound:=((hfull first).mp ((hi.represented first).mp hm).1).1
    obtain ⟨entry,he⟩:=resetBanks_present text fallback source removed env hK hcat hclasses partition capacity L first base
      anchors dirty st hsrc hi hc hfull hL hp (by omega) hm
    exact ⟨entry,he.ready⟩
  · obtain ⟨entry,he⟩:=hr first hm hp
    refine ⟨entry,?_,he.descriptor,?_,?_⟩
    · rw [resetBanks_other env partition capacity L first anchors dirty st hp]
      exact he.slot
    · change entry.config.anchor=readAnchor (MaskedTraversalRepair.anchorsLoop L dirty.keys.positions anchors 0).1 first L
      rw [MaskedTraversalRepair.anchorsLoop_read,if_neg hp]
      exact he.anchor
    · rw [resetBanks_sources]
      exact he.run

end REWB.MaskedTraversalRepairCoherence
