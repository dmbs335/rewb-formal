import REWB.MaskedTraversalRepairUnclipped

/-! The current source snapshot can have any actual erasure history and
ledger values. Reset preparation needs only Valid, cached n/modulus and
the unchanged original run array, not equality with an entire Batch.run
state. This is the contract preserved by actual reporting erasures.
-/
namespace REWB.MaskedTraversalRepairCoherence
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedTraversalAggregate
open REWB.MaskedTraversalBankReady REWB.MaskedTraversalContext REWB.MaskedClusterDescriptor
variable {α : Type} {C E : DFA α} {h σ : Nat}

structure Snapshot (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool) (removed : List Nat)
    (env : Env C E text.size (MaskedSuffixClass.height text.size))
    (partition : MaskedClusterLeaders.State h) (capacity L base : Nat) (st : Mutable.Store.State C E) : Prop where
  catalog : env.catalog=MaskedRunCatalog.ofBatch env.shared.target
    (MaskedMutableProgression.Batch.prepare text fallback source env.shared.prepared.K)
  classes : env.classes=MaskedSuffixClass.prepare text fallback
  valid : MaskedMutableProgression.Batch.Valid source removed st.sources
  size : st.sources.n=text.size
  modulus : st.sources.modulus=env.shared.prepared.K
  runs : st.sources.runs=(MaskedMutableProgression.Batch.prepare text fallback source env.shared.prepared.K).runs
  invariant : MaskedClusterLeaders.Invariant L partition
  capacity_eq : capacity=2^h
  complete : MaskedRunDiscovery.Complete (ArrayText.read text fallback) text.size base L partition.occurrences.entries
  positive : 0<L
  slot_size : text.size<st.slots.size

theorem Snapshot.runBacked {text : Array (Fin σ)} {fallback : Fin σ} {source : Array Bool} {removed : List Nat}
    {env : Env C E text.size (MaskedSuffixClass.height text.size)}
    {partition : MaskedClusterLeaders.State h} {capacity L base : Nat} {st : Mutable.Store.State C E}
    (hs : Snapshot text fallback source removed env partition capacity L base st)
    (first : Nat) (anchors : Array (Option Nat)) (ha : readAnchor anchors first L=L) (cfg : Mutable.Store.Config)
    (he : (MaskedTraversalBankReady.prepare partition capacity first L anchors env.window env.catalog env.classes).1=some cfg) :
    RunBacked st.sources env.shared.target env.shared.prepared.K cfg := by
  have hh:=reset_runBacked text fallback source env.shared.target env.shared.prepared.K partition capacity L first base
    anchors env.window hs.invariant hs.capacity_eq hs.complete hs.positive ha cfg
    (by simpa only [hs.catalog,hs.classes] using he) []
  change RunBacked (MaskedMutableProgression.Batch.prepare text fallback source env.shared.prepared.K)
    env.shared.target env.shared.prepared.K cfg at hh
  simpa only [RunBacked,hs.runs] using hh

theorem snapshot_reset_selected (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool) (removed : List Nat)
    (env : Env C E text.size (MaskedSuffixClass.height text.size))
    (partition : MaskedClusterLeaders.State h) (capacity L base first : Nat) (st : Mutable.Store.State C E)
    (hs : Snapshot text fallback source removed env partition capacity L base st)
    (anchors : Array (Option Nat)) (dirty : MaskedTraversalDirty.Marked h)
    (hp : first∈dirty.keys.positions) (entry : Mutable.Store.Entry C E)
    (he : (resetBanks env partition capacity L anchors dirty st).store.slots[first]?.join=some entry) :
    GoodSlot env.shared (resetBanks env partition capacity L anchors dirty st).store partition capacity L first
      (resetBanks env partition capacity L anchors dirty st).anchors entry := by
  have hb:=slot_bound _ first entry he
  rw [resetBanks_size] at hb
  have hcompile:=(resetBanks_compiled env partition capacity L first anchors dirty st hp hb).symm.trans he
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
  · rw [resetBanks_sources]
    exact hs.runBacked first _ hanchor entry.config hprep

theorem snapshot_reset_present (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool) (removed : List Nat)
    (env : Env C E text.size (MaskedSuffixClass.height text.size))
    (partition : MaskedClusterLeaders.State h) (capacity L base first : Nat) (st : Mutable.Store.State C E)
    (hs : Snapshot text fallback source removed env partition capacity L base st)
    (anchors : Array (Option Nat)) (dirty : MaskedTraversalDirty.Marked h)
    (hp : first∈dirty.keys.positions) (hm : first∈partition.leaders.entries) :
    ∃entry,GoodSlot env.shared (resetBanks env partition capacity L anchors dirty st).store partition capacity L first
      (resetBanks env partition capacity L anchors dirty st).anchors entry := by
  obtain ⟨d,hd,_,_⟩:=describeLeader_exists partition capacity L first hs.invariant hs.capacity_eq hm
  have hb0:=((hs.complete first).mp ((hs.invariant.represented first).mp hm).1).1
  have hb1:=hs.slot_size
  have hb : first<st.slots.size := by omega
  have hanchor : readAnchor (resetBanks env partition capacity L anchors dirty st).anchors first L=L := by
    change readAnchor (MaskedTraversalRepair.anchorsLoop L dirty.keys.positions anchors 0).1 first L=L
    rw [MaskedTraversalRepair.anchorsLoop_read,if_pos hp]
  cases hc : (MaskedTraversalBankReady.prepare partition capacity first L
      (resetBanks env partition capacity L anchors dirty st).anchors env.window env.catalog env.classes).1 with
  | none => simp only [MaskedTraversalBankReady.prepare,hd,reduceCtorEq] at hc
  | some cfg =>
    have hr:=hs.runBacked first _ hanchor cfg hc
    have hpres:=compile_present env.shared st cfg source removed hs.valid hs.modulus hr
    cases hbank : (Clip.compiled env.shared st cfg).1 with
    | none => rw [hbank] at hpres; cases hpres
    | some bank =>
      let entry : Mutable.Store.Entry C E:=⟨cfg,bank⟩
      have hslot : (resetBanks env partition capacity L anchors dirty st).store.slots[first]?.join=some entry := by
        rw [resetBanks_compiled env partition capacity L first anchors dirty st hp hb]
        simp only [MaskedTraversalBankReady.compile,hc]
        change ((Clip.compiled env.shared st cfg).1.map _)=some entry
        rw [hbank]
        rfl
      exact ⟨entry,snapshot_reset_selected text fallback source removed env partition capacity L base first st hs
        anchors dirty hp entry hslot⟩

theorem snapshot_reset_raw (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool) (removed : List Nat)
    (env : Env C E text.size (MaskedSuffixClass.height text.size))
    (partition : MaskedClusterLeaders.State h) (capacity L base : Nat) (st : Mutable.Store.State C E)
    (hs : Snapshot text fallback source removed env partition capacity L base st)
    (anchors : Array (Option Nat)) (dirty : MaskedTraversalDirty.Marked h)
    (hr : RawAway env.shared st partition capacity L anchors dirty.keys.positions) :
    RawComplete env.shared (resetBanks env partition capacity L anchors dirty st).store partition capacity L
      (resetBanks env partition capacity L anchors dirty st).anchors := by
  intro first hm
  by_cases hp : first∈dirty.keys.positions
  · obtain ⟨entry,he⟩:=snapshot_reset_present text fallback source removed env partition capacity L base first st hs anchors dirty hp hm
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

theorem snapshot_apply_selected (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool) (removed : List Nat)
    (env : Env C E text.size (MaskedSuffixClass.height text.size))
    (partition : MaskedClusterLeaders.State h) (capacity L base first : Nat) (st : Mutable.Store.State C E)
    (hs : Snapshot text fallback source removed env partition capacity L base st)
    (anchors : Array (Option Nat)) (dirty : MaskedTraversalDirty.Marked h) (tree : BankTree C E h)
    (hr : RawAway env.shared st partition capacity L anchors dirty.keys.positions)
    (hp : first∈dirty.keys.positions ∨ first∈(contextKeys partition capacity dirty).keys.positions)
    (entry : Mutable.Store.Entry C E)
    (he : (apply env partition capacity L anchors dirty st tree).store.slots[first]?.join=some entry) :
    GoodSlot env.shared (apply env partition capacity L anchors dirty st tree).store partition capacity L first
      (apply env partition capacity L anchors dirty st tree).anchors entry := by
  by_cases hq : first∈(contextKeys partition capacity dirty).keys.positions
  · have hready:=snapshot_reset_raw text fallback source removed env partition capacity L base st hs anchors dirty hr
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
    have hgood:=snapshot_reset_selected text fallback source removed env partition capacity L base first st hs anchors dirty hprimary entry hbefore
    exact hgood.transfer (refreshLoop_sources env.shared partition capacity L _ _ _) hslot

theorem snapshot_apply_present (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool) (removed : List Nat)
    (env : Env C E text.size (MaskedSuffixClass.height text.size))
    (partition : MaskedClusterLeaders.State h) (capacity L base first : Nat) (st : Mutable.Store.State C E)
    (hs : Snapshot text fallback source removed env partition capacity L base st)
    (anchors : Array (Option Nat)) (dirty : MaskedTraversalDirty.Marked h) (tree : BankTree C E h)
    (hr : RawAway env.shared st partition capacity L anchors dirty.keys.positions)
    (hp : first∈dirty.keys.positions ∨ first∈(contextKeys partition capacity dirty).keys.positions)
    (hm : first∈partition.leaders.entries) :
    ∃entry,GoodSlot env.shared (apply env partition capacity L anchors dirty st tree).store partition capacity L first
      (apply env partition capacity L anchors dirty st tree).anchors entry := by
  by_cases hq : first∈(contextKeys partition capacity dirty).keys.positions
  · apply refreshLoop_selected env.shared partition capacity L first _ _ _
      (snapshot_reset_raw text fallback source removed env partition capacity L base st hs anchors dirty hr) source removed _ _ hq hm
    · rw [resetBanks_sources]; exact hs.valid
    · rw [resetBanks_sources]; exact hs.modulus
  · obtain ⟨entry,hentry⟩:=snapshot_reset_present text fallback source removed env partition capacity L base first st hs anchors dirty (hp.resolve_right hq) hm
    exact ⟨entry,hentry.transfer (refreshLoop_sources env.shared partition capacity L _ _ _)
      (refreshLoop_other env.shared partition capacity L first _ _ _ hq)⟩

end REWB.MaskedTraversalRepairCoherence
