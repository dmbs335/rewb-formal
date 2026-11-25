import REWB.MaskedTraversalExecute
import REWB.MaskedTraversalSuspended

/-! Physical support of suspended bank entries and actual dirty keys.
No full-class certificate is required at a saved parent-depth frontier:
candidate support was established at the last complete-band compilation
and is preserved by the occurrence-monotone geometric operations.
-/
namespace REWB.MaskedTraversalExecute
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedTraversalAggregate
open REWB.MaskedClusterDescriptor REWB.MaskedTraversalDirty
variable {α : Type} {C E : DFA α} {h : Nat}

def Supported (positions : List Nat) (entries : List (Option (Mutable.Store.Entry C E))) : Prop :=
  ∀(first : Nat) (entry : Mutable.Store.Entry C E),entries[first]?=some (some entry)→∀p,
    Mutable.Batch.Candidates entry.config.descriptor.first entry.config.descriptor.period entry.config.descriptor.repetitions p→
      p∈positions

theorem supported_mono (before after : List Nat) (entries : List (Option (Mutable.Store.Entry C E)))
    (hs : Supported before entries) (hm : ∀p,p∈before→p∈after) : Supported after entries := by
  intro first entry he p hp
  exact hm p (hs first entry he p hp)

theorem coherent_supported (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity L : Nat)
    (entries : List (Option (Mutable.Store.Entry C E)))
    (hi : MaskedClusterLeaders.Invariant L partition) (hc : capacity=2^h)
    (coherent : Cells.Coherent env st partition capacity L entries)
    (f : Nat→α) (n base : Nat)
    (full : MaskedRunDiscovery.Complete f n base L partition.occurrences.entries) :
    Supported partition.occurrences.entries entries := by
  intro first entry he p hp
  obtain ⟨k,hk,rfl⟩:=hp
  have hd:=describeLeader_sound partition capacity L first hi hc entry.config.descriptor (coherent first entry he).descriptor
  exact hd.2.ap_mem partition capacity L hi hc entry.config.descriptor f n base full k hk

theorem supported_reindexed (positions : List Nat) (entries : List (Option (Mutable.Store.Entry C E)))
    (z : ReplayMaps.Value C.stateCount E.stateCount) (fresh : Nat) (hs : Supported positions entries) :
    Supported positions (entries.map (Cells.reindexedEntry z fresh)) := by
  intro first entry he p hp
  obtain ⟨before,hbefore,rfl⟩:=MaskedTraversalRepairTransport.reindexed_get z fresh first entries entry he
  exact hs first before hbefore p hp

def DirtySupported (positions : List Nat) (dirty : MaskedTraversalDirty.Marked h) : Prop :=
  ∀p,p∈dirty.keys.positions→p∈positions

theorem dirty_empty (positions : List Nat) : DirtySupported positions (MaskedTraversalDirty.empty h) := by
  intro p hp
  cases hp

theorem change_supported (before after : MaskedOrdered.Tree h) (capacity p : Nat)
    (positions : List Nat) (hbg : before.Good) (hbf : before.Fits 0)
    (hag : after.Good) (haf : after.Fits 0) (hc : capacity=2^h)
    (hb : ∀q,q∈before.entries→q∈positions) (ha : ∀q,q∈after.entries→q∈positions) (hp : p∈positions) :
    ∀q,q∈(prepareChange before after capacity p).keys→q∈positions := by
  intro q hq
  change q∈p::((around before capacity p).keys++(around after capacity p).keys) at hq
  rcases List.mem_cons.mp hq with rfl|hq
  · exact hp
  · rcases List.mem_append.mp hq with hq|hq
    · exact hb q (around_mem before capacity p q hbg hbf hc hq)
    · exact ha q (around_mem after capacity p q hag haf hc hq)

theorem marked_supported (before after : MaskedOrdered.Tree h) (capacity p : Nat)
    (positions : List Nat) (dirty : MaskedTraversalDirty.Marked h) (hv : dirty.keys.Valid)
    (hbg : before.Good) (hbf : before.Fits 0) (hag : after.Good) (haf : after.Fits 0) (hc : capacity=2^h)
    (hp : p<2^h) (hb : ∀q,q∈before.entries→q∈positions) (ha : ∀q,q∈after.entries→q∈positions)
    (hpos : p∈positions) (hd : DirtySupported positions dirty) :
    DirtySupported positions (markChange before after capacity p dirty) := by
  have hs:=markChange_spec before after capacity p dirty hv hbg hbf hag haf hc hp
  intro q hq
  rcases (hs.2.1 q).mp (hs.1.2.2.mem_iff.mp hq) with hnew|hold
  · exact change_supported before after capacity p positions hbg hbf hag haf hc hb ha hpos q hnew
  · exact hd q (hv.2.2.mem_iff.mpr hold)

theorem add_supported (before : MaskedClusterLeaders.State h) (capacity L p : Nat)
    (dirty : MaskedTraversalDirty.Marked h) (hv : dirty.keys.Valid)
    (hi : MaskedClusterLeaders.Invariant L before) (hc : capacity=2^h) (hp : p<capacity)
    (hd : DirtySupported before.occurrences.entries dirty) :
    DirtySupported (MaskedClusterLeaders.add capacity L p before).state.occurrences.entries
      (markChange before.leaders (MaskedClusterLeaders.add capacity L p before).state.leaders capacity p dirty) := by
  have ha:=MaskedClusterLeaders.add_invariant capacity L p before hi hc hp
  have mem : ∀q,q∈(MaskedClusterLeaders.add capacity L p before).state.occurrences.entries ↔ q=p ∨ q∈before.occurrences.entries := by
    intro q
    exact MaskedOrdered.insert_mem before.occurrences capacity p q hi.occFits hc (by omega)
  apply marked_supported before.leaders _ capacity p _ dirty hv hi.leadGood hi.leadFits ha.leadGood ha.leadFits hc (by omega)
  · intro q hq
    exact (mem q).mpr (Or.inr ((hi.represented q).mp hq).1)
  · intro q hq
    exact ((ha.represented q).mp hq).1
  · exact (mem p).mpr (Or.inl rfl)
  · intro q hq
    exact (mem q).mpr (Or.inr (hd q hq))

theorem crossing_supported (capacity old fresh : Nat) (s : MaskedClusterLeaders.State h)
    (dirty : MaskedTraversalDirty.Marked h) (hv : dirty.keys.Valid)
    (hi : MaskedClusterLeaders.Invariant old s) (hf : MaskedClusterLeaders.Future old s)
    (hc : capacity=2^h) (hle : fresh≤old) (hd : DirtySupported s.occurrences.entries dirty) :
    DirtySupported s.occurrences.entries
      (crossing s (MaskedClusterLeaders.shorten capacity fresh s) capacity dirty) := by
  have ha:=MaskedClusterLeaders.shorten_invariant capacity old fresh s hi hf hc hle
  have bound:=MaskedClusterLeaders.live_bound capacity old fresh s hi hc
  have hs:=live_spec s.leaders (MaskedClusterLeaders.shorten capacity fresh s).state.leaders capacity
    (MaskedClusterLeaders.shorten capacity fresh s).live dirty hv hi.leadGood hi.leadFits ha.leadGood ha.leadFits hc
    (fun e he=>by have hh:=bound e he; omega)
  intro p hp
  rcases (hs.2.1 p).mp (hs.1.2.2.mem_iff.mp hp) with ⟨e,he,hp⟩|hp
  · have hadj:=((MaskedThresholdEvents.shorten_correct (h+1) fresh s.occurrences capacity s.queue
      hi.occGood hi.occFits hc hi.queueGood e).mp he).2.2
    exact change_supported s.leaders (MaskedClusterLeaders.shorten capacity fresh s).state.leaders capacity e.value.edge.2
      s.occurrences.entries hi.leadGood hi.leadFits ha.leadGood ha.leadFits hc
      (fun q hq=>((hi.represented q).mp hq).1) (fun q hq=>((ha.represented q).mp hq).1) hadj.2.1 p hp
  · exact hd p (hv.2.2.mem_iff.mpr hp)

end REWB.MaskedTraversalExecute
