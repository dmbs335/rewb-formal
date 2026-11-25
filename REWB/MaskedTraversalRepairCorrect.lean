import REWB.MaskedTraversalRepair

/-! Simultaneous anchor resets preserve the required neighbor bound when
only unmarked anchors were already safe. Marked anchors are repaired from
the actual complete class. The final selected bank is the literal current
source-history compiler, with every predecessor read using the completed
anchor pass. No premise supplies a bank answer, a run ID or a query cost.

The unmarked-anchor premise is the precise residual locality obligation
for the dirty-set producer; it is not asserted by this module.
-/
namespace REWB.MaskedTraversalRepair
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedTraversalBankReady REWB.MaskedRunDiscovery
variable {α : Type} {σ h h' n : Nat}

def AnchorBoundsAway (partition : MaskedClusterLeaders.State h) (capacity n L : Nat)
    (anchors : Array (Option Nat)) (ps : List Nat) : Prop :=
  ∀first,first∉ps→∀d,(MaskedClusterDescriptor.describeLeader partition capacity first).1=some d→
    d.last+readAnchor anchors first L≤n ∧
    ∀p,d.following=some p→d.last+readAnchor anchors first L≤p

theorem anchorsLoop_bounds (partition : MaskedClusterLeaders.State h) (capacity n base L : Nat)
    (f : Nat→α) (anchors : Array (Option Nat)) (ps : List Nat) (work : Nat)
    (hi : MaskedClusterLeaders.Invariant L partition) (hc : capacity=2^h)
    (hfull : Complete f n base L partition.occurrences.entries) (hL : 0<L)
    (ha : AnchorBoundsAway partition capacity n L anchors ps) :
    AnchorBounds partition capacity n L (anchorsLoop L ps anchors work).1 := by
  intro first d hd
  rw [anchorsLoop_read]
  by_cases hp : first∈ps
  · rw [if_pos hp]
    have hg:=MaskedClusterDescriptor.describeLeader_geometry partition capacity L first hi hc d hd
      f n base hfull hL
    exact ⟨hg.anchor.lastBound,hg.anchor.followingSafe⟩
  · rw [if_neg hp]
    exact ha first hp d hd

theorem reset_sources (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (partition : MaskedClusterLeaders.State h) (capacity current : Nat)
    (anchors : Array (Option Nat)) (window : SourceWindow)
    (catalog : MaskedRunCatalog.Index) (classes : MaskedSuffixClass.Index n h')
    (target : Array Bool) (keys : MaskedTraversalDirty.Marked h) (st : Mutable.Store.State C E) :
    (reset C E book prepared ci ei partition capacity current anchors window catalog classes target keys st).store.sources=st.sources :=
  banksLoop_sources C E book prepared ci ei partition capacity current _ window catalog classes target _ st

theorem reset_other (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (partition : MaskedClusterLeaders.State h) (capacity current : Nat)
    (anchors : Array (Option Nat)) (window : SourceWindow)
    (catalog : MaskedRunCatalog.Index) (classes : MaskedSuffixClass.Index n h')
    (target : Array Bool) (keys : MaskedTraversalDirty.Marked h) (st : Mutable.Store.State C E)
    (p : Nat) (hp : p∉keys.keys.positions) :
    (reset C E book prepared ci ei partition capacity current anchors window catalog classes target keys st).store.slots[p]?=st.slots[p]? :=
  banksLoop_other C E book prepared ci ei partition capacity current _ window catalog classes target _ st p hp

theorem reset_current (C E : DFA (Fin σ)) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount) (hK : 0<prepared.K)
    (text : Array (Fin σ)) (fallback : Fin σ) (source target : Array Bool) (removed : List Nat)
    (partition : MaskedClusterLeaders.State h) (capacity L first base : Nat)
    (anchors : Array (Option Nat)) (window : SourceWindow) (keys : MaskedTraversalDirty.Marked h)
    (st : Mutable.Store.State C E)
    (hsrc : st.sources=MaskedMutableProgression.Batch.run text fallback source prepared.K removed)
    (hi : MaskedClusterLeaders.Invariant L partition) (hcap : capacity=2^h)
    (d : MaskedClusterDescriptor.Descriptor)
    (hd : (MaskedClusterDescriptor.describeLeader partition capacity first).1=some d)
    (hfull : Complete (ArrayText.read text fallback) text.size base L partition.occurrences.entries)
    (hL : 0<L) (haway : AnchorBoundsAway partition capacity text.size L anchors keys.keys.positions)
    (hp : first∈keys.keys.positions) (hb : first<st.slots.size)
    (gate inMode outMode : Bool) (i j : Fin (MaskedClusterStage.dfa C E).stateCount) :
    let out:=reset C E book prepared (BoundaryApplication.Range.build C text.toList)
      (BoundaryApplication.Range.build E text.toList) partition capacity L anchors window
      (MaskedRunCatalog.ofBatch target (MaskedMutableProgression.Batch.prepare text fallback source prepared.K))
      (MaskedSuffixClass.prepare text fallback) target keys st
    (out.store.slots[first]?.join).any
      (fun entry=>entry.bank.view (code _ gate (ReplayMaps.encode (ReplayMaps.one C.stateCount E.stateCount)))
        (code _ inMode i) (code _ outMode j))=true ↔
      Mutable.Batch.CursorStep C E text.toList d.first d.period d.repetitions L L (d.nextAt text.size)
        (incoming partition capacity first L out.anchors).cursor (incoming partition capacity first L out.anchors).enabled
        inMode outMode source removed target (window.gate gate)
        (MaskedClusterStage.decode C E i) (MaskedClusterStage.decode C E j) := by
  dsimp only [reset]
  rw [banksLoop_selected C E book prepared _ _ partition capacity L _ window _ _ target _ st first hp hb]
  simp only [Option.join]
  rw [hsrc]
  apply compile_reset_current C E book prepared hK text fallback source target removed partition capacity L first base
    (anchorsLoop L keys.keys.positions anchors 0).1 window hi hcap d hd hfull hL
  · exact anchorsLoop_bounds partition capacity text.size base L (ArrayText.read text fallback)
      anchors keys.keys.positions 0 hi hcap hfull hL haway
  · rw [anchorsLoop_read,if_pos hp]

end REWB.MaskedTraversalRepair
