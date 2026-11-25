import REWB.MaskedTraversalRetainedMode

/-! Retained anchored words, overlap mode and all cursor safety fields
are preserved by actual insertion/merge/crossing operations outside the
computed pending sets. These theorems strengthen the earlier scalar
AnchorBoundsAway transport to the full certificate used by physical bank
semantics. No cluster membership or mask-dependent geometry scan is used.
-/
namespace REWB.MaskedTraversalRetained
open REWB.MaskedClusterDescriptor REWB.MaskedRunDiscovery REWB.MaskedTraversalBankReady REWB.MaskedTraversalRepair
open REWB.MaskedTraversalFrontier REWB.MaskedTraversalNeighbor
variable {α : Type} {h : Nat}

theorem add_away (before : MaskedClusterLeaders.State h) (capacity n L p : Nat)
    (f : Nat→α) (anchors : Array (Option Nat)) (dirty : MaskedTraversalDirty.Marked h)
    (hv : dirty.keys.Valid) (hi : MaskedClusterLeaders.Invariant L before)
    (hc : capacity=2^h) (hp : p<capacity)
    (hb : Away before capacity f n L anchors dirty.keys.positions) :
    Away (MaskedClusterLeaders.add capacity L p before).state capacity f n L anchors
      (MaskedTraversalDirty.markChange before.leaders (MaskedClusterLeaders.add capacity L p before).state.leaders
        capacity p dirty).keys.positions := by
  have ha:=MaskedClusterLeaders.add_invariant capacity L p before hi hc hp
  have hs:=MaskedTraversalDirty.markChange_spec before.leaders
    (MaskedClusterLeaders.add capacity L p before).state.leaders capacity p dirty hv
    hi.leadGood hi.leadFits ha.leadGood ha.leadFits hc (by omega)
  apply transport_same before (MaskedClusterLeaders.add capacity L p before).state capacity f n L
    anchors dirty.keys.positions _
  · intro x hx
    apply hs.1.2.2.mem_iff.mpr
    exact (hs.2.1 x).mpr (Or.inr (hv.2.2.mem_iff.mp hx))
  · intro x hx
    apply add_describe_away before capacity L p x hi hc hp
    intro hm
    apply hx
    apply hs.1.2.2.mem_iff.mpr
    exact (hs.2.1 x).mpr (Or.inl hm)
  · exact hb

theorem merge_away (capacity n L : Nat) (left right : Frontier h)
    (f : Nat→α) (anchors : Array (Option Nat)) (dirty : MaskedTraversalDirty.Marked h) (hv : dirty.keys.Valid)
    (hl : left.Valid L) (hr : right.Valid L) (hc : capacity=2^h)
    (hb : Away
      (if (MaskedTraversalFrontier.merge capacity L left right).keptLeft then left.state else right.state)
      capacity f n L anchors dirty.keys.positions) :
    Away (MaskedTraversalFrontier.merge capacity L left right).frontier.state capacity f n L anchors
      (MaskedTraversalDirty.patches capacity (MaskedTraversalFrontier.merge capacity L left right).revPatches dirty).keys.positions := by
  have hp:=MaskedTraversalDirty.merge_patches capacity L left right hl hr hc
  have hs:=MaskedTraversalDirty.patches_spec capacity L
    (MaskedTraversalFrontier.merge capacity L left right).revPatches dirty hv hc hp
  apply transport_same
    (if (MaskedTraversalFrontier.merge capacity L left right).keptLeft then left.state else right.state)
    (MaskedTraversalFrontier.merge capacity L left right).frontier.state capacity f n L anchors dirty.keys.positions _
  · intro x hx
    apply hs.1.2.2.mem_iff.mpr
    exact (hs.2.1 x).mpr (Or.inr (hv.2.2.mem_iff.mp hx))
  · intro x hx
    apply merge_describe_unmarked capacity L x left right dirty hv hl hr hc
    intro hm
    exact hx (hs.1.2.2.mem_iff.mpr hm)
  · exact hb

theorem crossing_away (capacity n old fresh : Nat) (s : MaskedClusterLeaders.State h)
    (f : Nat→α) (anchors : Array (Option Nat)) (dirty : MaskedTraversalDirty.Marked h) (hv : dirty.keys.Valid)
    (hi : MaskedClusterLeaders.Invariant old s) (hf : MaskedClusterLeaders.Future old s)
    (hc : capacity=2^h) (hle : fresh≤old)
    (hb : Away s capacity f n old anchors dirty.keys.positions) :
    Away (MaskedClusterLeaders.shorten capacity fresh s).state capacity f n fresh anchors
      (MaskedTraversalDirty.crossing s (MaskedClusterLeaders.shorten capacity fresh s) capacity dirty).keys.positions := by
  have ha:=MaskedClusterLeaders.shorten_invariant capacity old fresh s hi hf hc hle
  have hbound:=MaskedClusterLeaders.live_bound capacity old fresh s hi hc
  have hs:=MaskedTraversalDirty.live_spec s.leaders (MaskedClusterLeaders.shorten capacity fresh s).state.leaders capacity
    (MaskedClusterLeaders.shorten capacity fresh s).live dirty hv hi.leadGood hi.leadFits ha.leadGood ha.leadFits hc
    (fun e he=>by have hh:=hbound e he; omega)
  intro first hnot d hdesc
  have hnotTree : first∉(MaskedTraversalDirty.crossing s (MaskedClusterLeaders.shorten capacity fresh s) capacity dirty).keys.tree.entries :=
    fun hm=>hnot (hs.1.2.2.mem_iff.mpr hm)
  have hnotOld : first∉dirty.keys.positions := by
    intro hm
    apply hnotTree
    exact (hs.2.1 first).mpr (Or.inr (hv.2.2.mem_iff.mp hm))
  have hdeq:=crossing_describe_unmarked capacity old fresh first s dirty hv hi hf hc hle hnotTree
  have hdescOld : (describeLeader s capacity first).1=some d := hdeq.symm.trans hdesc
  obtain ⟨H,hH,cert⟩:=hb first hnotOld d hdescOld
  have hd:=describeLeader_sound s capacity old first hi hc d hdescOld
  have hlast : d.last+old≤n := by have h1:=cert.current; have h2:=cert.lastBound; omega
  have hmode:=mode_away capacity n old fresh s hi hf hc hle d hd.2 hlast (by
    intro e he hm
    apply hnotTree
    apply (hs.2.1 first).mpr
    apply Or.inl
    refine ⟨e,he,?_⟩
    simpa only [hd.1] using hm)
  exact ⟨H,hH,MaskedLocalAnchor.shorten f n d.first old fresh (copies d) d.last (d.nextAt n)
    d.previous d.following H cert hle hmode⟩

theorem band_all (f : Nat→α) (n capacity L : Nat) (anchors : Array (Option Nat))
    (origin : REWB.MaskedOrdered.Tree h) (band : MaskedTraversalEdge.Band h) (hv : band.Valid capacity origin)
    (hc : capacity=2^h) (hl : band.lo≤L) (hh : L≤band.hi)
    (ha : Away band.snapshot capacity f n band.hi anchors []) :
    Away band.snapshot capacity f n L anchors [] := by
  intro first hn d hd
  exact band_own f n capacity first L anchors origin band hv hc hl hh d hd (ha first hn d hd)

theorem crossing_reset_all (capacity n base old fresh : Nat) (s : MaskedClusterLeaders.State h)
    (f : Nat→α) (anchors : Array (Option Nat)) (dirty : MaskedTraversalDirty.Marked h) (hv : dirty.keys.Valid)
    (hi : MaskedClusterLeaders.Invariant old s) (hf : MaskedClusterLeaders.Future old s)
    (hc : capacity=2^h) (hle : fresh≤old)
    (hb : Away s capacity f n old anchors dirty.keys.positions)
    (hfull : Complete f n base fresh (MaskedClusterLeaders.shorten capacity fresh s).state.occurrences.entries)
    (hpos : 0<fresh) (hn : n<anchors.size) :
    Away (MaskedClusterLeaders.shorten capacity fresh s).state capacity f n fresh
      (anchorsLoop fresh
        (MaskedTraversalDirty.crossing s (MaskedClusterLeaders.shorten capacity fresh s) capacity dirty).keys.positions anchors 0).1 [] :=
  reset_all _ capacity n base fresh f anchors _
    (MaskedClusterLeaders.shorten_invariant capacity old fresh s hi hf hc hle) hc hfull hpos hn
    (crossing_away capacity n old fresh s f anchors dirty hv hi hf hc hle hb)

end REWB.MaskedTraversalRetained
