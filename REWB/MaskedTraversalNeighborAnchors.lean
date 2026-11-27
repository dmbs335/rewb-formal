import REWB.MaskedTraversalNeighborMerge
import REWB.MaskedTraversalRepairCorrect

/-! The reset pass's former unmarked-anchor premise is propagated by
the actual geometric operations and their computed dirty sets. Existing
unsafe marked anchors may remain pending through partial/equal-depth
imports; every unmarked current descriptor retains its bounds. A complete
class reset then obtains full AnchorBounds from these proved premises.
-/
namespace REWB.MaskedTraversalNeighbor
open REWB.MaskedClusterDescriptor REWB.MaskedTraversalBankReady REWB.MaskedTraversalRepair
open REWB.MaskedTraversalFrontier
variable {h : Nat}

theorem readAnchor_mono (anchors : Array (Option Nat)) (first fresh old : Nat) (hle : fresh≤old) :
    readAnchor anchors first fresh≤readAnchor anchors first old := by
  unfold readAnchor
  cases he : (anchors[first]?).join with
  | none => exact hle
  | some H => exact Nat.le_refl _

theorem transport_boundsAway (before after : MaskedClusterLeaders.State h) (capacity n old fresh : Nat)
    (anchors : Array (Option Nat)) (oldKeys newKeys : List Nat) (hle : fresh≤old)
    (hgrow : ∀p,p∈oldKeys→p∈newKeys)
    (hdesc : ∀p,p∉newKeys→(describeLeader after capacity p).1=(describeLeader before capacity p).1)
    (hb : AnchorBoundsAway before capacity n old anchors oldKeys) :
    AnchorBoundsAway after capacity n fresh anchors newKeys := by
  intro first hnot d hd
  have hold : (describeLeader before capacity first).1=some d := (hdesc first hnot).symm.trans hd
  have hnotOld : first∉oldKeys := by intro hm; exact hnot (hgrow first hm)
  have hs:=hb first hnotOld d hold
  have hr:=readAnchor_mono anchors first fresh old hle
  exact ⟨Nat.le_trans (Nat.add_le_add_left hr d.last) hs.1,
    fun p hp=>Nat.le_trans (Nat.add_le_add_left hr d.last) (hs.2 p hp)⟩

theorem add_anchorBoundsAway (before : MaskedClusterLeaders.State h) (capacity n L p : Nat)
    (anchors : Array (Option Nat)) (dirty : MaskedTraversalDirty.Marked h)
    (hv : dirty.keys.Valid) (hi : MaskedClusterLeaders.Invariant L before)
    (hc : capacity=2^h) (hp : p<capacity)
    (hb : AnchorBoundsAway before capacity n L anchors dirty.keys.positions) :
    AnchorBoundsAway (MaskedClusterLeaders.add capacity L p before).state capacity n L anchors
      (MaskedTraversalDirty.markChange before.leaders (MaskedClusterLeaders.add capacity L p before).state.leaders
        capacity p dirty).keys.positions := by
  have ha:=MaskedClusterLeaders.add_invariant capacity L p before hi hc hp
  have hs:=MaskedTraversalDirty.markChange_spec before.leaders
    (MaskedClusterLeaders.add capacity L p before).state.leaders capacity p dirty hv
    hi.leadGood hi.leadFits ha.leadGood ha.leadFits hc (by omega)
  apply transport_boundsAway before (MaskedClusterLeaders.add capacity L p before).state capacity n L L
    anchors dirty.keys.positions _ (Nat.le_refl _)
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

theorem crossing_anchorBoundsAway (capacity n old fresh : Nat) (s : MaskedClusterLeaders.State h)
    (anchors : Array (Option Nat)) (dirty : MaskedTraversalDirty.Marked h) (hv : dirty.keys.Valid)
    (hi : MaskedClusterLeaders.Invariant old s) (hf : MaskedClusterLeaders.Future old s)
    (hc : capacity=2^h) (hle : fresh≤old)
    (hb : AnchorBoundsAway s capacity n old anchors dirty.keys.positions) :
    AnchorBoundsAway (MaskedClusterLeaders.shorten capacity fresh s).state capacity n fresh anchors
      (MaskedTraversalDirty.crossing s (MaskedClusterLeaders.shorten capacity fresh s) capacity dirty).keys.positions := by
  have ha:=MaskedClusterLeaders.shorten_invariant capacity old fresh s hi hf hc hle
  have hbound:=MaskedClusterLeaders.live_bound capacity old fresh s hi hc
  have hs:=MaskedTraversalDirty.live_spec s.leaders (MaskedClusterLeaders.shorten capacity fresh s).state.leaders capacity
    (MaskedClusterLeaders.shorten capacity fresh s).live dirty hv hi.leadGood hi.leadFits ha.leadGood ha.leadFits hc
    (fun e he=>by have hh:=hbound e he; omega)
  apply transport_boundsAway s (MaskedClusterLeaders.shorten capacity fresh s).state capacity n old fresh
    anchors dirty.keys.positions _ hle
  · intro x hx
    apply hs.1.2.2.mem_iff.mpr
    exact (hs.2.1 x).mpr (Or.inr (hv.2.2.mem_iff.mp hx))
  · intro x hx
    apply crossing_describe_unmarked capacity old fresh x s dirty hv hi hf hc hle
    intro hm
    exact hx (hs.1.2.2.mem_iff.mpr hm)
  · exact hb

theorem merge_anchorBoundsAway (capacity n L : Nat) (left right : Frontier h)
    (anchors : Array (Option Nat)) (dirty : MaskedTraversalDirty.Marked h) (hv : dirty.keys.Valid)
    (hl : left.Valid L) (hr : right.Valid L) (hc : capacity=2^h)
    (hb : AnchorBoundsAway
      (if (MaskedTraversalFrontier.merge capacity L left right).keptLeft then left.state else right.state)
      capacity n L anchors dirty.keys.positions) :
    AnchorBoundsAway (MaskedTraversalFrontier.merge capacity L left right).frontier.state capacity n L anchors
      (MaskedTraversalDirty.patches capacity (MaskedTraversalFrontier.merge capacity L left right).revPatches dirty).keys.positions := by
  have hp:=MaskedTraversalDirty.merge_patches capacity L left right hl hr hc
  have hs:=MaskedTraversalDirty.patches_spec capacity L
    (MaskedTraversalFrontier.merge capacity L left right).revPatches dirty hv hc hp
  apply transport_boundsAway
    (if (MaskedTraversalFrontier.merge capacity L left right).keptLeft then left.state else right.state)
    (MaskedTraversalFrontier.merge capacity L left right).frontier.state capacity n L L anchors dirty.keys.positions _ (Nat.le_refl _)
  · intro x hx
    apply hs.1.2.2.mem_iff.mpr
    exact (hs.2.1 x).mpr (Or.inr (hv.2.2.mem_iff.mp hx))
  · intro x hx
    apply merge_describe_unmarked capacity L x left right dirty hv hl hr hc
    intro hm
    exact hx (hs.1.2.2.mem_iff.mpr hm)
  · exact hb

end REWB.MaskedTraversalNeighbor
