import REWB.MaskedTraversalIncomingOperations

/-! Bridge structural/local-anchor preservation to concrete stored bank
configuration fields. The only permissible normalization is the current
length: own H, actual incoming cursor, run ID and immutable counts remain
the same outside the primary and current-successor repair sets.
-/
namespace REWB.MaskedTraversalIncoming
open REWB.MaskedOrdered REWB.MaskedClusterDescriptor REWB.MaskedTraversalBankReady
open REWB.MaskedTraversalContext
variable {α : Type} {h : Nat}

theorem populated_length (partition : MaskedClusterLeaders.State h) (capacity n old fresh first : Nat)
    (f : Nat→α) (anchors : Array (Option Nat))
    (hi : MaskedClusterLeaders.Invariant old partition) (hc : capacity=2^h)
    (ha : MaskedTraversalRetained.Away partition capacity f n old anchors []) :
    incoming partition capacity first fresh anchors=incoming partition capacity first old anchors := by
  cases hp : (Tree.pred partition.leaders capacity first).1 with
  | none => simp only [incoming,hp]
  | some p =>
    have hs:=Tree.pred_correct partition.leaders capacity first hi.leadGood hi.leadFits hc
    rw [hp] at hs
    obtain ⟨d,hd,_,_⟩:=describeLeader_exists partition capacity old p hi hc hs.1
    obtain ⟨H,hH,_⟩:=ha p (by simp) d hd
    simp only [incoming,hp,hd,readAnchor,hH,Option.getD_some]

theorem band_incoming (f : Nat→α) (n capacity L first : Nat) (anchors : Array (Option Nat))
    (origin : Tree h) (band : MaskedTraversalEdge.Band h) (hv : band.Valid capacity origin)
    (hc : capacity=2^h)
    (ha : MaskedTraversalRetained.Away band.snapshot capacity f n band.hi anchors []) :
    incoming band.snapshot capacity first L anchors=incoming band.snapshot capacity first band.hi anchors :=
  populated_length band.snapshot capacity n band.hi L first f anchors hv.invariant hc ha

/-- This equality records all fields, including unchanged source-window
selection, run ID and target counts, rather than merely the two cursor
projections. The old configuration may have any older raw length. -/
theorem config_preserved (before after : MaskedClusterLeaders.State h)
    (capacity old fresh first : Nat) (anchors : Array (Option Nat)) (keys : List Nat)
    (cfg : MaskedCluster.Mutable.Store.Config)
    (hkey : first∉keys)
    (hanchor : readAnchor anchors first fresh=readAnchor anchors first old)
    (hin : (incoming after capacity first fresh (MaskedTraversalRepair.anchorsLoop fresh keys anchors 0).1).cursor=
      (incoming before capacity first old anchors).cursor ∧
      (incoming after capacity first fresh (MaskedTraversalRepair.anchorsLoop fresh keys anchors 0).1).enabled=
      (incoming before capacity first old anchors).enabled) :
    config after capacity first fresh (MaskedTraversalRepair.anchorsLoop fresh keys anchors 0).1 cfg=
      {config before capacity first old anchors cfg with length:=fresh} := by
  simp only [config,MaskedTraversalRepair.anchorsLoop_read,if_neg hkey,hanchor,hin.1,hin.2]

theorem retained_config_preserved (before after : MaskedClusterLeaders.State h)
    (capacity n old fresh first : Nat) (f : Nat→α) (anchors : Array (Option Nat)) (keys : List Nat)
    (cfg : MaskedCluster.Mutable.Store.Config)
    (hb : MaskedClusterLeaders.Invariant old before) (ha : MaskedClusterLeaders.Invariant fresh after)
    (hc : capacity=2^h)
    (hocc : ∀p,p∈before.occurrences.entries→p∈after.occurrences.entries)
    (hdesc : ∀p,p∉keys→(describeLeader after capacity p).1=(describeLeader before capacity p).1)
    (hown : MaskedTraversalRetained.Away after capacity f n fresh anchors keys)
    (hm : first∈after.leaders.entries) (hkey : first∉keys)
    (hn : first∉(successors after.leaders capacity keys (MaskedTraversalDirty.empty h)).keys.tree.entries) :
    config after capacity first fresh (MaskedTraversalRepair.anchorsLoop fresh keys anchors 0).1 cfg=
      {config before capacity first old anchors cfg with length:=fresh} := by
  have hin:=retained_transport before after capacity n old fresh first f anchors keys hb ha hc hocc hdesc hown hm hn
  have hreset:=reset_preserves_transport before after capacity old fresh first anchors keys ha hc hm hn hin
  obtain ⟨d,hd,_,_⟩:=describeLeader_exists after capacity fresh first ha hc hm
  obtain ⟨H,hH,_⟩:=hown first hkey d hd
  apply config_preserved before after capacity old fresh first anchors keys cfg hkey _ hreset
  simp only [readAnchor,hH,Option.getD_some]

end REWB.MaskedTraversalIncoming
