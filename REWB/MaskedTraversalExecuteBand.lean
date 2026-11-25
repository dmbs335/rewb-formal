import REWB.MaskedTraversalExecuteInvariant

/-! Complete preservation for the concrete positive-band transaction:
two-pass actual repair, shared-cut report, physical source deletion,
single shared replay selection, lazy aggregate reindex and actual live
crossing collection. The next length can be zero or an incomplete parent
class; its output is Pending, not an unjustified new complete-class reset.
-/
namespace REWB.MaskedTraversalExecute
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedTraversalAggregate
open REWB.MaskedTraversalRepairCoherence
variable {σ h : Nat} {B C E : DFA (Fin σ)}

theorem band_prepared (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool)
    (env : Env B C E text.size (MaskedSuffixClass.height text.size)) (hs : Static text fallback source env)
    (capacity : Nat) (hc : capacity=2^h) (b : MaskedTraversalEdge.Band h) (st : State C E h)
    (hv : st.Valid text fallback source env b.snapshot capacity b.hi)
    (hm : MaskedTraversalPositiveCoverage.Metadata text fallback capacity b) :
    let repaired:=MaskedTraversalRepairCoherence.apply env.repair b.snapshot capacity b.hi st.global.anchors st.frame.dirty st.global.store st.frame.tree
    Cells.Maintained env.repair.shared b.snapshot capacity b.hi text.size repaired.anchors source st.global.answers.history repaired.store repaired.tree ∧
      MaskedTraversalRetained.Away b.snapshot capacity (ArrayText.read text fallback) text.size b.hi repaired.anchors [] ∧
      ∀L,b.lo≤L→L≤b.hi→Cells.BandGeometry text.toList fallback b.snapshot capacity (representative b) b.hi L repaired.anchors := by
  obtain ⟨entries,hr,hp,hu,_⟩:=hv.entries
  have snap:=snapshot text fallback source env hs capacity hc b st hv.global hm
  have maintained:=snapshot_apply_maintained text fallback source st.global.answers.history env.repair b.snapshot capacity b.hi
    (representative b) st.global.store snap st.global.anchors st.frame.dirty st.frame.tree entries hp hv.tree hr hs.window hu
  have own:=snapshot_apply_anchors text fallback source st.global.answers.history env.repair b.snapshot capacity b.hi
    (representative b) st.global.store snap st.global.anchors st.frame.dirty st.frame.tree hv.own hv.global.anchors
  refine ⟨maintained,own,?_⟩
  intro L hL hH
  refine ⟨hm.valid.invariant,(hm.valid.at hc hL hH).1,hc,?_,?_,?_,?_,?_,hH,?_⟩
  · simpa only [Array.toArray_toList,Array.length_toList] using hm.complete b.hi hm.valid.bounds (Nat.le_refl _)
  · simpa only [Array.toArray_toList,Array.length_toList] using hm.complete L hL hH
  · simpa only [Array.toArray_toList,Array.length_toList] using own
  · simpa only [Array.toArray_toList,Array.length_toList] using
      MaskedTraversalRetained.band_all (ArrayText.read text fallback) text.size capacity L _ _ b hm.valid hc hL hH own
  · have hh:=hm.positive
    omega
  · simpa only [Array.length_toList] using hm.bounded

theorem band_valid (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool)
    (env : Env B C E text.size (MaskedSuffixClass.height text.size)) (hs : Static text fallback source env)
    (capacity : Nat) (hc : capacity=2^h) (b : MaskedTraversalEdge.Band h) (st : State C E h)
    (hv : st.Valid text fallback source env b.snapshot capacity b.hi)
    (hm : MaskedTraversalPositiveCoverage.Metadata text fallback capacity b) :
    (band env capacity b st).Valid text fallback source env b.crossing.state capacity (b.lo-1) := by
  let repaired:=MaskedTraversalRepairCoherence.apply env.repair b.snapshot capacity b.hi st.global.anchors st.frame.dirty st.global.store st.frame.tree
  let collected:=Collect.run B C E env.cut env.repair.shared repaired.store b.snapshot capacity repaired.tree
    (representative b) b.lo b.hi b.hi st.global.answers
  let z:=ReplayMaps.word C E (Spec.slice text.toList (representative b+(b.lo-1)) (representative b+b.hi))
  have prepared:=band_prepared text fallback source env hs capacity hc b st hv hm
  change Cells.Maintained _ _ _ _ _ repaired.anchors _ _ repaired.store repaired.tree ∧ _ at prepared
  have full:=hm.complete b.hi hm.valid.bounds (Nat.le_refl _)
  have maintained:=Collect.run_maintained B C E env.cut env.repair.shared repaired.store b.snapshot capacity
    (representative b) b.hi b.lo b.hi text.size repaired.anchors source repaired.tree st.global.answers
    hm.valid.invariant hc (ArrayText.read text fallback) full prepared.1
  change collected.band.repaired.ready=true ∧ Cells.Maintained _ _ _ _ _ _ _ collected.answers.history _ _ at maintained
  have av : MaskedTraversalAnswers.Valid text.size
      (fun p=>MaskedProgression.readMask source p=true ∧ Spec.maskedStart B C E text.toList
        (MaskedProgression.readMask env.repair.shared.target) p) collected.answers := by
    simpa only [collected,hs.cut,Array.length_toList] using
      Collect.run_answers_valid B C E env.repair.shared repaired.store b.snapshot capacity (representative b) b.hi b.lo b.hi
        repaired.anchors source repaired.tree st.global.answers text.toList fallback prepared.2.2
        (by simpa only [Array.length_toList] using prepared.1) hs.cRanges hs.eRanges hm.valid.bounds
        (by simpa only [Array.length_toList] using hv.global.answers)
  obtain ⟨valid,hn,hK,hg,entries,hr,hco,hcp,hl,hu⟩:=maintained.2
  have hle : b.lo-1≤b.hi := by have hh:=hm.valid.bounds; omega
  have hrep : representative b+b.hi≤text.toList.length := by simpa only [Array.length_toList] using hm.bounded
  have replayEq : (replay C E env.repair.shared.cRanges env.repair.shared.eRanges
      (representative b) (b.lo-1) b.hi).maps=z := by
    rw [hs.cRanges,hs.eRanges]
    exact replay_value C E text.toList (representative b) (b.lo-1) b.hi hle hrep
  have pending:=MaskedTraversalRepairTransport.crossing_pending env.repair capacity (representative b) b.hi (b.lo-1)
    b.snapshot repaired.anchors collected.band.repaired.store entries text.toList fallback
    hm.valid.invariant hm.valid.future hc (by simpa only [Array.toArray_toList,Array.length_toList] using full)
    (by simpa only [Array.toArray_toList,Array.length_toList] using prepared.2.1) hco hcp hl hs.cRanges hs.eRanges hle hrep
  have own:=MaskedTraversalRetained.crossing_away capacity text.size b.hi (b.lo-1) b.snapshot (ArrayText.read text fallback)
    repaired.anchors (MaskedTraversalDirty.empty h) (MaskedOrdered.State.empty_valid h)
    hm.valid.invariant hm.valid.future hc hle prepared.2.1
  have dv:=MaskedTraversalDirty.crossing_spec capacity b.hi (b.lo-1) b.snapshot b.crossing hm.valid.crossing
    (MaskedTraversalDirty.empty h) (MaskedOrdered.State.empty_valid h) hm.valid.invariant hm.valid.future hc hle
  have ds:=crossing_supported capacity b.hi (b.lo-1) b.snapshot (MaskedTraversalDirty.empty h)
    (MaskedOrdered.State.empty_valid h) hm.valid.invariant hm.valid.future hc hle (dirty_empty _)
  have supp:=coherent_supported env.repair.shared collected.band.repaired.store b.snapshot capacity b.hi entries
    hm.valid.invariant hc hco (ArrayText.read text fallback) text.size (representative b) full
  have hslots : text.size<collected.band.repaired.store.slots.size := by
    change text.size<(eraseMany env.repair.shared b.snapshot capacity b.hi collected.band.reported.starts repaired.store repaired.tree).store.slots.size
    rw [eraseMany_size,apply_size]
    exact hv.global.slots
  have hanchor : text.size<repaired.anchors.size := by rw [apply_anchor_size]; exact hv.global.anchors
  have runs : collected.band.repaired.store.sources.runs=
      (MaskedMutableProgression.Batch.prepare text fallback source env.repair.shared.prepared.K).runs := by
    rw [Collect.run_runs,apply_sources]
    exact hv.global.runs
  have good : (MaskedTraversalAggregate.shorten (bankAction z) collected.band.repaired.tree).1.Good :=
    Tree.reindex_good _ _ hg
  have represented:=Cells.shorten_represents z (b.lo-1) collected.band.repaired.tree entries hr
  have unclipped:=MaskedTraversalRepairTransport.reindexed_unclipped z (b.lo-1) text.size entries hu
  have supported:=supported_reindexed b.snapshot.occurrences.entries entries z (b.lo-1) supp
  change State.Valid text fallback source env b.crossing.state capacity (b.lo-1)
    ⟨⟨repaired.anchors,collected.band.repaired.store,collected.answers,_⟩,
      ⟨(MaskedTraversalAggregate.shorten (bankAction (replay C E env.repair.shared.cRanges env.repair.shared.eRanges
          (representative b) (b.lo-1) b.hi).maps) collected.band.repaired.tree).1,
        MaskedTraversalDirty.crossing b.snapshot b.crossing capacity (MaskedTraversalDirty.empty h)⟩⟩
  rw [replayEq,hm.valid.crossing]
  refine ⟨⟨valid,hn,hK,runs,hslots,hanchor,av⟩,?_,ds,good,own,
    entries.map (Cells.reindexedEntry z (b.lo-1)),represented,pending,unclipped,supported⟩
  simpa only [hm.valid.crossing] using dv.1

end REWB.MaskedTraversalExecute
