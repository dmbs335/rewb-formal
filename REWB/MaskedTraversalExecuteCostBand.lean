import REWB.MaskedTraversalExecuteCostEvents
import REWB.MaskedTraversalExecuteBand
import REWB.MaskedTraversalRepairSnapshotCost
import REWB.MaskedTraversalAggregateCollectCost

/-! One concrete band pays for every actual repair, interval query,
answer write, source erase, lazy replay and subsequent dirty collection.
The pending-key potential and delivered-fanout/output credits are kept
on opposite sides so they telescope through the real sequential plan.
Fixed-pattern action construction calls remain separately counted by the
executor's actionBuilds field. -/
namespace REWB.MaskedTraversalExecute.Cost
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedTraversalAggregate
open REWB.MaskedTraversalRepairCoherence
variable {α : Type} {σ h : Nat} {B C E : DFA (Fin σ)}

def actualWork (global : Global C E) : Nat := global.stats.work+global.store.sources.updateWork
def credit (rowUnit outputUnit : Nat) (global : Global C E) : Nat :=
  global.store.sources.delivered*rowUnit+outputUnit*global.stats.reported
def held (repairUnit : Nat) (frame : Frame C E h) : Nat := repairUnit*frame.dirty.keys.positions.length

def replayBudget (C E : DFA α) (n : Nat) : Nat := C.stateCount+E.stateCount+16*(n.log2+2)+6
def bandBudget (B C E : DFA α) (K h n : Nat) : Nat :=
  Reporting.queryBudget B C E K h n+replayBudget C E n+
    Tree.reindexBudget (2*ReplayMaps.count C.stateCount E.stateCount) (2*(MaskedClusterStage.dfa C E).stateCount)+62
def outputBudget (B C E : DFA α) (K h n : Nat) : Nat :=
  (2*Reporting.queryBudget B C E K h n+41)*h+Collect.repairBudget C E K h n+6

theorem band_charged (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool)
    (env : Env B C E text.size (MaskedSuffixClass.height text.size)) (hs : Static text fallback source env)
    (capacity : Nat) (hc : capacity=2^h) (b : MaskedTraversalEdge.Band h) (st : State C E h)
    (hv : st.Valid text fallback source env b.snapshot capacity b.hi)
    (hm : MaskedTraversalPositiveCoverage.Metadata text fallback capacity b) :
    let out:=band env capacity b st
    let D:=MaskedTraversalRepairCoherence.repairBudget C E env.repair.shared.prepared.K text.size h
    let R:=MaskedMutableProgression.Batch.rowBudget text.size
    let U:=outputBudget B C E env.repair.shared.prepared.K h text.size
    actualWork out.global+credit R U st.global+held D out.frame≤
      actualWork st.global+credit R U out.global+held D st.frame+
        markBudget h D*b.crossing.live.length+bandBudget B C E env.repair.shared.prepared.K h text.size := by
  let D:=MaskedTraversalRepairCoherence.repairBudget C E env.repair.shared.prepared.K text.size h
  let R:=MaskedMutableProgression.Batch.rowBudget text.size
  let A:=Reporting.queryBudget B C E env.repair.shared.prepared.K h text.size
  let Q:=Collect.repairBudget C E env.repair.shared.prepared.K h text.size
  let P:=replayBudget C E text.size
  let S:=Tree.reindexBudget (2*ReplayMaps.count C.stateCount E.stateCount) (2*(MaskedClusterStage.dfa C E).stateCount)
  let repaired:=MaskedTraversalRepairCoherence.apply env.repair b.snapshot capacity b.hi st.global.anchors
    st.frame.dirty st.global.store st.frame.tree
  let collected:=Collect.run B C E env.cut env.repair.shared repaired.store b.snapshot capacity
    repaired.tree (representative b) b.lo b.hi b.hi st.global.answers
  let replayed:=replay C E env.repair.shared.cRanges env.repair.shared.eRanges (representative b) (b.lo-1) b.hi
  let shortened:=MaskedTraversalAggregate.shorten (bankAction replayed.maps) collected.band.repaired.tree
  let dirty:=MaskedTraversalDirty.crossing b.snapshot b.crossing capacity (MaskedTraversalDirty.empty h)
  obtain ⟨entries,_,pending,_,_⟩:=hv.entries
  have snap:=snapshot text fallback source env hs capacity hc b st hv.global hm
  have repairCost : repaired.work≤D*st.frame.dirty.keys.positions.length+16 :=
    apply_snapshot_work C E text fallback source st.global.answers.history env.repair b.snapshot capacity b.hi
      (representative b) st.global.store snap hs.cRanges hs.eRanges st.global.anchors st.frame.dirty st.frame.tree
      pending.raw hv.own hv.global.anchors
  have prepared:=band_prepared text fallback source env hs capacity hc b st hv hm
  change Cells.Maintained _ _ _ _ _ repaired.anchors _ _ repaired.store repaired.tree ∧ _ at prepared
  have collectCost : MaskedReporting.totalWork collected.band.reported+collected.band.repaired.work+
      collected.answers.work+collected.band.repaired.store.sources.updateWork+repaired.store.sources.delivered*R≤
    st.global.answers.work+repaired.store.sources.updateWork+(A+1)+
      ((2*A+3)*h+Q+6)*collected.band.reported.starts.length+
        collected.band.repaired.store.sources.delivered*R := by
    simpa only [collected,hs.cut,Array.length_toList] using
      Collect.run_charged B C E env.repair.shared repaired.store b.snapshot capacity (representative b) b.hi b.lo b.hi
        repaired.anchors source repaired.tree st.global.answers text.toList fallback prepared.2.2
        (by simpa only [Array.length_toList] using prepared.1) hs.cRanges hs.eRanges hm.valid.bounds
  have calls : collected.band.reported.calls≤1+2*h*collected.band.reported.starts.length := by
    simpa only [collected,Collect.run,hs.cut] using
      Reporting.run_calls B C E env.repair.shared repaired.store b.snapshot capacity (representative b) b.hi b.lo b.hi
        repaired.anchors source st.global.answers.history repaired.tree text.toList fallback prepared.2.2
        (by simpa only [Array.length_toList] using prepared.1) hs.cRanges hs.eRanges hm.valid.bounds
  have counted : collected.band.reported.count=collected.band.reported.starts.length :=
    MaskedReporting.report_count _ h 0
  have writes : collected.answers.work=st.global.answers.work+6*collected.band.reported.starts.length :=
    Collect.run_added_work B C E env.cut env.repair.shared repaired.store b.snapshot capacity repaired.tree
      (representative b) b.lo b.hi b.hi st.global.answers
  have sources : repaired.store.sources=st.global.store.sources :=
    apply_sources env.repair b.snapshot capacity b.hi st.global.anchors st.frame.dirty st.global.store st.frame.tree
  rw [sources] at collectCost
  have replayCost : replayed.work≤P := by
    have hh:=(replay_bounds C E text.toList (representative b) (b.lo-1) b.hi
      (by have hbound:=hm.valid.bounds; omega) (by simpa only [Array.length_toList] using hm.bounded)).2.2
    simpa only [replayed,hs.cRanges,hs.eRanges,Array.length_toList] using hh
  have shortenCost : shortened.2≤S := Tree.reindex_steps _ _
  have dirtyCost : dirty.work+D*dirty.keys.positions.length≤markBudget h D*b.crossing.live.length+2 :=
    crossing_fresh b.snapshot b.crossing capacity D
  have callsCost:=Nat.mul_le_mul_left 19 calls
  change (st.global.stats.work+repaired.work+collected.band.reported.queryWork+
      collected.band.reported.copies+20*collected.band.reported.calls+collected.band.repaired.work+
      (collected.answers.work-st.global.answers.work)+replayed.work+shortened.2+dirty.work+24+
      collected.band.repaired.store.sources.updateWork)+
      (st.global.store.sources.delivered*R+((2*A+41)*h+Q+6)*st.global.stats.reported)+
      D*dirty.keys.positions.length≤
    (st.global.stats.work+st.global.store.sources.updateWork)+
      (collected.band.repaired.store.sources.delivered*R+((2*A+41)*h+Q+6)*
        (st.global.stats.reported+collected.band.reported.count))+
      D*st.frame.dirty.keys.positions.length+markBudget h D*b.crossing.live.length+(A+P+S+62)
  rw [counted]
  simp only [MaskedReporting.totalWork,Nat.mul_add,Nat.add_mul,Nat.mul_assoc] at collectCost callsCost ⊢
  omega

end REWB.MaskedTraversalExecute.Cost
