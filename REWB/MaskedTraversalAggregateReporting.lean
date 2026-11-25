import REWB.MaskedTraversalAggregateEraseMany
import REWB.MaskedReporting

/-! Concrete band reporting and source removal. Queries share the actual
prepared cut index, source store and persistent aggregate. Reported
positions are then erased by the proved current-bank fold. Query units
sum the returned finite-table, shared-cut and scalar counters; the
pattern-only cost of a finite monoid operation remains a fixed factor.
The separate mutable-source fanout ledger is preserved in the result.
-/
namespace REWB.MaskedTraversalAggregate.Reporting
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedTraversalAggregate.Cells
variable {α : Type} {h : Nat}

def queryUnits (out : WindowResult) : Nat :=
  out.clippingWork+out.band.aggregateWork+out.band.closureProbes+out.band.cutProducts+
    out.band.cutVisits+out.band.cutProbes+out.band.arithmetic

def regionBudget (C E : DFA α) (h : Nat) : Nat :=
  4*(h+1)*Tree.queryBudget (2*ReplayMaps.count C.stateCount E.stateCount) (2*(MaskedClusterStage.dfa C E).stateCount)+
    3*ReplayMaps.count C.stateCount E.stateCount+
    2*(ReplayMaps.count C.stateCount E.stateCount*((2*(MaskedClusterStage.dfa C E).stateCount)*
      ((2*(MaskedClusterStage.dfa C E).stateCount)*((2*(MaskedClusterStage.dfa C E).stateCount)+1))))+8

def queryBudget (B C E : DFA α) (K h n : Nat) : Nat :=
  14*h+17+2*(Mutable.Store.bankLimit C E K n+
    (h+1)*Tree.replaceBudget (2*ReplayMaps.count C.stateCount E.stateCount) (2*(MaskedClusterStage.dfa C E).stateCount)+10)+
    regionBudget C E h+ReplayMaps.count C.stateCount E.stateCount*(E.stateCount+1)+3+3*(Nat.log2 n+2)+
    (MaskedCut.DFAIndex.jointEnum B C E).elems.length*(MaskedCut.DFAIndex.jointEnum B C E).elems.length+11

def ask (B C E : DFA α) (cut : Cut.Shared B C E) (env : Clip.Env C E)
    (st : Mutable.Store.State C E) (partition : MaskedClusterLeaders.State h) (capacity : Nat)
    (tree : BankTree C E h) (base lengthLo lengthHi old : Nat) : MaskedReporting.Query :=
  fun lo hi=>let out:=queryWindow B C E cut env st partition capacity tree lo hi base lengthLo lengthHi old
    ; (out.band.answer,queryUnits out)

theorem query_aggregate_work (B C E : DFA α) (cut : Cut.Shared B C E) (env : Clip.Env C E)
    (st : Mutable.Store.State C E) (partition : MaskedClusterLeaders.State h) (capacity : Nat)
    (tree : BankTree C E h) (lo hi base lengthLo lengthHi old : Nat) :
    (queryWindow B C E cut env st partition capacity tree lo hi base lengthLo lengthHi old).band.aggregateWork≤
      regionBudget C E h := by
  have hh:=region_work (Clip.window env st partition capacity old lo hi tree).update.tree
    (Clip.window env st partition capacity old lo hi tree).lower hi
  unfold queryWindow
  dsimp only
  split
  · exact hh
  · exact Nat.zero_le _

theorem ask_work (B C E : DFA α) (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity base old L lengthLo lengthHi lo hi : Nat)
    (anchors : Array (Option Nat)) (source : Array Bool) (removed : List Nat) (tree : BankTree C E h)
    (w : Word α) (fallback : α) (geometry : BandGeometry w fallback partition capacity base old L anchors)
    (hm : Maintained env partition capacity old w.length anchors source removed st tree)
    (hc : env.cRanges=BoundaryApplication.Range.build C w) (he : env.eRanges=BoundaryApplication.Range.build E w) :
    (ask B C E (Cut.build B C E w) env st partition capacity tree base lengthLo lengthHi old lo hi).2≤
      queryBudget B C E env.prepared.K h w.length := by
  obtain ⟨hv,hn,_,_,entries,_,hco,hcp,hl,_⟩:=hm
  have hclip:=queryWindow_actual_clipping_work B env st partition capacity base old L lo hi lengthLo lengthHi
    anchors tree entries hco hcp hl w fallback geometry source removed hv hn hc he
  have hag:=query_aggregate_work B C E (Cut.build B C E w) env st partition capacity tree lo hi base lengthLo lengthHi old
  have hb:=queryWindow_band_counters B C E w env st partition capacity tree lo hi base lengthLo lengthHi old
  simp only [ask,queryUnits,queryBudget]
  omega

structure Result (C E : DFA α) (h : Nat) where
  reported : MaskedReporting.Result
  repaired : SourceChange C E h

def run (B C E : DFA α) (cut : Cut.Shared B C E) (env : Clip.Env C E)
    (st : Mutable.Store.State C E) (partition : MaskedClusterLeaders.State h) (capacity : Nat)
    (tree : BankTree C E h) (base lengthLo lengthHi old : Nat) : Result C E h :=
  let reported:=MaskedReporting.report (ask B C E cut env st partition capacity tree base lengthLo lengthHi old) h 0
  let repaired:=eraseMany env partition capacity old reported.starts st tree
  ⟨reported,repaired⟩

theorem run_nodup (B C E : DFA α) (cut : Cut.Shared B C E) (env : Clip.Env C E)
    (st : Mutable.Store.State C E) (partition : MaskedClusterLeaders.State h) (capacity : Nat)
    (tree : BankTree C E h) (base lengthLo lengthHi old : Nat) :
    (run B C E cut env st partition capacity tree base lengthLo lengthHi old).reported.starts.Nodup :=
  MaskedReporting.report_nodup _ h 0

theorem run_maintained (B C E : DFA α) (cut : Cut.Shared B C E) (env : Clip.Env C E)
    (st : Mutable.Store.State C E) (partition : MaskedClusterLeaders.State h) (capacity base old lengthLo lengthHi n : Nat)
    (anchors : Array (Option Nat)) (source : Array Bool) (removed : List Nat) (tree : BankTree C E h)
    (hi : MaskedClusterLeaders.Invariant old partition) (hc : capacity=2^h)
    (f : Nat→α) (hfull : MaskedRunDiscovery.Complete f n base old partition.occurrences.entries)
    (hm : Maintained env partition capacity old n anchors source removed st tree) :
    let out:=run B C E cut env st partition capacity tree base lengthLo lengthHi old
    out.repaired.ready=true ∧ Maintained env partition capacity old n anchors source
      (out.reported.starts.reverse++removed) out.repaired.store out.repaired.tree :=
  eraseMany_maintained env partition capacity old n anchors source removed _ st tree hi hc f base hfull hm

theorem run_queryWork (B C E : DFA α) (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity base old L lengthLo lengthHi : Nat)
    (anchors : Array (Option Nat)) (source : Array Bool) (removed : List Nat) (tree : BankTree C E h)
    (w : Word α) (fallback : α) (geometry : BandGeometry w fallback partition capacity base old L anchors)
    (hm : Maintained env partition capacity old w.length anchors source removed st tree)
    (hc : env.cRanges=BoundaryApplication.Range.build C w) (he : env.eRanges=BoundaryApplication.Range.build E w) :
    let out:=run B C E (Cut.build B C E w) env st partition capacity tree base lengthLo lengthHi old
    out.reported.queryWork≤queryBudget B C E env.prepared.K h w.length*out.reported.calls :=
  MaskedReporting.report_queryWork _ _
    (fun lo hi=>ask_work B C E env st partition capacity base old L lengthLo lengthHi lo hi anchors source removed tree
      w fallback geometry hm hc he) h 0

end REWB.MaskedTraversalAggregate.Reporting
