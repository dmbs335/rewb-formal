import REWB.MaskedAllStartFullCostRepair
import REWB.MaskedAllStartFullCostCollect
import REWB.MaskedTraversalExecuteRuntime

/-! One actual executor band with all finite formula, replay-action and
joint-cut constructors installed. Explicit destructuring consumes the
repair/report results once; no original report is rerun to recover a
projection. The whole original State, including every old ledger, is
preserved. The expanded ledger is bounded by its actual work increment.
-/
namespace REWB.MaskedAllStart.FullCost.Execution
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedTraversalAggregate
open REWB.MaskedTraversalExecute
variable {α : Type} {B C E : DFA α} {h n h' : Nat}

def coefficient (B C E : DFA α) (K : Nat) : Nat :=
  Repair.factor C E K+Transaction.coefficient B C E K+
    MaskedFiniteConstruction.bankActionBudget C.stateCount E.stateCount+1

theorem coefficient_pos (B C E : DFA α) (K : Nat) : 1≤coefficient B C E K := by
  unfold coefficient
  omega

def band (env : Env B C E n h') (capacity : Nat) (b : MaskedTraversalEdge.Band h)
    (st : MaskedTraversalExecute.State C E h) : Bank.Result (MaskedTraversalExecute.State C E h) :=
  let oldStats:=st.global.stats
  let oldAnswerWork:=st.global.answers.work
  let ⟨⟨anchors,store,tree,_,repairUnits⟩,repairWork⟩:=Repair.apply env.repair b.snapshot capacity b.hi
    st.global.anchors st.frame.dirty st.global.store st.frame.tree
  let base:=representative b
  let ⟨⟨⟨reported,⟨afterStore,afterTree,_,eraseUnits,_⟩⟩,answers⟩,collectWork⟩:=
    Transaction.collect B C E env.cut env.repair.shared store b.snapshot capacity tree
      base b.lo b.hi b.hi st.global.answers
  let replayed:=replay C E env.repair.shared.cRanges env.repair.shared.eRanges base (b.lo-1) b.hi
  let ⟨action,actionWork⟩:=MaskedFiniteConstruction.bankAction replayed.maps
  let ⟨shortened,shortenWork⟩:=MaskedTraversalAggregate.shorten action afterTree
  let dirty:=MaskedTraversalDirty.crossing b.snapshot b.crossing capacity (MaskedTraversalDirty.empty h)
  let oldWork:=oldStats.work+repairUnits+reported.queryWork+reported.copies+20*reported.calls+eraseUnits+
    (answers.work-oldAnswerWork)+replayed.work+shortenWork+dirty.work+24
  (⟨⟨anchors,afterStore,answers,
      ⟨oldWork,oldStats.bands+1,oldStats.queryCalls+reported.calls,
        oldStats.reported+reported.count,oldStats.actionBuilds+1⟩⟩,
    ⟨shortened,dirty⟩⟩,
    repairWork+collectWork+replayed.work+actionWork+shortenWork+dirty.work+24)

theorem band_value (env : Env B C E n h') (capacity : Nat) (b : MaskedTraversalEdge.Band h)
    (st : MaskedTraversalExecute.State C E h) : (band env capacity b st).1=MaskedTraversalExecute.band env capacity b st := by
  simp only [band,MaskedTraversalExecute.band,Repair.apply_value,Transaction.collect_value,
    MaskedFiniteConstruction.bankAction_value]

theorem band_credit (env : Env B C E n h') (capacity : Nat) (b : MaskedTraversalEdge.Band h)
    (st : MaskedTraversalExecute.State C E h) (ht : PeriodicConstruction.Cut.Tiny env.cut.tree) :
    (band env capacity b st).2+coefficient B C E env.repair.shared.prepared.K*st.global.stats.work≤
      coefficient B C E env.repair.shared.prepared.K*(band env capacity b st).1.global.stats.work := by
  let repaired:=Repair.apply env.repair b.snapshot capacity b.hi st.global.anchors
    st.frame.dirty st.global.store st.frame.tree
  let collected:=Transaction.collect B C E env.cut env.repair.shared repaired.1.store b.snapshot capacity
    repaired.1.tree (representative b) b.lo b.hi b.hi st.global.answers
  let replayed:=replay C E env.repair.shared.cRanges env.repair.shared.eRanges (representative b) (b.lo-1) b.hi
  let action:=MaskedFiniteConstruction.bankAction replayed.maps
  let shortened:=MaskedTraversalAggregate.shorten action.1 collected.1.band.repaired.tree
  let dirty:=MaskedTraversalDirty.crossing b.snapshot b.crossing capacity (MaskedTraversalDirty.empty h)
  let F:=coefficient B C E env.repair.shared.prepared.K
  have hr : repaired.2≤Repair.factor C E env.repair.shared.prepared.K*repaired.1.work :=
    Repair.apply_work _ _ _ _ _ _ _ _
  have hc : collected.2≤Transaction.coefficient B C E env.repair.shared.prepared.K*
      Transaction.collectUnits collected.1 st.global.answers.work :=
    Transaction.collect_work _ _ _ _ _ _ _ _ _ _ _ _ _ _ ht
  have hrf:=Nat.mul_le_mul_right repaired.1.work
    (show Repair.factor C E env.repair.shared.prepared.K≤F by dsimp only [F,coefficient]; omega)
  have hcf:=Nat.mul_le_mul_right (Transaction.collectUnits collected.1 st.global.answers.work)
    (show Transaction.coefficient B C E env.repair.shared.prepared.K≤F by dsimp only [F,coefficient]; omega)
  have ha : action.2≤MaskedFiniteConstruction.bankActionBudget C.stateCount E.stateCount :=
    MaskedFiniteConstruction.bankAction_work replayed.maps
  have hs:=Nat.mul_le_mul_right (replayed.work+shortened.2+dirty.work)
    (coefficient_pos B C E env.repair.shared.prepared.K)
  have hk : MaskedFiniteConstruction.bankActionBudget C.stateCount E.stateCount+24≤F*24 := by
    dsimp only [F,coefficient]
    omega
  change repaired.2+collected.2+replayed.work+action.2+shortened.2+dirty.work+24+
      F*st.global.stats.work≤
    F*(st.global.stats.work+repaired.1.work+collected.1.band.reported.queryWork+
      collected.1.band.reported.copies+20*collected.1.band.reported.calls+collected.1.band.repaired.work+
      (collected.1.answers.work-st.global.answers.work)+replayed.work+shortened.2+dirty.work+24)
  simp only [Nat.one_mul] at hs
  change replayed.work+shortened.2+dirty.work≤F*(replayed.work+shortened.2+dirty.work) at hs
  simp only [Transaction.collectUnits,Transaction.units,Report.oldUnits,Nat.mul_add,Nat.one_mul] at hc hcf hs ⊢
  omega

theorem band_mono (env : Env B C E n h') (capacity : Nat) (b : MaskedTraversalEdge.Band h)
    (st : MaskedTraversalExecute.State C E h) : st.global.stats.work≤(band env capacity b st).1.global.stats.work := by
  simp only [band_value,MaskedTraversalExecute.band]
  omega

theorem band_work (env : Env B C E n h') (capacity : Nat) (b : MaskedTraversalEdge.Band h)
    (st : MaskedTraversalExecute.State C E h) (ht : PeriodicConstruction.Cut.Tiny env.cut.tree) :
    (band env capacity b st).2≤coefficient B C E env.repair.shared.prepared.K*
      ((band env capacity b st).1.global.stats.work-st.global.stats.work) := by
  have hh:=band_credit env capacity b st ht
  have he:=Nat.sub_add_cancel (band_mono env capacity b st)
  have hm:=congrArg (fun x=>coefficient B C E env.repair.shared.prepared.K*x) he
  simp only [Nat.mul_add] at hm
  omega

end REWB.MaskedAllStart.FullCost.Execution
