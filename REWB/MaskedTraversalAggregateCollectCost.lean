import REWB.MaskedTraversalAggregateCollect

/-! One output-sensitive charge for actual interval reporting, current
bank repair, answer-bit writes, and delivered mutable-source fanout. The
potential terms telescope over successive executed bands.
-/
namespace REWB.MaskedTraversalAggregate.Collect
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedTraversalAggregate.Cells
variable {α : Type} {h : Nat}

def repairBudget (C E : DFA α) (K h n : Nat) : Nat :=
  11*h+25+Mutable.Store.bankLimit C E K n+
    (h+1)*Tree.replaceBudget (2*ReplayMaps.count C.stateCount E.stateCount) (2*(MaskedClusterStage.dfa C E).stateCount)+
    MaskedMutableProgression.Batch.requestBudget n

theorem run_charged (B C E : DFA α) (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity base old lengthLo lengthHi : Nat)
    (anchors : Array (Option Nat)) (source : Array Bool) (tree : BankTree C E h) (answers : MaskedTraversalAnswers.State)
    (w : Word α) (fallback : α)
    (geometry : ∀L,lengthLo≤L→L≤lengthHi→BandGeometry w fallback partition capacity base old L anchors)
    (hm : Maintained env partition capacity old w.length anchors source answers.history st tree)
    (hc : env.cRanges=BoundaryApplication.Range.build C w) (he : env.eRanges=BoundaryApplication.Range.build E w)
    (hlength : lengthLo≤lengthHi) :
    let out:=run B C E (Cut.build B C E w) env st partition capacity tree base lengthLo lengthHi old answers
    let A:=Reporting.queryBudget B C E env.prepared.K h w.length
    MaskedReporting.totalWork out.band.reported+out.band.repaired.work+out.answers.work+
        out.band.repaired.store.sources.updateWork+st.sources.delivered*MaskedMutableProgression.Batch.rowBudget w.length≤
      answers.work+st.sources.updateWork+(A+1)+
        ((2*A+3)*h+repairBudget C E env.prepared.K h w.length+6)*out.band.reported.starts.length+
        out.band.repaired.store.sources.delivered*MaskedMutableProgression.Batch.rowBudget w.length := by
  have hr:=Reporting.run_charged B C E env st partition capacity base old lengthLo lengthHi anchors source answers.history tree
    w fallback geometry hm hc he hlength
  have hw:=run_added_work B C E (Cut.build B C E w) env st partition capacity tree base lengthLo lengthHi old answers
  dsimp only at hr hw ⊢
  change _≤_ at hr
  change _≤_
  simp only [run] at hw ⊢
  rw [hw]
  dsimp only [repairBudget]
  simp only [Nat.add_mul,Nat.mul_add,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] at hr ⊢
  omega

end REWB.MaskedTraversalAggregate.Collect
