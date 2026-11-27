import REWB.MaskedAllStartFullCostWindow
import REWB.MaskedAllStartFullCostReport
import REWB.MaskedAllStartFullCostErase
import REWB.MaskedTraversalAggregateCollect

/-! The actual reporting transaction with full primitive constructions.
It executes one reporter, one erase fold, and one answer push, and retains
their original complete result. The source-fanout ledger remains in the
returned store and is charged separately by the final solver. -/
namespace REWB.MaskedAllStart.FullCost.Transaction
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedTraversalAggregate
variable {α : Type} {C E : DFA α} {h : Nat}

def run (B C E : DFA α) (idx : Cut.Shared B C E) (env : Clip.Env C E)
    (st : Mutable.Store.State C E) (partition : MaskedClusterLeaders.State h) (capacity : Nat)
    (tree : BankTree C E h) (base lengthLo lengthHi old : Nat) : Bank.Result (Reporting.Result C E h) :=
  let ⟨reported,reportWork⟩:=Report.report
    (Query.ask B C E idx env st partition capacity tree base lengthLo lengthHi old) h 0
  let ⟨repaired,eraseWork⟩:=Erase.eraseMany env partition capacity old reported.starts st tree
  (⟨reported,repaired⟩,reportWork+eraseWork)

theorem run_value (B C E : DFA α) (idx : Cut.Shared B C E) (env : Clip.Env C E)
    (st : Mutable.Store.State C E) (partition : MaskedClusterLeaders.State h) (capacity : Nat)
    (tree : BankTree C E h) (base lengthLo lengthHi old : Nat) :
    (run B C E idx env st partition capacity tree base lengthLo lengthHi old).1=
      Reporting.run B C E idx env st partition capacity tree base lengthLo lengthHi old := by
  simp only [run,Reporting.run,Report.report_value,Query.ask_value,Erase.eraseMany_value]

def coefficient (B C E : DFA α) (K : Nat) : Nat := Query.coefficient B C E K+Bank.extra C E K+1

theorem coefficient_pos (B C E : DFA α) (K : Nat) : 1≤coefficient B C E K := by
  unfold coefficient
  omega

def units (out : Reporting.Result C E h) : Nat := Report.oldUnits out.reported+out.repaired.work

theorem run_work (B C E : DFA α) (idx : Cut.Shared B C E) (env : Clip.Env C E)
    (st : Mutable.Store.State C E) (partition : MaskedClusterLeaders.State h) (capacity : Nat)
    (tree : BankTree C E h) (base lengthLo lengthHi old : Nat)
    (ht : PeriodicConstruction.Cut.Tiny idx.tree) :
    (run B C E idx env st partition capacity tree base lengthLo lengthHi old).2≤
      coefficient B C E env.prepared.K*units
        (run B C E idx env st partition capacity tree base lengthLo lengthHi old).1 := by
  have hr:=Report.report_work
    (Query.ask B C E idx env st partition capacity tree base lengthLo lengthHi old)
    (Query.coefficient B C E env.prepared.K) (Query.coefficient_pos B C E env.prepared.K)
    (fun lo hi=>Query.ask_work B C E idx env st partition capacity tree base lengthLo lengthHi old lo hi ht) h 0
  have he:=Erase.eraseMany_work env partition capacity old
    (Report.report (Query.ask B C E idx env st partition capacity tree base lengthLo lengthHi old) h 0).1.starts st tree
  have hrc:=Nat.mul_le_mul_right
    (Report.oldUnits (Report.report (Query.ask B C E idx env st partition capacity tree base lengthLo lengthHi old) h 0).1)
    (show Query.coefficient B C E env.prepared.K≤coefficient B C E env.prepared.K by unfold coefficient; omega)
  have hec:=Nat.mul_le_mul_right
    (Erase.eraseMany env partition capacity old
      (Report.report (Query.ask B C E idx env st partition capacity tree base lengthLo lengthHi old) h 0).1.starts st tree).1.work
    (show Bank.extra C E env.prepared.K+1≤coefficient B C E env.prepared.K by unfold coefficient; omega)
  simp only [run,units,Nat.mul_add]
  omega

def collect (B C E : DFA α) (idx : Cut.Shared B C E) (env : Clip.Env C E)
    (st : Mutable.Store.State C E) (partition : MaskedClusterLeaders.State h) (capacity : Nat)
    (tree : BankTree C E h) (base lengthLo lengthHi old : Nat) (answers : MaskedTraversalAnswers.State) :
    Bank.Result (Collect.Result C E h) :=
  let beforeWork:=answers.work
  let ⟨⟨reported,repaired⟩,runWork⟩:=run B C E idx env st partition capacity tree base lengthLo lengthHi old
  let next:=MaskedTraversalAnswers.push reported.starts answers
  (⟨⟨reported,repaired⟩,next⟩,runWork+(next.work-beforeWork))

theorem collect_value (B C E : DFA α) (idx : Cut.Shared B C E) (env : Clip.Env C E)
    (st : Mutable.Store.State C E) (partition : MaskedClusterLeaders.State h) (capacity : Nat)
    (tree : BankTree C E h) (base lengthLo lengthHi old : Nat) (answers : MaskedTraversalAnswers.State) :
    (collect B C E idx env st partition capacity tree base lengthLo lengthHi old answers).1=
      Collect.run B C E idx env st partition capacity tree base lengthLo lengthHi old answers := by
  simp only [collect,Collect.run,run_value]

def collectUnits (out : Collect.Result C E h) (beforeWork : Nat) : Nat :=
  units out.band+(out.answers.work-beforeWork)

theorem collect_work (B C E : DFA α) (idx : Cut.Shared B C E) (env : Clip.Env C E)
    (st : Mutable.Store.State C E) (partition : MaskedClusterLeaders.State h) (capacity : Nat)
    (tree : BankTree C E h) (base lengthLo lengthHi old : Nat) (answers : MaskedTraversalAnswers.State)
    (ht : PeriodicConstruction.Cut.Tiny idx.tree) :
    (collect B C E idx env st partition capacity tree base lengthLo lengthHi old answers).2≤
      coefficient B C E env.prepared.K*collectUnits
        (collect B C E idx env st partition capacity tree base lengthLo lengthHi old answers).1 answers.work := by
  have hr:=run_work B C E idx env st partition capacity tree base lengthLo lengthHi old ht
  have hs:=Nat.mul_le_mul_right
    ((MaskedTraversalAnswers.push (run B C E idx env st partition capacity tree base lengthLo lengthHi old).1.reported.starts answers).work-answers.work)
    (coefficient_pos B C E env.prepared.K)
  have hh:=Nat.add_le_add hr hs
  simpa only [collect,collectUnits,units,Nat.mul_add,Nat.one_mul] using hh

end REWB.MaskedAllStart.FullCost.Transaction
