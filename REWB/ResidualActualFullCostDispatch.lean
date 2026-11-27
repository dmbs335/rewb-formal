import REWB.ResidualActualFullCostInputs
import REWB.ResidualActualPeriodic
import REWB.ResidualActualFullCostCached

/-! Actual construction-counted residual dispatch. Each finite input bank
is produced once through FullCost.inputs, and its stored bits feed the
primitive-refined periodic cached dispatcher. Original answers are preserved.
The counters include the new row and periodic construction operations;
inherited transition/comparison primitives keep their documented scope. -/
namespace REWB.ResidualActual.FullCost
variable {σ : Nat}

structure Execution where
  cached : Periodic.Cached.Execution
  inputWork : Nat
  fixedPatternBuilds : Nat

def Execution.answer (out : Execution) : Bool := out.cached.answer
def Execution.accountedWork (out : Execution) : Nat := out.cached.accountedWork+out.inputWork+2

namespace P1

def execute (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) : Execution :=
  let rows:=inputs P text.toList fallback s
  let cached:=Cached.P1.execute P text fallback s L D Q hs rows.1.bits
  ⟨cached,rows.2+text.size+5,rows.1.fixedPatternBuilds⟩

theorem execute_answer (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) :
    (execute P text fallback s L D Q hs).answer=
      (Periodic.P1.execute P text fallback s L D Q hs).answer := by
  simp only [execute,Execution.answer,inputs_value,Cached.P1.execute_answer,
    Periodic.P1.execute,Periodic.Execution.answer]

theorem execute_correct (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) (hSL : s≤L) (hD : 0<D) (hQL : Q≤L) :
    (execute P text fallback s L D Q hs).answer=true ↔ MatchesWithin P.nested1 text.toList 2 := by
  rw [execute_answer]
  exact Periodic.P1.execute_correct P text fallback s L D Q hs hSL hD hQL

theorem execute_inputWork (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) :
    (execute P text fallback s L D Q hs).inputWork=
      (inputs P text.toList fallback s).2+text.size+5 := rfl

theorem execute_builds (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) :
    (execute P text fallback s L D Q hs).fixedPatternBuilds=
      (Periodic.P1.execute P text fallback s L D Q hs).fixedPatternBuilds := by
  simp only [execute,inputs_value,Periodic.P1.execute]

theorem execute_work_le_base (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) :
    (execute P text fallback s L D Q hs).accountedWork≤
      (Periodic.P1.execute P text fallback s L D Q hs).accountedWork+
        (inputs P text.toList fallback s).2+
        (PeriodicActual.FullCost.Cubic.solve P (ArrayText.read text fallback) text.size Q).2 := by
  have hc:=Cached.P1.execute_work_le_old P text fallback s L D Q hs
    (inputs P text.toList fallback s).1.bits
  simp only [inputs_value] at hc
  unfold Execution.accountedWork execute Periodic.Execution.accountedWork Periodic.P1.execute
  simp only [inputs_value]
  omega

def auto (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) : Execution :=
  execute P text fallback (ThresholdBudget.block text.size) (ThresholdBudget.length text.size)
    (ThresholdBudget.length text.size) (ThresholdBudget.period text.size) (ResidualCached.parameters text.size).1

theorem auto_answer (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) :
    (auto P text fallback).answer=(Periodic.P1.auto P text fallback).answer :=
  execute_answer P text fallback _ _ _ _ _

theorem auto_correct (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) :
    (auto P text fallback).answer=true ↔ MatchesWithin P.nested1 text.toList 2 := by
  rw [auto_answer]
  exact Periodic.P1.auto_correct P text fallback

theorem auto_builds (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) :
    (auto P text fallback).fixedPatternBuilds=(Periodic.P1.auto P text fallback).fixedPatternBuilds :=
  execute_builds P text fallback _ _ _ _ _

theorem auto_work_le_base (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) :
    (auto P text fallback).accountedWork≤
      (Periodic.P1.auto P text fallback).accountedWork+
        (inputs P text.toList fallback (ThresholdBudget.block text.size)).2+
        (PeriodicActual.FullCost.Cubic.solve P (ArrayText.read text fallback) text.size
          (ThresholdBudget.period text.size)).2 :=
  execute_work_le_base P text fallback _ _ _ _ _

end P1

namespace P2

def execute (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) : Execution :=
  let rows:=inputs P text.toList fallback s
  let cached:=Cached.P2.execute P text fallback s L D Q hs rows.1.bits
  ⟨cached,rows.2+text.size+5,rows.1.fixedPatternBuilds⟩

theorem execute_answer (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) :
    (execute P text fallback s L D Q hs).answer=
      (Periodic.P2.execute P text fallback s L D Q hs).answer := by
  simp only [execute,Execution.answer,inputs_value,Cached.P2.execute_answer,
    Periodic.P2.execute,Periodic.Execution.answer]

theorem execute_correct (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) (hSL : s≤L) (hD : 0<D) (hQL : Q≤L) :
    (execute P text fallback s L D Q hs).answer=true ↔ MatchesWithin P.nested2 text.toList 2 := by
  rw [execute_answer]
  exact Periodic.P2.execute_correct P text fallback s L D Q hs hSL hD hQL

theorem execute_inputWork (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) :
    (execute P text fallback s L D Q hs).inputWork=
      (inputs P text.toList fallback s).2+text.size+5 := rfl

theorem execute_builds (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) :
    (execute P text fallback s L D Q hs).fixedPatternBuilds=
      (Periodic.P2.execute P text fallback s L D Q hs).fixedPatternBuilds := by
  simp only [execute,inputs_value,Periodic.P2.execute]

theorem execute_work_le_base (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) :
    (execute P text fallback s L D Q hs).accountedWork≤
      (Periodic.P2.execute P text fallback s L D Q hs).accountedWork+
        (inputs P text.toList fallback s).2+
        (PeriodicActual.FullCost.P2.solve P (ArrayText.read text fallback) text.size Q).2 := by
  have hc:=Cached.P2.execute_work_le_old P text fallback s L D Q hs
    (inputs P text.toList fallback s).1.bits
  simp only [inputs_value] at hc
  unfold Execution.accountedWork execute Periodic.Execution.accountedWork Periodic.P2.execute
  simp only [inputs_value]
  omega

def auto (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) : Execution :=
  execute P text fallback (ThresholdBudget.block text.size) (ThresholdBudget.length text.size)
    (ThresholdBudget.length text.size) (ThresholdBudget.period text.size) (ResidualCached.parameters text.size).1

theorem auto_answer (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) :
    (auto P text fallback).answer=(Periodic.P2.auto P text fallback).answer :=
  execute_answer P text fallback _ _ _ _ _

theorem auto_correct (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) :
    (auto P text fallback).answer=true ↔ MatchesWithin P.nested2 text.toList 2 := by
  rw [auto_answer]
  exact Periodic.P2.auto_correct P text fallback

theorem auto_builds (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) :
    (auto P text fallback).fixedPatternBuilds=(Periodic.P2.auto P text fallback).fixedPatternBuilds :=
  execute_builds P text fallback _ _ _ _ _

theorem auto_work_le_base (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) :
    (auto P text fallback).accountedWork≤
      (Periodic.P2.auto P text fallback).accountedWork+
        (inputs P text.toList fallback (ThresholdBudget.block text.size)).2+
        (PeriodicActual.FullCost.P2.solve P (ArrayText.read text fallback) text.size
          (ThresholdBudget.period text.size)).2 :=
  execute_work_le_base P text fallback _ _ _ _ _

end P2

end REWB.ResidualActual.FullCost
