import REWB.ResidualActualPeriodicCached
import REWB.ResidualActualDispatch

/-! Actual finite-row construction followed by the periodic-construction
refinement.  The caller supplies only the pattern, text, fallback and
numeric thresholds.  This layer uses the existing actual row producer
once; its row-construction ledger keeps its existing stated scope.
The cached layer also accepts the refined full-cost row producer. -/
namespace REWB.ResidualActual.Periodic
variable {σ : Nat}

structure Execution where
  cached : Cached.Execution
  inputWork : Nat
  fixedPatternBuilds : Nat

def Execution.answer (out : Execution) : Bool := out.cached.answer
def Execution.accountedWork (out : Execution) : Nat := out.cached.accountedWork+out.inputWork+2

namespace P1

def execute (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) : Execution :=
  let rows:=ResidualActual.P1.inputs P text.toList fallback s
  let cached:=Cached.P1.execute P text fallback s L D Q hs rows.bits
  ⟨cached,rows.work+text.size+5,rows.fixedPatternBuilds⟩

theorem execute_answer (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) :
    (execute P text fallback s L D Q hs).answer=
      (ResidualActual.P1.execute P text fallback s L D Q hs).answer := by
  change (Cached.P1.execute P text fallback s L D Q hs
    (ResidualActual.P1.inputs P text.toList fallback s).bits).answer=
      (ResidualCached.P1.execute P text fallback s L D Q hs
        (ResidualActual.P1.inputs P text.toList fallback s).bits).answer
  exact Cached.P1.execute_answer P text fallback s L D Q hs _

theorem execute_correct (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) (hSL : s≤L) (hD : 0<D) (hQL : Q≤L) :
    (execute P text fallback s L D Q hs).answer=true ↔ MatchesWithin P.nested1 text.toList 2 := by
  rw [execute_answer]
  exact ResidualActual.P1.execute_correct P text fallback s L D Q hs hSL hD hQL

theorem execute_inputWork (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) :
    (execute P text fallback s L D Q hs).inputWork=
      (ResidualActual.P1.execute P text fallback s L D Q hs).inputWork := rfl

theorem execute_builds (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) :
    (execute P text fallback s L D Q hs).fixedPatternBuilds=
      (ResidualActual.P1.execute P text fallback s L D Q hs).fixedPatternBuilds := rfl

theorem execute_work_le_old (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) :
    (execute P text fallback s L D Q hs).accountedWork≤
      (ResidualActual.P1.execute P text fallback s L D Q hs).accountedWork+
        (PeriodicActual.Cubic.solve P (ArrayText.read text fallback) text.size Q).2 := by
  have h:=Cached.P1.execute_work_le_old P text fallback s L D Q hs
    (ResidualActual.P1.inputs P text.toList fallback s).bits
  unfold Execution.accountedWork execute ResidualActual.P1.Execution.accountedWork
    ResidualActual.P1.execute
  dsimp only
  omega

def auto (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) : Execution :=
  execute P text fallback (ThresholdBudget.block text.size) (ThresholdBudget.length text.size)
    (ThresholdBudget.length text.size) (ThresholdBudget.period text.size) (ResidualCached.parameters text.size).1

theorem auto_answer (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) :
    (auto P text fallback).answer=(ResidualActual.P1.auto P text fallback).answer :=
  execute_answer P text fallback _ _ _ _ _

theorem auto_correct (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) :
    (auto P text fallback).answer=true ↔ MatchesWithin P.nested1 text.toList 2 := by
  rw [auto_answer]
  exact ResidualActual.P1.auto_correct P text fallback

theorem auto_builds (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) :
    (auto P text fallback).fixedPatternBuilds=(ResidualActual.P1.auto P text fallback).fixedPatternBuilds := rfl

theorem auto_work_le_old (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) :
    (auto P text fallback).accountedWork≤
      (ResidualActual.P1.auto P text fallback).accountedWork+
        (PeriodicActual.Cubic.solve P (ArrayText.read text fallback) text.size
          (ThresholdBudget.period text.size)).2 :=
  execute_work_le_old P text fallback _ _ _ _ _

end P1

namespace P2

def execute (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) : Execution :=
  let rows:=ResidualActual.P2.inputs P text.toList fallback s
  let cached:=Cached.P2.execute P text fallback s L D Q hs rows.bits
  ⟨cached,rows.work+text.size+5,rows.fixedPatternBuilds⟩

theorem execute_answer (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) :
    (execute P text fallback s L D Q hs).answer=
      (ResidualActual.P2.execute P text fallback s L D Q hs).answer := by
  change (Cached.P2.execute P text fallback s L D Q hs
    (ResidualActual.P2.inputs P text.toList fallback s).bits).answer=
      (ResidualCached.P2.execute P text fallback s L D Q hs
        (ResidualActual.P2.inputs P text.toList fallback s).bits).answer
  exact Cached.P2.execute_answer P text fallback s L D Q hs _

theorem execute_correct (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) (hSL : s≤L) (hD : 0<D) (hQL : Q≤L) :
    (execute P text fallback s L D Q hs).answer=true ↔ MatchesWithin P.nested2 text.toList 2 := by
  rw [execute_answer]
  exact ResidualActual.P2.execute_correct P text fallback s L D Q hs hSL hD hQL

theorem execute_inputWork (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) :
    (execute P text fallback s L D Q hs).inputWork=
      (ResidualActual.P2.execute P text fallback s L D Q hs).inputWork := rfl

theorem execute_builds (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) :
    (execute P text fallback s L D Q hs).fixedPatternBuilds=
      (ResidualActual.P2.execute P text fallback s L D Q hs).fixedPatternBuilds := rfl

theorem execute_work_le_old (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) :
    (execute P text fallback s L D Q hs).accountedWork≤
      (ResidualActual.P2.execute P text fallback s L D Q hs).accountedWork+
        (PeriodicActual.P2.solve P (ArrayText.read text fallback) text.size Q).2 := by
  have h:=Cached.P2.execute_work_le_old P text fallback s L D Q hs
    (ResidualActual.P2.inputs P text.toList fallback s).bits
  unfold Execution.accountedWork execute ResidualActual.P2.Execution.accountedWork
    ResidualActual.P2.execute
  dsimp only
  omega

def auto (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) : Execution :=
  execute P text fallback (ThresholdBudget.block text.size) (ThresholdBudget.length text.size)
    (ThresholdBudget.length text.size) (ThresholdBudget.period text.size) (ResidualCached.parameters text.size).1

theorem auto_answer (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) :
    (auto P text fallback).answer=(ResidualActual.P2.auto P text fallback).answer :=
  execute_answer P text fallback _ _ _ _ _

theorem auto_correct (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) :
    (auto P text fallback).answer=true ↔ MatchesWithin P.nested2 text.toList 2 := by
  rw [auto_answer]
  exact ResidualActual.P2.auto_correct P text fallback

theorem auto_builds (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) :
    (auto P text fallback).fixedPatternBuilds=(ResidualActual.P2.auto P text fallback).fixedPatternBuilds := rfl

theorem auto_work_le_old (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) :
    (auto P text fallback).accountedWork≤
      (ResidualActual.P2.auto P text fallback).accountedWork+
        (PeriodicActual.P2.solve P (ArrayText.read text fallback) text.size
          (ThresholdBudget.period text.size)).2 :=
  execute_work_le_old P text fallback _ _ _ _ _

end P2

end REWB.ResidualActual.Periodic
