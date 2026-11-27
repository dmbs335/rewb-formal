import REWB.ResidualActualRows
import REWB.ResidualCachedAuto

/-! End-to-end separated residual dispatch. The only runtime inputs are
the finite pattern, text, fallback symbol and numeric thresholds. Actual
all-start rows are constructed before the cached dispatcher is called.
Correctness has no row-provenance or answer-oracle premise.

The returned accounted-work counter includes actual row production.
It retains the documented scope of the existing periodic ledgers and
does not silently turn those ledgers into a full machine-cost theorem. -/
namespace REWB.ResidualActual
variable {σ : Nat}

namespace P1

structure Execution where
  cached : ResidualCached.P1.Execution
  inputWork : Nat
  fixedPatternBuilds : Nat

def Execution.answer (out : Execution) : Bool := out.cached.answer
def Execution.accountedWork (out : Execution) : Nat := out.cached.accountedWork+out.inputWork+2

def execute (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) : Execution :=
  let rows:=inputs P text.toList fallback s
  let cached:=ResidualCached.P1.execute P text fallback s L D Q hs rows.bits
  ⟨cached,rows.work+text.size+5,rows.fixedPatternBuilds⟩

theorem execute_correct (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) (hSL : s≤L) (hD : 0<D) (hQL : Q≤L) :
    (execute P text fallback s L D Q hs).answer=true ↔ MatchesWithin P.nested1 text.toList 2 :=
  ResidualCached.P1.execute_correct P text fallback s L D Q hs hSL hD hQL
    (inputs P text.toList fallback s).bits (inputs_ready P text.toList fallback s)

theorem execute_inputWork (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) :
    (execute P text fallback s L D Q hs).inputWork=(inputs P text.toList fallback s).work+text.size+5 := rfl

theorem execute_builds (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) :
    (execute P text fallback s L D Q hs).fixedPatternBuilds=(inputs P text.toList fallback s).fixedPatternBuilds := rfl

theorem execute_accountedWork (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) (hL : 0<L) (hD : 0<D) :
    (execute P text fallback s L D Q hs).accountedWork≤
      (inputs P text.toList fallback s).work+text.size+7+
        ResidualCached.P1.residualBudget P text.size s L D Q+
        (PeriodicAccounting.longExpr P).eval text.size Q+
        (PeriodicAccounting.shortExpr P).eval text.size Q := by
  have h:=ResidualCached.P1.execute_accountedWork P text fallback s L D Q hs hL hD
    (inputs P text.toList fallback s).bits
  change (ResidualCached.P1.execute P text fallback s L D Q hs (inputs P text.toList fallback s).bits).accountedWork+
    ((inputs P text.toList fallback s).work+text.size+5)+2≤_
  omega

def auto (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) : Execution :=
  execute P text fallback (ThresholdBudget.block text.size) (ThresholdBudget.length text.size)
    (ThresholdBudget.length text.size) (ThresholdBudget.period text.size) (ResidualCached.parameters text.size).1

theorem auto_correct (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) :
    (auto P text fallback).answer=true ↔ MatchesWithin P.nested1 text.toList 2 :=
  execute_correct P text fallback _ _ _ _ (ResidualCached.parameters text.size).1
    (ResidualCached.parameters text.size).2.1 (ResidualCached.parameters text.size).2.2.1
    (ResidualCached.parameters text.size).2.2.2

end P1

namespace P2

structure Execution where
  cached : ResidualCached.P2.Execution
  inputWork : Nat
  fixedPatternBuilds : Nat

def Execution.answer (out : Execution) : Bool := out.cached.answer
def Execution.accountedWork (out : Execution) : Nat := out.cached.accountedWork+out.inputWork+2

def execute (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) : Execution :=
  let rows:=inputs P text.toList fallback s
  let cached:=ResidualCached.P2.execute P text fallback s L D Q hs rows.bits
  ⟨cached,rows.work+text.size+5,rows.fixedPatternBuilds⟩

theorem execute_correct (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) (hSL : s≤L) (hD : 0<D) (hQL : Q≤L) :
    (execute P text fallback s L D Q hs).answer=true ↔ MatchesWithin P.nested2 text.toList 2 :=
  ResidualCached.P2.execute_correct P text fallback s L D Q hs hSL hD hQL
    (inputs P text.toList fallback s).bits (inputs_ready P text.toList fallback s)

theorem execute_inputWork (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) :
    (execute P text fallback s L D Q hs).inputWork=(inputs P text.toList fallback s).work+text.size+5 := rfl

theorem execute_builds (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) :
    (execute P text fallback s L D Q hs).fixedPatternBuilds=(inputs P text.toList fallback s).fixedPatternBuilds := rfl

theorem execute_accountedWork (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) (hL : 0<L) (hD : 0<D) :
    (execute P text fallback s L D Q hs).accountedWork≤
      (inputs P text.toList fallback s).work+text.size+7+
        ResidualCached.P2.residualBudget P text.size s L D Q+
        (PeriodicAccounting.p2Expr P).eval text.size Q*PeriodicAccounting.logHeight text.size := by
  have h:=ResidualCached.P2.execute_accountedWork P text fallback s L D Q hs hL hD
    (inputs P text.toList fallback s).bits
  change (ResidualCached.P2.execute P text fallback s L D Q hs (inputs P text.toList fallback s).bits).accountedWork+
    ((inputs P text.toList fallback s).work+text.size+5)+2≤_
  omega

def auto (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) : Execution :=
  execute P text fallback (ThresholdBudget.block text.size) (ThresholdBudget.length text.size)
    (ThresholdBudget.length text.size) (ThresholdBudget.period text.size) (ResidualCached.parameters text.size).1

theorem auto_correct (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) :
    (auto P text fallback).answer=true ↔ MatchesWithin P.nested2 text.toList 2 :=
  execute_correct P text fallback _ _ _ _ (ResidualCached.parameters text.size).1
    (ResidualCached.parameters text.size).2.1 (ResidualCached.parameters text.size).2.2.1
    (ResidualCached.parameters text.size).2.2.2

end P2

/-- The previous cached residual budget plus the two actual row costs.
No row family is a caller argument. -/
theorem auto_accountedWork (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) :
    (P1.auto P text fallback).accountedWork+(P2.auto P text fallback).accountedWork≤
      (P1.inputs P text.toList fallback (ThresholdBudget.block text.size)).work+
      (P2.inputs P text.toList fallback (ThresholdBudget.block text.size)).work+
      2*text.size+14+ResidualCached.Cost.budget P text.size := by
  have h:=ResidualCached.auto_accountedWork P text fallback
    (P1.inputs P text.toList fallback (ThresholdBudget.block text.size)).bits
    (P2.inputs P text.toList fallback (ThresholdBudget.block text.size)).bits
  unfold P1.auto P1.execute P1.Execution.accountedWork P2.auto P2.execute P2.Execution.accountedWork
  dsimp only
  unfold ResidualCached.P1.auto ResidualCached.P2.auto at h
  omega

end REWB.ResidualActual
