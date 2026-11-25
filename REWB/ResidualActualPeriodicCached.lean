import REWB.PeriodicActualBranchCost
import REWB.ResidualCachedDispatch

/-! The cached residual dispatcher with the actual measured periodic
branch substituted at its call site.  Finite all-start input rows are
retained inputs of this layer.  No old dispatcher is called at runtime
to recover an answer or a cost.  Its answer and residual ledger occur
only in the following preservation proofs. -/
namespace REWB.ResidualActual.Periodic.Cached
variable {σ : Nat}

structure Execution where
  periodic : PeriodicConstruction.Result Bool
  answer : Bool
  residualWork : Nat

def Execution.accountedWork (r : Execution) : Nat := r.residualWork+r.periodic.2

namespace P1

def execute (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s)
    (bits : ResidualCached.P1.Inputs P text.toList.length s) : Execution :=
  let w:=text.toList
  let read:=ArrayText.read text fallback
  let periodic:=PeriodicActual.Cubic.solve P read text.size Q
  let short:=ShortOuter.P1.solve P text fallback L
  let schedule:=ResidualDispatch.prepare read text.size s L D Q
  let cache:=ResidualCached.P1.build P w fallback s hs bits
  let checked:=ResidualCached.any (ResidualCached.P1.query cache) schedule.windows
  ⟨periodic,periodic.1 || short.answer || checked.1,
    short.work+schedule.work+cache.work+checked.2+text.size+10⟩

theorem execute_periodic (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) (bits : ResidualCached.P1.Inputs P text.toList.length s) :
    (execute P text fallback s L D Q hs bits).periodic=
      PeriodicActual.Cubic.solve P (ArrayText.read text fallback) text.size Q := rfl

theorem execute_answer (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) (bits : ResidualCached.P1.Inputs P text.toList.length s) :
    (execute P text fallback s L D Q hs bits).answer=
      (ResidualCached.P1.execute P text fallback s L D Q hs bits).answer := by
  simp only [execute,ResidualCached.P1.execute,PeriodicActual.Cubic.solve_value]

theorem execute_residual_eq (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) (bits : ResidualCached.P1.Inputs P text.toList.length s) :
    (execute P text fallback s L D Q hs bits).residualWork=
      (ResidualCached.P1.execute P text fallback s L D Q hs bits).residualWork := rfl

theorem execute_correct (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) (hSL : s≤L) (hD : 0<D) (hQL : Q≤L)
    (bits : ResidualCached.P1.Inputs P text.toList.length s)
    (ready : ResidualCached.P1.Ready P text.toList s bits) :
    (execute P text fallback s L D Q hs bits).answer=true ↔ MatchesWithin P.nested1 text.toList 2 := by
  rw [execute_answer]
  exact ResidualCached.P1.execute_correct P text fallback s L D Q hs hSL hD hQL bits ready

theorem execute_accountedWork (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) (hL : 0<L) (hD : 0<D)
    (bits : ResidualCached.P1.Inputs P text.toList.length s) :
    (execute P text fallback s L D Q hs bits).accountedWork≤
      ResidualCached.P1.residualBudget P text.size s L D Q+
        PeriodicActual.Cubic.coefficient P*(PeriodicActual.Cubic.expr P).eval text.size Q := by
  rw [Execution.accountedWork,execute_residual_eq,execute_periodic]
  exact Nat.add_le_add
    (ResidualCached.P1.execute_residualWork P text fallback s L D Q hs hL hD bits)
    (PeriodicActual.Cubic.solve_expr P (ArrayText.read text fallback) text.size Q)

theorem execute_work_le_old (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) (bits : ResidualCached.P1.Inputs P text.toList.length s) :
    (execute P text fallback s L D Q hs bits).accountedWork≤
      (ResidualCached.P1.execute P text fallback s L D Q hs bits).accountedWork+
        (PeriodicActual.Cubic.solve P (ArrayText.read text fallback) text.size Q).2 := by
  rw [Execution.accountedWork,execute_residual_eq,execute_periodic]
  unfold ResidualCached.P1.Execution.accountedWork
  omega

end P1

namespace P2

def execute (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s)
    (bits : ResidualCached.P2.Inputs P text.toList.length s) : Execution :=
  let w:=text.toList
  let read:=ArrayText.read text fallback
  let periodic:=PeriodicActual.P2.solve P read text.size Q
  let short:=ShortOuter.P2.solve P text fallback L
  let schedule:=ResidualDispatch.prepare read text.size s L D Q
  let cache:=ResidualCached.P2.build P w fallback s hs bits
  let checked:=ResidualCached.any (ResidualCached.P2.query cache) schedule.windows
  ⟨periodic,periodic.1 || short.answer || checked.1,
    short.work+schedule.work+cache.work+checked.2+text.size+10⟩

theorem execute_periodic (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) (bits : ResidualCached.P2.Inputs P text.toList.length s) :
    (execute P text fallback s L D Q hs bits).periodic=
      PeriodicActual.P2.solve P (ArrayText.read text fallback) text.size Q := rfl

theorem execute_answer (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) (bits : ResidualCached.P2.Inputs P text.toList.length s) :
    (execute P text fallback s L D Q hs bits).answer=
      (ResidualCached.P2.execute P text fallback s L D Q hs bits).answer := by
  simp only [execute,ResidualCached.P2.execute,PeriodicActual.P2.solve_value]

theorem execute_residual_eq (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) (bits : ResidualCached.P2.Inputs P text.toList.length s) :
    (execute P text fallback s L D Q hs bits).residualWork=
      (ResidualCached.P2.execute P text fallback s L D Q hs bits).residualWork := rfl

theorem execute_correct (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) (hSL : s≤L) (hD : 0<D) (hQL : Q≤L)
    (bits : ResidualCached.P2.Inputs P text.toList.length s)
    (ready : ResidualCached.P2.Ready P text.toList s bits) :
    (execute P text fallback s L D Q hs bits).answer=true ↔ MatchesWithin P.nested2 text.toList 2 := by
  rw [execute_answer]
  exact ResidualCached.P2.execute_correct P text fallback s L D Q hs hSL hD hQL bits ready

theorem execute_accountedWork (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) (hL : 0<L) (hD : 0<D)
    (bits : ResidualCached.P2.Inputs P text.toList.length s) :
    (execute P text fallback s L D Q hs bits).accountedWork≤
      ResidualCached.P2.residualBudget P text.size s L D Q+
        PeriodicActual.P2.coefficient P*
          ((PeriodicAccounting.p2Expr P).eval text.size Q*PeriodicAccounting.logHeight text.size) := by
  rw [Execution.accountedWork,execute_residual_eq,execute_periodic]
  exact Nat.add_le_add
    (ResidualCached.P2.execute_residualWork P text fallback s L D Q hs hL hD bits)
    (PeriodicActual.P2.solve_expr P (ArrayText.read text fallback) text.size Q)

theorem execute_work_le_old (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) (bits : ResidualCached.P2.Inputs P text.toList.length s) :
    (execute P text fallback s L D Q hs bits).accountedWork≤
      (ResidualCached.P2.execute P text fallback s L D Q hs bits).accountedWork+
        (PeriodicActual.P2.solve P (ArrayText.read text fallback) text.size Q).2 := by
  rw [Execution.accountedWork,execute_residual_eq,execute_periodic]
  unfold ResidualCached.P2.Execution.accountedWork
  omega

end P2
end REWB.ResidualActual.Periodic.Cached
