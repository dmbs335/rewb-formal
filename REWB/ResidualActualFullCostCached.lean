import REWB.PeriodicActualFullCostBranchCost
import REWB.ResidualActualPeriodicCached

/-! The refined run/cache/key pipeline is installed at the actual
periodic call sites. The retained row bits are consumed once by the
residual cache. Answers and residual counters agree with the previous
cached dispatcher; the periodic field records the refined actual work.
No old dispatcher is executed to recover a comparison result. -/
namespace REWB.ResidualActual.FullCost.Cached
variable {σ : Nat}

namespace P1

def execute (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s)
    (bits : ResidualCached.P1.Inputs P text.toList.length s) : Periodic.Cached.Execution :=
  let w:=text.toList
  let read:=ArrayText.read text fallback
  let measured:=PeriodicActual.FullCost.Cubic.solve P read text.size Q
  let periodic:=(measured.1.1,measured.2)
  let short:=ShortOuter.P1.solve P text fallback L
  let schedule:=ResidualDispatch.prepare read text.size s L D Q
  let cache:=ResidualCached.P1.build P w fallback s hs bits
  let checked:=ResidualCached.any (ResidualCached.P1.query cache) schedule.windows
  ⟨periodic,periodic.1 || short.answer || checked.1,
    short.work+schedule.work+cache.work+checked.2+text.size+10⟩

theorem execute_periodic (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) (bits : ResidualCached.P1.Inputs P text.toList.length s) :
    (execute P text fallback s L D Q hs bits).periodic=
      ((PeriodicActual.FullCost.Cubic.solve P (ArrayText.read text fallback) text.size Q).1.1,
       (PeriodicActual.FullCost.Cubic.solve P (ArrayText.read text fallback) text.size Q).2) := rfl

theorem execute_answer (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) (bits : ResidualCached.P1.Inputs P text.toList.length s) :
    (execute P text fallback s L D Q hs bits).answer=
      (Periodic.Cached.P1.execute P text fallback s L D Q hs bits).answer := by
  simp only [execute,Periodic.Cached.P1.execute,PeriodicActual.FullCost.Cubic.solve_value]

theorem execute_residual_eq (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) (bits : ResidualCached.P1.Inputs P text.toList.length s) :
    (execute P text fallback s L D Q hs bits).residualWork=
      (Periodic.Cached.P1.execute P text fallback s L D Q hs bits).residualWork := rfl

theorem execute_correct (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) (hSL : s≤L) (hD : 0<D) (hQL : Q≤L)
    (bits : ResidualCached.P1.Inputs P text.toList.length s)
    (ready : ResidualCached.P1.Ready P text.toList s bits) :
    (execute P text fallback s L D Q hs bits).answer=true ↔ MatchesWithin P.nested1 text.toList 2 := by
  rw [execute_answer]
  exact Periodic.Cached.P1.execute_correct P text fallback s L D Q hs hSL hD hQL bits ready

theorem execute_accountedWork (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) (hL : 0<L) (hD : 0<D)
    (bits : ResidualCached.P1.Inputs P text.toList.length s) :
    (execute P text fallback s L D Q hs bits).accountedWork≤
      ResidualCached.P1.residualBudget P text.size s L D Q+
        PeriodicActual.FullCost.Cubic.coefficient P*
          ((PeriodicActual.FullCost.Cubic.expr P).eval text.size Q) := by
  rw [Periodic.Cached.Execution.accountedWork,execute_residual_eq,execute_periodic,
    Periodic.Cached.P1.execute_residual_eq]
  exact Nat.add_le_add
    (ResidualCached.P1.execute_residualWork P text fallback s L D Q hs hL hD bits)
    (PeriodicActual.FullCost.Cubic.solve_expr P (ArrayText.read text fallback) text.size Q)

theorem execute_work_le_old (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) (bits : ResidualCached.P1.Inputs P text.toList.length s) :
    (execute P text fallback s L D Q hs bits).accountedWork≤
      (Periodic.Cached.P1.execute P text fallback s L D Q hs bits).accountedWork+
        (PeriodicActual.FullCost.Cubic.solve P (ArrayText.read text fallback) text.size Q).2 := by
  simp only [Periodic.Cached.Execution.accountedWork,execute_residual_eq,execute_periodic]
  omega

end P1

namespace P2

def execute (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s)
    (bits : ResidualCached.P2.Inputs P text.toList.length s) : Periodic.Cached.Execution :=
  let w:=text.toList
  let read:=ArrayText.read text fallback
  let measured:=PeriodicActual.FullCost.P2.solve P read text.size Q
  let periodic:=(measured.1.1,measured.2)
  let short:=ShortOuter.P2.solve P text fallback L
  let schedule:=ResidualDispatch.prepare read text.size s L D Q
  let cache:=ResidualCached.P2.build P w fallback s hs bits
  let checked:=ResidualCached.any (ResidualCached.P2.query cache) schedule.windows
  ⟨periodic,periodic.1 || short.answer || checked.1,
    short.work+schedule.work+cache.work+checked.2+text.size+10⟩

theorem execute_periodic (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) (bits : ResidualCached.P2.Inputs P text.toList.length s) :
    (execute P text fallback s L D Q hs bits).periodic=
      ((PeriodicActual.FullCost.P2.solve P (ArrayText.read text fallback) text.size Q).1.1,
       (PeriodicActual.FullCost.P2.solve P (ArrayText.read text fallback) text.size Q).2) := rfl

theorem execute_answer (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) (bits : ResidualCached.P2.Inputs P text.toList.length s) :
    (execute P text fallback s L D Q hs bits).answer=
      (Periodic.Cached.P2.execute P text fallback s L D Q hs bits).answer := by
  simp only [execute,Periodic.Cached.P2.execute,PeriodicActual.FullCost.P2.solve_value]

theorem execute_residual_eq (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) (bits : ResidualCached.P2.Inputs P text.toList.length s) :
    (execute P text fallback s L D Q hs bits).residualWork=
      (Periodic.Cached.P2.execute P text fallback s L D Q hs bits).residualWork := rfl

theorem execute_correct (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) (hSL : s≤L) (hD : 0<D) (hQL : Q≤L)
    (bits : ResidualCached.P2.Inputs P text.toList.length s)
    (ready : ResidualCached.P2.Ready P text.toList s bits) :
    (execute P text fallback s L D Q hs bits).answer=true ↔ MatchesWithin P.nested2 text.toList 2 := by
  rw [execute_answer]
  exact Periodic.Cached.P2.execute_correct P text fallback s L D Q hs hSL hD hQL bits ready

theorem execute_accountedWork (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) (hL : 0<L) (hD : 0<D)
    (bits : ResidualCached.P2.Inputs P text.toList.length s) :
    (execute P text fallback s L D Q hs bits).accountedWork≤
      ResidualCached.P2.residualBudget P text.size s L D Q+
        PeriodicActual.FullCost.P2.coefficient P*
          ((PeriodicAccounting.p2Expr P).eval text.size Q*PeriodicAccounting.logHeight text.size) := by
  rw [Periodic.Cached.Execution.accountedWork,execute_residual_eq,execute_periodic,
    Periodic.Cached.P2.execute_residual_eq]
  exact Nat.add_le_add
    (ResidualCached.P2.execute_residualWork P text fallback s L D Q hs hL hD bits)
    (PeriodicActual.FullCost.P2.solve_expr P (ArrayText.read text fallback) text.size Q)

theorem execute_work_le_old (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) (bits : ResidualCached.P2.Inputs P text.toList.length s) :
    (execute P text fallback s L D Q hs bits).accountedWork≤
      (Periodic.Cached.P2.execute P text fallback s L D Q hs bits).accountedWork+
        (PeriodicActual.FullCost.P2.solve P (ArrayText.read text fallback) text.size Q).2 := by
  simp only [Periodic.Cached.Execution.accountedWork,execute_residual_eq,execute_periodic]
  omega

end P2

end REWB.ResidualActual.FullCost.Cached
