import REWB.PeriodicConstructionCutBuild
import REWB.PeriodicConstructionCutPhase
import REWB.MaskedPeriodicTextRegression

/-! Kernel regressions for the counted local query. These use semantic
value-preservation theorems, so the real-tail example does not ask the
kernel to evaluate an enormous fixed-pattern compiler. -/
namespace REWB.PeriodicConstruction.Cut.Regression
open REWB.MaskedPeriodic REWB.MaskedCut.DFAIndex REWB.MaskedFiniteAction.Maps
open REWB.MaskedPeriodic.Regression (universal odd)

theorem empty_tuple_result (B C E : DFA α) :
    Cut.fullTuples B C E none=([],1) := rfl

theorem zero_period (B C E : DFA α)
    (prepared : PreparedPattern B.stateCount C.stateCount E.stateCount)
    (idx : MaskedCut.Index.Tree (jointEnum B C E)) (tail : Map E.stateCount)
    (s R : Nat) (counts : Array Nat) (base : Nat) :
    Cut.query B C E prepared idx tail s R 0 counts base=(⟨⟨false,0,4⟩,0,0⟩,4) := by
  simp only [Cut.query,Nat.lt_irrefl,false_and,if_false]

theorem empty_build (B C E : DFA α) :
    (Cut.buildDFA B C E []).1=MaskedCut.DFAIndex.build B C E [] :=
  Cut.buildDFA_value B C E []

theorem real_tail (prepared : PreparedPattern 1 1 2) :
    (Cut.query universal universal odd prepared
      (Cut.buildDFA universal universal odd Text.Regression.unary).1.1
      (Cut.prepareTail universal universal odd
        (Cut.buildDFA universal universal odd Text.Regression.unary).1.1 5 Text.Regression.unary.length).1.map
      1 5 1 (MaskedProgression.build Text.Regression.target3 0 6 (prepared.K*1)).counts 0).1.result.answer=true := by
  simp only [Cut.query_value,Cut.prepareTail_value,Cut.buildDFA_value]
  exact Text.Regression.indexed_real_tail prepared

end REWB.PeriodicConstruction.Cut.Regression
