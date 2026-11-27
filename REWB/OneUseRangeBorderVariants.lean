import REWB.BoundaryRangeAutomata
import REWB.BoundaryApplicationRange

/-! Changing a DFA's initial state or final predicate leaves every
materialized transition map unchanged. This adapter shares the whole
range tree and copies only its four scalar/reference fields. -/
namespace REWB.OneUseRange.Border
open REWB.BoundaryApplication REWB.BoundaryRange
variable {α : Type}

def changeRanges (d : DFA α) (idx : Range.Index d) (q : Fin d.stateCount)
    (F : Fin d.stateCount→Bool) : Range.Index (Automata.change d q F) :=
  ⟨idx.tree,idx.length,idx.products,idx.letterCells⟩

@[simp] theorem changeRanges_build (d : DFA α) (w : Word α) (q : Fin d.stateCount)
    (F : Fin d.stateCount→Bool) :
    changeRanges d (Range.build d w) q F=Range.build (Automata.change d q F) w := rfl

def startRanges (d : DFA α) (idx : Range.Index d) (q : Fin d.stateCount) :
    Range.Index (Automata.start d q) := changeRanges d idx q d.final

def stopRanges (d : DFA α) (idx : Range.Index d) (q : Fin d.stateCount) :
    Range.Index (Automata.stop d q) := changeRanges d idx d.initial (fun s=>decide (s=q))

@[simp] theorem startRanges_build (d : DFA α) (w : Word α) (q : Fin d.stateCount) :
    startRanges d (Range.build d w) q=Range.build (Automata.start d q) w := rfl

@[simp] theorem stopRanges_build (d : DFA α) (w : Word α) (q : Fin d.stateCount) :
    stopRanges d (Range.build d w) q=Range.build (Automata.stop d q) w := rfl

end REWB.OneUseRange.Border
