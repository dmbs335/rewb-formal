import REWB.SmallPeriodP2

/-! Narrow executable regression for the phase/run loop adapters.
The q=0 phase rows have empty formulas, and period-zero run rows have
empty phase lists. These deliberately test large loop traversals without
an expensive Presburger instance; they are not valid-run semantic tests.
Run with `lake env lean --run audits/lean_p2_tail_smoke.lean`. -/
open REWB

private def allBits : DFA (Fin 2) :=
  ⟨1,⟨0,by decide⟩,fun _ _=>⟨0,by decide⟩,fun _=>true⟩

private def pattern : SevenDFA (Fin 2) :=
  ⟨allBits,allBits,allBits,allBits,allBits,allBits,allBits⟩

private def sameWork (a b : SmallPeriodP2.Work) : Bool :=
  a.accepted==b.accepted && a.cacheWork==b.cacheWork &&
  a.equalityReads==b.equalityReads && a.phaseCalls==b.phaseCalls &&
  a.projectionSteps==b.projectionSteps

def main : IO Unit := do
  let count:=100000
  let f:=fun _ : Nat=>(0 : Fin 2)
  let shared:=FullyCachedP2.prepare pattern f 0 [] []
  let row : P2Periodic.Five:=⟨0,0,0,0,0⟩
  let one:=CountedCachedP2.solveAt pattern 0 0 shared (P2Periodic.extend 0 row)
  let rows:=List.replicate count row
  let result:=SmallPeriodP2.phases pattern 0 0 shared rows
  let expected : SmallPeriodP2.Work:=
    ⟨one.accepted,0,count*one.equalityReads,count,count*one.projectionSteps⟩
  if !(sameWork result expected) then
    throw (IO.userError s!"phase traversal counters differ: {repr result}")
  let contexts:=(BoundaryContexts.build pattern []).1
  let emptyRun : RunGeometry.Bounds:=⟨0,0,0⟩
  let runs:=SmallPeriodP2.runs pattern f contexts (List.replicate count emptyRun)
  if !(sameWork runs {}) then
    throw (IO.userError s!"empty-choice run traversal differs: {repr runs}")
  IO.println s!"P2 phase rows={count}; equalityReads={result.equalityReads}; projectionSteps={result.projectionSteps}; eager counters preserved"
  IO.println s!"P2 empty-choice run rows={count}; all Work fields preserved; stack-safe traversals passed"
