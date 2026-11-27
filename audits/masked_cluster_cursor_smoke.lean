import REWB.MaskedClusterCursorRegression
import REWB.MaskedPeriodicRegression

/-! Bounded executable audit of all four cursor blocks against literal
    chronological zero/one-jump text scans, plus actual materialized
    composition for two adjacent dense clusters. The reference alone
    scans individual occurrences. Production uses shared range indices,
    finite orbits and immutable stepped-prefix arrays.
-/
open REWB REWB.MaskedCluster REWB.Periodic
open REWB.MaskedCluster.Regression (seen last singletonWord)
open REWB.MaskedPeriodic.Regression (odd even)

structure DenseCase where
  period : Word Bool
  pad : Word Bool
  m : Nat
  H : Nat
  L : Nat
  nextOffset : Nat
  incomingOffset : Nat
  enabled : Bool

def denseCases : List DenseCase :=
  [⟨[true,false],[false],3,6,5,10,1,true⟩,
   ⟨[true,false],[false],3,6,5,12,2,true⟩,
   ⟨[true,false],[false],3,6,4,13,0,false⟩,
   ⟨[true,false],[false],3,6,6,10,2,true⟩,
   ⟨[true,false],[false],1,4,4,4,1,true⟩,
   ⟨[false],[true],2,2,2,3,1,true⟩,
   ⟨[true,true,false],[false,true],2,8,6,11,3,true⟩,
   ⟨[true,true,false],[false,true],2,7,6,13,1,true⟩]

def masks : Array (Array Bool) :=
  #[Array.replicate 64 false,Array.replicate 64 true,
    Array.ofFn (fun i : Fin 64=>decide (i.val%3=1 ∨ i.val=6)),
    Array.ofFn (fun i : Fin 64=>decide (i.val=1 ∨ i.val=5 ∨ i.val=8 ∨ i.val=11 ∨ i.val=18))]

def windows (s q n : Nat) : List SourceWindow :=
  [⟨true,0,n⟩,⟨false,0,n⟩,⟨true,s+q,s+q⟩,
    ⟨true,s+q,s+2*q⟩,⟨true,n,0⟩,⟨true,0,0⟩]

/-- This reference uses the literal current L endpoint, not the cached
    H overlap mode or the compiler's lower/upper AP index formulas. -/
def directCursor (C E : DFA Bool) (w : Word Bool) (s q m L H next incoming : Nat)
    (enabled inputMode outputMode : Bool) (source target : Array Bool) (window : SourceWindow)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount) : Bool :=
  if inputMode && !enabled then false else
    let I:=if inputMode then incoming else s
    let O:=if outputMode then s+m*q+H else next
    let one:=(List.range (m+1)).any fun k=>
      let p:=s+k*q
      decide (I≤p) && (if outputMode then decide (next<p+L) else decide (p+L≤next)) &&
        decide (MaskedClusterStage.direct C E w I p L O
          ((window.enabled && decide (window.lo≤p ∧ p<window.hi)) && source[p]?.getD false)
          (target[p]?.getD false) input=some output)
    if outputMode then one else
      decide (MaskedClusterStage.read C E (Spec.slice w I next) input=output) || one

def checkBlocks (C E : DFA Bool) (actual : CursorBlocks (MaskedClusterStage.dfa C E).stateCount)
    (reference : Bool→Bool→MaskedClusterStage.State C.stateCount E.stateCount→
      MaskedClusterStage.State C.stateCount E.stateCount→Bool) (label : String) : IO (Nat×Nat) := do
  let states:=List.ofFn (fun i : Fin (MaskedClusterStage.dfa C E).stateCount=>i)
  let mut cells:=0
  let mut hits:=0
  for inMode in [false,true] do
    for outMode in [false,true] do
      for input in states do
        for output in states do
          let expected:=reference inMode outMode (MaskedClusterStage.decode C E input)
            (MaskedClusterStage.decode C E output)
          let got:=(((actual.get inMode outMode).cells.get input).get output)
          unless got=expected do
            throw (IO.userError s!"{label}: mode={inMode}/{outMode}, state={input.val}/{output.val}, got={got}, expected={expected}")
          cells:=cells+1
          if got then hits:=hits+1
  return (cells,hits)

def runRows (C E : DFA Bool) : IO Unit := do
  let begin ← IO.monoMsNow
  let prepared:=prepare C.stateCount E.stateCount
  let mut cells:=0
  let mut hits:=0
  let mut blocksChecked:=0
  let mut maxDenseWork:=0
  let mut maxPointWork:=0
  for test in denseCases do
    let q:=test.period.length
    let s:=test.pad.length
    let next:=s+test.nextOffset
    let incoming:=s+test.incomingOffset
    let finish:=s+test.m*q+test.H
    let w:=test.pad++(repeatWord test.period (test.m+test.H+1)).take (test.m*q+test.H)++
      [true,false,true,false,true]
    let validCopies:=(List.range (test.m+1)).all fun k=>
      Spec.slice w s (s+test.H)==Spec.slice w (s+k*q) (s+k*q+test.H)
    unless validCopies && decide (0<q ∧ 0<test.m ∧ 2*q≤test.L ∧ test.L≤test.H ∧
        s+(test.m-1)*q+test.H≤next ∧ s+test.m*q<next ∧ next≤w.length ∧
        finish≤w.length ∧ (next<finish ↔ next<s+test.m*q+test.L) ∧
        (test.enabled=true→s<incoming ∧ incoming≤s+q)) do
      throw (IO.userError "invalid dense cursor audit geometry")
    let ci:=BoundaryApplication.Range.build C w
    let ei:=BoundaryApplication.Range.build E w
    let source:=masks[(blocksChecked/6)%4]?.getD #[]
    let target:=masks[(blocksChecked/6+2)%4]?.getD #[]
    let sourceCounts:=MaskedProgression.build source 0 w.length (prepared.K*q)
    let targetCounts:=MaskedProgression.build target 0 w.length (prepared.K*q)
    for window in windows s q w.length do
      let actual:=compileDense C E prepared ci ei s q test.m test.L test.H next incoming test.enabled
        source target sourceCounts.counts targetCounts.counts 0 window
      unless actual.2≤denseCompilerBudget C E prepared.K w.length do
        throw (IO.userError "dense cursor measured counter exceeded proved budget")
      let checked ← checkBlocks C E actual.1
        (directCursor C E w s q test.m test.L test.H next incoming test.enabled · · source target window)
        s!"dense#{blocksChecked}"
      cells:=cells+checked.1
      hits:=hits+checked.2
      blocksChecked:=blocksChecked+1
      maxDenseWork:=max maxDenseWork actual.2
  for (s,L,H,next,incoming,enabled) in
      [(1,1,3,5,2,true),(1,2,3,2,0,false),(0,2,4,1,1,true),(1,1,1,2,2,true)] do
    let w:=singletonWord
    unless decide (L≤H ∧ s+H≤w.length ∧ s<next ∧ next≤w.length ∧
        (next<s+H ↔ next<s+L) ∧ (enabled=true→s<incoming ∧ incoming≤next)) do
      throw (IO.userError "invalid singleton cursor audit geometry")
    let ci:=BoundaryApplication.Range.build C w
    let ei:=BoundaryApplication.Range.build E w
    let source:=masks[1]!
    let target:=masks[3]!
    for window in windows s 1 w.length do
      let actual:=compilePoint C E ci ei s L H next incoming enabled source target window
      unless actual.2≤pointCompilerBudget C E w.length do
        throw (IO.userError "singleton cursor measured counter exceeded proved budget")
      let checked ← checkBlocks C E actual.1
        (directCursor C E w s 1 0 L H next incoming enabled · · source target window)
        s!"singleton#{blocksChecked}"
      cells:=cells+checked.1
      hits:=hits+checked.2
      blocksChecked:=blocksChecked+1
      maxPointWork:=max maxPointWork actual.2
  let finish ← IO.monoMsNow
  IO.println s!"cursor C/E={C.stateCount}/{E.stateCount}: blocks={blocksChecked}, cells={cells}, true={hits}, mismatches=0, elapsed={finish-begin} ms"
  IO.println s!"counter maxima: dense preparation+AP+four matrices={maxDenseWork}, singleton preparation+four matrices={maxPointWork}"
  (←IO.getStdout).flush

/-- The exact length-6 copies occur at 0,3,8,11. The sparse gap 3→8
    creates an overshoot cursor 9, which skips only the next first copy.
    In particular source 3 cannot target 8, but can target 11. -/
def adjacentWord : Word Bool :=
  [true,false,true,true,false,true,true,false,true,false,true,true,false,true,true,false,true]

def runComposition (C E : DFA Bool) : IO Unit := do
  let begin ← IO.monoMsNow
  let w:=adjacentWord
  let prepared:=prepare C.stateCount E.stateCount
  let ci:=BoundaryApplication.Range.build C w
  let ei:=BoundaryApplication.Range.build E w
  let copies:=(List.range w.length).filter fun p=>decide (p+6≤w.length) &&
    (Spec.slice w p (p+6)==Spec.slice w 0 6)
  unless copies=[0,3,8,11] do throw (IO.userError s!"unexpected complete adjacent class: {copies}")
  let states:=List.ofFn (fun i : Fin (MaskedClusterStage.dfa C E).stateCount=>i)
  let source:=Array.ofFn (fun i : Fin 17=>decide (i.val=3))
  let sourceCounts:=MaskedProgression.build source 0 w.length (prepared.K*3)
  let mut cells:=0
  let mut hits:=0
  let mut compositions:=0
  let mut maxWork:=0
  for targetPositions in [[8],[11],[8,11],[]] do
    let target:=Array.ofFn (fun i : Fin 17=>targetPositions.contains i.val)
    let targetCounts:=MaskedProgression.build target 0 w.length (prepared.K*3)
    for window in [SourceWindow.mk true 0 4,⟨true,3,4⟩,⟨false,0,17⟩,⟨true,0,0⟩] do
      let a:=compileDense C E prepared ci ei 0 3 1 6 6 8 0 false source target
        sourceCounts.counts targetCounts.counts 0 window
      let b:=compileDense C E prepared ci ei 8 3 1 6 6 17 9 true source target
        sourceCounts.counts targetCounts.counts 0 window
      let actual:=composeBlocks a.1 b.1
      let stageCount:=(MaskedClusterStage.dfa C E).stateCount
      unless actual.2=2*((2*stageCount)*((2*stageCount)*11))+
          (2*stageCount)*((2*stageCount)*(2*stageCount+1))+2 do
        throw (IO.userError "cursor composition/flatten counter mismatch")
      for inputMode in [false,true] do
        for outputMode in [false,true] do
          for input in states do
            for output in states do
              let expected:=[false,true].any fun middleMode=>states.any fun middle=>
                directCursor C E w 0 3 1 6 6 8 0 false inputMode middleMode source target window
                  (MaskedClusterStage.decode C E input) (MaskedClusterStage.decode C E middle) &&
                directCursor C E w 8 3 1 6 6 17 9 true middleMode outputMode source target window
                  (MaskedClusterStage.decode C E middle) (MaskedClusterStage.decode C E output)
              let got:=actual.1.view 0 (code _ inputMode input) (code _ outputMode output)
              unless got=expected do
                throw (IO.userError s!"composition#{compositions}: modes={inputMode}/{outputMode}, states={input.val}/{output.val}, got={got}, expected={expected}")
              cells:=cells+1
              if got then hits:=hits+1
      compositions:=compositions+1
      maxWork:=max maxWork actual.2
  let finish ← IO.monoMsNow
  IO.println s!"composed cursor C/E={C.stateCount}/{E.stateCount}: products={compositions}, cells={cells}, true={hits}, mismatches=0, max flatten+multiply work={maxWork}, elapsed={finish-begin} ms"
  (←IO.getStdout).flush

def main : IO Unit := do
  runRows odd even
  runRows seen last
  runComposition odd even
  runComposition seen last
  IO.println "Counters include actual range preparation, AP queries, matrix writes, flattening and composition; finite-orbit/formula construction, immutable mask preparation, shared index construction and global scheduling are separate."

#print axioms REWB.MaskedCluster.sourcePairQuery_correct
#print axioms REWB.MaskedCluster.rowCell_correct
#print axioms REWB.MaskedCluster.pointRowCell_correct
#print axioms REWB.MaskedCluster.compileDense_correct
#print axioms REWB.MaskedCluster.compilePoint_correct
#print axioms REWB.MaskedCluster.composeBlocks_denotes
#print axioms REWB.MaskedCluster.compileDense_work
#print axioms REWB.MaskedCluster.compilePoint_work
#print axioms REWB.MaskedCluster.composeBlocks_work
#print axioms REWB.MaskedCluster.CursorRegression.target_outside_source_window
#print axioms REWB.MaskedCluster.CursorRegression.incoming_passed_singleton
