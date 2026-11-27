import REWB.MaskedPeriodicRegression

/-! Actual shared-index/orbit/projection/AP execution checked against
    finite direct DFA factor enumeration. The default CI set is bounded;
    pass --extended for the larger rotation/residue/mask probe. -/
open REWB REWB.MaskedPeriodic REWB.MaskedPeriodic.Regression
open REWB.MaskedCut.DFAIndex REWB.MaskedFiniteAction.Maps

structure Case where
  period : Word Bool
  start : Nat
  eta : Nat
  N : Nat
  tail : Word Bool
  maskId : Nat

def combinedCases : List Case := [⟨[true],0,0,9,[true],1⟩]

def positiveCases : List Case :=
  [⟨[true,false],0,1,6,[],1⟩,
   ⟨[true,false],1,1,9,[true],2⟩,
   ⟨[true,false],0,0,6,[true],0⟩,
   ⟨[true,false],0,1,6,[],0⟩,
   ⟨[true,true,false],1,2,6,[],1⟩]

def extendedCases : List Case :=
  ([[false],[true],[true,false],[false,true],[true,true,false],[false,true,false,true]] : List (Word Bool)).flatMap fun V=>
    (List.range V.length).flatMap fun start=>
      (List.range V.length).flatMap fun eta=>
        [4,6,9].flatMap fun N=>[0,1,2].map fun maskId=>⟨V,start,eta,N,[true],maskId⟩

def flush : IO Unit := do (← IO.getStdout).flush

def runCases (b c e : DFA Bool) (suite : List Case) : IO Unit := do
  IO.println s!"preparing fixed-pattern modulus: states={b.stateCount},{c.stateCount},{e.stateCount}"
  flush
  let begin ← IO.monoMsNow
  let prepared := preparePattern b.stateCount c.stateCount e.stateCount
  IO.println s!"prepared pattern modulus: {prepared.K}"
  let ready ← IO.monoMsNow
  IO.println s!"pattern preparation: {ready-begin} ms"
  flush
  let masks := #[Array.replicate 40 false,irregularMask,Array.replicate 40 true]
  let indexed := (suite.map Case.period).eraseDups.map fun V=>(V,build b c e (V++V))
  let mut queries := 0
  let mut hits := 0
  let mut maxProducts := 0
  let mut maxVisits := 0
  let mut maxMaskSlots := 0
  let mut maxScalar := 0
  for test in suite do
    let q := test.period.length
    let doubled := test.period++test.period
    let some entry := indexed.find? (fun entry=>entry.1==test.period) |
      throw (IO.userError "missing prepared period index")
    let index := entry.2
    let mask := masks[test.maskId]?.getD #[]
    let counts := MaskedProgression.build mask 0 40 (prepared.K*q)
    let result := phaseQuery b c e prepared index.1 (wordMap e test.tail)
      test.start test.eta q test.N counts.counts 0 test.start
    -- Copying a rotation belongs only to the direct test reference.
    let rotated := Spec.slice doubled test.start (test.start+q)
    let expected := directPhase b c e rotated test.tail test.eta test.N mask 0 40 test.start
    unless result.result.answer=expected do
      throw (IO.userError s!"periodic mismatch: V={test.period}, phase={test.start}, eta={test.eta}, N={test.N}, maskId={test.maskId}, got={result.result.answer}, expected={expected}")
    queries := queries+1
    if expected then hits := hits+1
    maxProducts := max maxProducts result.products
    maxVisits := max maxVisits result.visits
    maxMaskSlots := max maxMaskSlots result.result.slots
    maxScalar := max maxScalar result.result.arithmetic
    let elapsed ← IO.monoMsNow
    IO.println s!"case {queries}/{suite.length}: answer={expected}, elapsed={elapsed-ready} ms"
    flush
  IO.println s!"joint-cut/direct-factor regression: queries={queries}, hits={hits}, mismatches=0"
  IO.println s!"observed maxima: cut/range products={maxProducts}, index visits={maxVisits}, mask slots={maxMaskSlots}, mask-query scalar charge={maxScalar}"
  IO.println "Compiler construction work is separate from the reported mask-query counters."

def main (args : List String) : IO Unit := do
  if args.contains "--extended" then
    runCases odd universal even extendedCases
  else
    runCases odd universal even combinedCases
    runCases odd universal universal positiveCases
    runCases universal universal even positiveCases

#print axioms REWB.MaskedPeriodic.OrbitData.descriptor_spec
#print axioms REWB.MaskedPeriodic.projection_correct
#print axioms REWB.MaskedPeriodic.Modulus.projection_compatible
#print axioms REWB.MaskedPeriodic.projection_steps
#print axioms REWB.MaskedPeriodic.queryBranch_correct
#print axioms REWB.MaskedPeriodic.interiorTuples_correct
#print axioms REWB.MaskedPeriodic.endingTuples_correct
#print axioms REWB.MaskedPeriodic.contexts_value
#print axioms REWB.MaskedPeriodic.physical_positive
#print axioms REWB.MaskedPeriodic.phaseQuery_correct
#print axioms REWB.MaskedPeriodic.Regression.projected_boundary_cases
