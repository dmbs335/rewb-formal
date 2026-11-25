import REWB.MaskedPeriodicTextRegression

/-! Bounded actual-text check. Each case compares both in-run and full
    suffix queries with literal slice recognition and copy equality.
    The joint universes have size at most four; no large all-map probe
    is silently included in the default audit.
-/
open REWB REWB.MaskedPeriodic REWB.MaskedPeriodic.Text
open REWB.MaskedPeriodic.Regression (universal odd even irregularMask)
open REWB.MaskedPeriodic.Text.Regression (direct)
open REWB.MaskedCut.DFAIndex

structure TextCase where
  period : Word Bool
  pad : Word Bool
  turns : Nat
  eta : Nat
  shift : Nat
  tail : Word Bool
  maskId : Nat
  base : Nat := 0
  len : Nat := 40

def cases : List TextCase :=
  [⟨[true],[true],4,0,0,[true],2,0,40⟩,
   ⟨[true,false],[false],5,1,0,[false],3,0,40⟩,
   ⟨[true,false],[false],7,0,0,[true,false,true],3,0,40⟩,
   ⟨[true,false],[false],7,1,1,[true],1,0,40⟩,
   ⟨[true,true,false],[false,true],6,2,2,[true,false],1,0,40⟩,
   ⟨[false,true],[false],6,0,0,[true,true],0,0,40⟩,
   ⟨[false,true],[false],6,1,0,[true,true],4,0,40⟩,
   ⟨[true,false],[false],5,1,11,[true],4,0,40⟩,
   ⟨[true,false],[false],5,1,12,[true],4,0,40⟩,
   ⟨[true,false],[false],5,1,0,[false],3,4,4⟩,
   ⟨[true,false],[false],5,1,0,[false],3,4,3⟩,
   ⟨[true,false],[false],7,1,1,[true],5,0,40⟩]

def flush : IO Unit := do (← IO.getStdout).flush

def runCases (b c e : DFA Bool) : IO Unit := do
  let begin ← IO.monoMsNow
  let prepared := preparePattern b.stateCount c.stateCount e.stateCount
  IO.println s!"actual-text suite states={b.stateCount},{c.stateCount},{e.stateCount}; modulus={prepared.K}"
  let ready ← IO.monoMsNow
  IO.println s!"pattern preparation: {ready-begin} ms"
  flush
  let masks := #[Array.replicate 40 false,irregularMask,
    Text.Regression.target3,Text.Regression.target7,Array.replicate 40 true,#[true,false,true]]
  let mut count := 0
  let mut hits := 0
  let mut differences := 0
  let mut maxProducts := 0
  let mut maxVisits := 0
  let mut maxSlots := 0
  let mut maxScalar := 0
  for test in cases do
    let q := test.period.length
    let w := test.pad++Periodic.repeatWord test.period test.turns++test.period.take test.eta++test.tail
    let s := test.pad.length+test.shift
    let R := test.pad.length+test.turns*q+test.eta
    let valid := (List.range R).all fun i=>
      if s≤i ∧ i+q<R then w[i]?==w[i+q]? else true
    unless valid do throw (IO.userError "audit constructed a nonperiodic interval")
    let index := (build b c e w).1
    let tail := prepareTail b c e index R w.length
    let mask := masks[test.maskId]?.getD #[]
    let counts := MaskedProgression.build mask test.base test.len (prepared.K*q)
    let inside := inRun b c e prepared index s R q counts.counts test.base
    let complete := query b c e prepared index tail.map s R q counts.counts test.base
    for (mode,result,after) in [("in-run",inside,[]),("full",complete,w.drop R)] do
      let expected := direct b c e w after s R q mask test.base test.len
      unless result.result.answer=expected do
        throw (IO.userError s!"actual-text mismatch: mode={mode}, source={s}, end={R}, q={q}, mask={test.maskId}, window={test.base}:{test.len}, got={result.result.answer}, expected={expected}")
      count := count+1
      if expected then hits := hits+1
      maxProducts := max maxProducts result.products
      maxVisits := max maxVisits result.visits
      maxSlots := max maxSlots result.result.slots
      maxScalar := max maxScalar result.result.arithmetic
    if inside.result.answer≠complete.result.answer then differences := differences+1
  let finish ← IO.monoMsNow
  IO.println s!"actual-text queries={count}, hits={hits}, suffix-mode differences={differences}, mismatches=0; execution={finish-ready} ms"
  IO.println s!"observed query maxima: products={maxProducts}, visits={maxVisits}, mask slots={maxSlots}, scalar charge={maxScalar}"
  IO.println "The scalar charge includes fixed endpoint arithmetic; compiler construction and shared index preparation have separate ledgers."
  flush

def main : IO Unit := do
  runCases odd universal universal
  runCases universal universal even

#print axioms REWB.MaskedPeriodic.Text.families_iff
#print axioms REWB.MaskedPeriodic.Text.actual_equal_copies
#print axioms REWB.MaskedPeriodic.Text.query_correct
#print axioms REWB.MaskedPeriodic.Text.query_run_correct
#print axioms REWB.MaskedPeriodic.Text.query_full_run_correct
#print axioms REWB.MaskedPeriodic.Text.Regression.indexed_real_text
#print axioms REWB.MaskedPeriodic.Text.Regression.actual_ending_witness
