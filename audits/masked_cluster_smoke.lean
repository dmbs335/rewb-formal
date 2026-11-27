import REWB.MaskedClusterRegression
import REWB.MaskedPeriodicRegression

/-! Bounded matrix audit against literal one-jump text scans. Production
    cells use actual range maps, finite orbits and stepped mask arrays.
    The reference alone visits individual candidate positions.
-/
open REWB REWB.MaskedCluster REWB.Periodic
open REWB.MaskedCluster.Regression (seen last singletonWord)
open REWB.MaskedPeriodic.Regression (odd even)

structure ClusterCase where
  period : Word Bool
  pad : Word Bool
  m : Nat
  H : Nat
  L : Nat
  lo : Nat
  hi : Nat
  incoming : Nat
  extra : Nat
  sourceId : Nat
  targetId : Nat
  base : Nat
  len : Nat

def cases : List ClusterCase :=
  [⟨[true,false],[false],4,6,5,0,4,0,2,1,2,0,40⟩,
   ⟨[true,false],[false],4,6,4,1,4,1,0,2,3,0,40⟩,
   ⟨[true,false],[false],4,6,4,1,4,2,2,3,2,0,40⟩,
   ⟨[true,false],[false],4,6,5,0,3,0,1,1,2,0,40⟩,
   ⟨[true,false],[false],4,6,5,1,3,1,1,2,1,0,40⟩,
   ⟨[true,false],[false],4,6,4,4,4,0,0,1,3,0,40⟩,
   ⟨[true,true,false],[true,false],3,7,6,0,3,0,3,2,3,0,40⟩,
   ⟨[false],[true],4,3,2,1,4,1,0,3,2,0,40⟩,
   ⟨[true,false],[false],4,6,6,0,4,0,1,0,1,0,40⟩,
   ⟨[true,false],[false],4,6,4,0,4,0,1,1,0,0,40⟩,
   ⟨[true,false],[false],4,6,5,0,4,0,2,1,2,4,4⟩,
   ⟨[true,false],[false],4,6,5,3,2,1,0,2,1,0,40⟩]

def masks : Array (Array Bool) :=
  #[Array.replicate 40 false,Array.replicate 40 true,
    Array.ofFn (fun i : Fin 40=>decide (i.val%3=1 ∨ i.val=6)),
    Array.ofFn (fun i : Fin 40=>decide (i.val=1 ∨ i.val=5 ∨ i.val=8 ∨ i.val=11 ∨ i.val=18))]

def directCell (C E : DFA Bool) (w : Word Bool) (I s q L lo hi O : Nat)
    (source target : Array Bool) (base len : Nat)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount) : Bool :=
  (List.range (hi+1)).any fun k=>
    let p:=s+k*q
    decide (lo≤k ∧ base≤p ∧ p<base+len) &&
      decide (MaskedClusterStage.direct C E w I p L O
        (MaskedProgression.readMask source p) (MaskedProgression.readMask target p) input=some output)

def runCases (C E : DFA Bool) : IO Unit := do
  let begin ← IO.monoMsNow
  let prepared:=prepare C.stateCount E.stateCount
  let states:=List.ofFn (fun i : Fin (MaskedClusterStage.dfa C E).stateCount=>i)
  let mut cells:=0
  let mut hits:=0
  let mut matrices:=0
  let mut maxProducts:=0
  let mut maxVisits:=0
  let mut maxMatrixWork:=0
  for test in cases do
    let q:=test.period.length
    let s:=test.pad.length
    let R:=s+test.m*q+test.H
    let w:=test.pad++(repeatWord test.period (test.m+test.H+1)).take (test.m*q+test.H)++
      [true,false,true,false,true]
    let I:=s+test.incoming
    let O:=s+test.hi*q+test.H+test.extra
    let valid:=(List.range R).all fun i=>if s≤i ∧ i+q<R then w[i]?==w[i+q]? else true
    unless valid && decide (O≤w.length ∧ 2*q≤test.H) do
      throw (IO.userError "bad dense-cluster audit geometry")
    let ci:=BoundaryApplication.Range.build C w
    let ei:=BoundaryApplication.Range.build E w
    let ctx:=contexts C E ci ei I s test.H q test.lo test.hi O
    let tail:=replay C E ci ei s test.L test.H
    let source:=masks[test.sourceId]?.getD #[]
    let target:=masks[test.targetId]?.getD #[]
    let sourceCounts:=MaskedProgression.build source test.base test.len (prepared.K*q)
    let targetCounts:=MaskedProgression.build target test.base test.len (prepared.K*q)
    let actual:=matrix C E prepared ctx.maps tail.maps test.lo test.hi sourceCounts.counts
      targetCounts.counts test.base q s
    for input in states do
      for output in states do
        let expected:=directCell C E w I s q test.L test.lo test.hi O source target test.base test.len
          (MaskedClusterStage.decode C E input) (MaskedClusterStage.decode C E output)
        let got:=(actual.cells.get input).get output
        unless got=expected do
          throw (IO.userError s!"dense cell mismatch: case={matrices}, input={input.val}, output={output.val}, got={got}, expected={expected}")
        cells:=cells+1
        if expected then hits:=hits+1
    matrices:=matrices+1
    maxProducts:=max maxProducts (ctx.products+tail.products)
    maxVisits:=max maxVisits (ctx.visits+tail.visits)
    maxMatrixWork:=max maxMatrixWork actual.work
  for (I,p,L,H,O) in [(0,1,1,3,5),(1,1,1,1,5),(0,0,2,4,5)] do
    let ci:=BoundaryApplication.Range.build C singletonWord
    let ei:=BoundaryApplication.Range.build E singletonWord
    let ctx:=pointContexts C E ci ei I p H O
    let tail:=replay C E ci ei p L H
    let source:=masks[1]!
    let target:=masks[2]!
    let actual:=pointMatrix C E ctx.maps tail.maps source target p
    for input in states do
      for output in states do
        let expected:=decide (MaskedClusterStage.direct C E singletonWord I p L O
          (MaskedProgression.readMask source p) (MaskedProgression.readMask target p)
          (MaskedClusterStage.decode C E input)=some (MaskedClusterStage.decode C E output))
        let got:=(actual.cells.get input).get output
        unless got=expected do
          throw (IO.userError s!"singleton cell mismatch: p={p}, input={input.val}, output={output.val}")
        cells:=cells+1
        if expected then hits:=hits+1
    matrices:=matrices+1
  let finish ← IO.monoMsNow
  IO.println s!"cluster matrices={matrices}, cells={cells}, true cells={hits}, mismatches=0, elapsed={finish-begin} ms"
  IO.println s!"states C/E={C.stateCount}/{E.stateCount}, K={prepared.K}; maxima: context+tail products={maxProducts}, visits={maxVisits}, AP+matrix work={maxMatrixWork}"
  IO.println "Compiler construction and global update/report scheduling are not included in the AP+matrix counter."
  (← IO.getStdout).flush

def main : IO Unit := do
  runCases odd even
  runCases seen last

#print axioms REWB.MaskedCluster.pairQuery_correct
#print axioms REWB.MaskedCluster.cell_words
#print axioms REWB.MaskedCluster.cell_direct_first
#print axioms REWB.MaskedCluster.certificate_onPeriod
#print axioms REWB.MaskedCluster.cell_direct_certificate
#print axioms REWB.MaskedCluster.matrix_work
#print axioms REWB.MaskedCluster.pointCell_direct
#print axioms REWB.MaskedCluster.Regression.singleton_not_unary
