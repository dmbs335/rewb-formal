import REWB.MaskedClusterCutRegression
import REWB.MaskedPeriodicRegression

/-! Bounded full-index tests use four joint maps, with B or E having two
    real states. The mixed-cut regression also scans the actual stored
    joint tuples for B2/C1/E2. Its full shared-index query is kernel-proved
    in CutRegression and is additionally runnable with
      lake env lean --run audits/masked_cluster_cut_smoke.lean -- --full-correlation
    That optional J=16 full-index probe exceeded a 30-second external
    timeout at this checkpoint and was stopped; it is not a passed runtime
    gate. It exposes the larger fixed-map materialization cost explicitly.
-/
open REWB REWB.MaskedCluster REWB.MaskedFiniteAction
open REWB.MaskedCluster.CutRegression (all)
open REWB.MaskedCluster.Regression (last singletonWord last1)
open REWB.MaskedPeriodic.Regression (odd)

structure Test (C E : DFA Bool) where
  lo : Nat
  hi : Nat
  gate : Bool
  inputMode : Bool
  outputMode : Bool
  input : MaskedClusterStage.State C.stateCount E.stateCount
  output : MaskedClusterStage.State C.stateCount E.stateCount

structure Stats where
  queries : Nat := 0
  hits : Nat := 0
  products : Nat := 0
  visits : Nat := 0
  tuples : Nat := 0
  entries : Nat := 0

def directCursor (C E : DFA Bool) (w : Word Bool) (s q m L H next incoming : Nat)
    (enabled inMode outMode : Bool) (source target : Array Bool) (window : SourceWindow)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount) : Bool :=
  if inMode && !enabled then false else
    let I:=if inMode then incoming else s
    let O:=if outMode then s+m*q+H else next
    let jump:=(List.range (m+1)).any fun k=>
      let p:=s+k*q
      decide (I≤p) && (if outMode then decide (next<p+L) else decide (p+L≤next)) &&
        decide (MaskedClusterStage.direct C E w I p L O
          ((window.enabled && decide (window.lo≤p ∧ p<window.hi)) && source[p]?.getD false)
          (target[p]?.getD false) input=some output)
    if outMode then jump else decide (MaskedClusterStage.read C E (Spec.slice w I next) input=output) || jump

def check (B C E : DFA Bool) (w : Word Bool) (idx : Cut.Shared B C E)
    (bank : Table (2*ReplayMaps.count C.stateCount E.stateCount) (2*(MaskedClusterStage.dfa C E).stateCount))
    (s q m old H next incoming : Nat) (enabled : Bool) (source target : Array Bool)
    (window : SourceWindow) (test : Test C E) (stats : Stats) : IO Stats := do
  let got:=Cut.queryBank B C E idx bank test.gate 0 test.lo test.hi old
    (code _ test.inputMode (MaskedClusterStage.encode C E test.input))
    (code _ test.outputMode (MaskedClusterStage.encode C E test.output))
  let clipped:=if test.gate then window else SourceWindow.mk false window.lo window.hi
  let expected:=if test.lo≤test.hi ∧ test.hi≤old ∧ old≤w.length then
    (List.range (test.hi+1)).any fun L=>
      decide (test.lo≤L) && B.final (B.run B.initial (Spec.slice w 0 L)) &&
        directCursor C E w s q m L H next incoming enabled test.inputMode test.outputMode source target clipped
          test.input test.output
    else false
  unless got.1.answer=expected do
    throw (IO.userError s!"cut#{stats.queries}: interval={test.lo}/{test.hi}, gate={test.gate}, got={got.1.answer}, expected={expected}")
  let jointSize:=(MaskedCut.DFAIndex.jointEnum B C E).elems.length
  unless got.1.products≤3 && got.1.visits≤3*(Nat.log2 w.length+2) &&
      got.1.tupleProbes≤jointSize*jointSize && got.1.arithmetic≤8 &&
      got.2=ReplayMaps.count C.stateCount E.stateCount do
    throw (IO.userError "cut counters exceeded verified caps")
  return ⟨stats.queries+1,stats.hits+(if expected then 1 else 0),max stats.products got.1.products,
    max stats.visits got.1.visits,max stats.tuples got.1.tupleProbes,max stats.entries got.2⟩

def runDense : IO Unit := do
  let begin ←IO.monoMsNow
  let B:=odd
  let C:=all
  let E:=all
  let w:Word Bool:=[true,false,true,false,true,false,true,false,true,false]
  let idx:=Cut.build B C E w
  let ci:=BoundaryApplication.Range.build C w
  let ei:=BoundaryApplication.Range.build E w
  let prepared:=prepare C.stateCount E.stateCount
  let book:=ReplayMaps.prepare C.stateCount E.stateCount
  let source:=Array.ofFn (fun i : Fin 10=>decide (i.val=0 ∨ i.val=2))
  let target:=Array.ofFn (fun i : Fin 10=>decide (i.val=4))
  let sc:=MaskedProgression.build source 0 w.length (prepared.K*2)
  let tc:=MaskedProgression.build target 0 w.length (prepared.K*2)
  let tests : List (Test C E):=
    [⟨4,6,true,false,false,.waiting,.gap C.initial⟩,
     ⟨4,4,true,false,false,.waiting,.gap C.initial⟩,
     ⟨5,5,true,false,false,.waiting,.gap C.initial⟩,
     ⟨6,6,true,false,false,.waiting,.gap C.initial⟩,
     ⟨6,4,true,false,false,.waiting,.gap C.initial⟩,
     ⟨4,6,false,false,false,.waiting,.gap C.initial⟩,
     ⟨4,6,false,false,false,.gap C.initial,.suffix E.initial⟩,
     ⟨4,6,true,true,false,.waiting,.gap C.initial⟩,
     ⟨4,6,true,false,true,.waiting,.gap C.initial⟩,
     ⟨4,6,false,false,false,.suffix E.initial,.suffix E.initial⟩]
  let mut stats:Stats:={}
  for window in [SourceWindow.mk true 0 10,⟨true,2,3⟩] do
    let bank:=compileDenseBank C E book prepared ci ei 0 2 2 6 6 10 1 true source target sc.counts tc.counts 0 window
    for test in tests do
      stats←check B C E w idx bank.1 0 2 2 6 6 10 1 true source target window test stats
  let finish ←IO.monoMsNow
  IO.println s!"cut dense B/C/E=2/1/1: queries={stats.queries}, hits={stats.hits}, mismatches=0, elapsed={finish-begin} ms; max products={stats.products}, visits={stats.visits}, tuples={stats.tuples}, component writes={stats.entries}"
  (←IO.getStdout).flush

def runPoint : IO Unit := do
  let begin ←IO.monoMsNow
  let B:=all
  let C:=all
  let E:=last
  let w:=singletonWord
  let idx:=Cut.build B C E w
  let ci:=BoundaryApplication.Range.build C w
  let ei:=BoundaryApplication.Range.build E w
  let book:=ReplayMaps.prepare C.stateCount E.stateCount
  let source:=#[true,false,false,false,false]
  let target:=source
  let window:=SourceWindow.mk true 0 5
  let bank:=compilePointBank C E book ci ei 0 5 5 5 1 true source target window
  let tests : List (Test C E):=
    [⟨1,4,false,false,false,.gap C.initial,.suffix last1⟩,
     ⟨5,5,false,false,false,.gap C.initial,.suffix last1⟩,
     ⟨1,5,false,false,false,.gap C.initial,.suffix E.initial⟩,
     ⟨3,2,true,false,false,.gap C.initial,.suffix last1⟩,
     ⟨1,5,true,true,false,.gap C.initial,.suffix last1⟩,
     ⟨1,5,true,false,true,.gap C.initial,.suffix last1⟩,
     ⟨1,5,true,false,false,.waiting,.gap C.initial⟩,
     ⟨1,5,false,false,false,.waiting,.gap C.initial⟩]
  let mut stats:Stats:={}
  for test in tests do
    stats←check B C E w idx bank.1 0 1 0 5 5 5 1 true source target window test stats
  let finish ←IO.monoMsNow
  IO.println s!"cut singleton B/C/E=1/1/2: queries={stats.queries}, hits={stats.hits}, mismatches=0, elapsed={finish-begin} ms; max products={stats.products}, visits={stats.visits}, tuples={stats.tuples}, component writes={stats.entries}"
  (←IO.getStdout).flush

/-- Literal actual-word cut tuples exercise the selector with two
    nontrivial automata, without repeating expensive full summary builds
    in the default audit. The real full query is separately kernel-proved. -/
def runCorrelation (full : Bool) : IO Unit := do
  let begin ←IO.monoMsNow
  let B:=last
  let C:=all
  let E:=last
  let w:=CutRegression.word
  let bank:=bankComponent CutRegression.bank false
  let cuts:=MatrixTable.ofRel (MaskedCut.DFAIndex.jointEnum B C E) fun p s=>
    [1,2].any fun L=>decide (MaskedCut.DFAIndex.jointWord B C E (Spec.slice w 0 L)=p ∧
      MaskedCut.DFAIndex.jointWord B C E (Spec.slice w L 2)=s)
  let i:=code _ false (MaskedClusterStage.encode C E (.gap C.initial))
  let j:=code _ false (MaskedClusterStage.encode C E (.suffix last1))
  let scanned:=Cut.scanCells B C E bank.1 i j cuts
  unless scanned.1=false && scanned.2=256 do throw (IO.userError "joint-cut correlation was lost")
  let bOnly:=B.final (B.run B.initial (Spec.slice w 0 2))
  let suffixOnly:=bank.1.view (ReplayMaps.encode (ReplayMaps.word C E (Spec.slice w 1 2))) i j
  unless bOnly && suffixOnly do throw (IO.userError "correlation regression lacks separate false-positive witnesses")
  let finish ←IO.monoMsNow
  IO.println s!"joint B2/C1/E2 correlation: 256 stored tuple probes, separate witnesses=true, same-cut answer=false, elapsed={finish-begin} ms"
  (←IO.getStdout).flush
  if full then
    let fullBegin ←IO.monoMsNow
    IO.println "Starting optional J=16 full shared-index correlation query."
    (←IO.getStdout).flush
    let result:=Cut.queryBank B C E (Cut.build B C E w) CutRegression.bank false 0 1 2 2 i j
    unless result.1.answer=false do throw (IO.userError "full shared-cut correlation query failed")
    let fullEnd ←IO.monoMsNow
    IO.println s!"optional full correlation passed, elapsed={fullEnd-fullBegin} ms, products={result.1.products}, visits={result.1.visits}, tuple probes={result.1.tupleProbes}"

def main (args : List String) : IO Unit := do
  runDense
  runPoint
  runCorrelation (args.contains "--full-correlation")
  IO.println "Production queries scan no copy lengths; finite-map encoding/monoid operations and global cluster/source-deletion scheduling retain separate accounting."

#print axioms REWB.MaskedCluster.Cut.query_correct
#print axioms REWB.MaskedCluster.Cut.query_bounds
#print axioms REWB.MaskedCluster.Cut.query_denseBank_correct
#print axioms REWB.MaskedCluster.Cut.query_pointBank_correct
#print axioms REWB.MaskedCluster.CutRegression.separate_witnesses
#print axioms REWB.MaskedCluster.CutRegression.rejects_mixed_cuts
