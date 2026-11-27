import REWB.MaskedClusterMutableRegression
import REWB.MaskedClusterRegression
import REWB.MaskedPeriodicRegression

/-! Bounded executable audit of rebuilt banks after actual persistent
    source erases. The reference mask is an independently updated Boolean
    array; executable code never calls the proof-only `snapshot` array.
    Targets remain immutable, including at deleted source positions.
    Full shared-cut tests use four joint maps to keep the fixed-pattern
    materialization cost bounded. This is not a global dirty-bank repair
    scheduler: every tested current bank is explicitly rebuilt.
-/
namespace REWB.MaskedCluster.Mutable.Audit
open REWB.MaskedFiniteAction
open REWB.MaskedCluster.Regression (seen last singletonWord)
open REWB.MaskedPeriodic.Regression (odd)

def reference (C E : DFA Bool) (w : Word Bool) (s q m L H next incoming : Nat)
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

def checkSelected (C E : DFA Bool)
    (bank : Table (2*ReplayMaps.count C.stateCount E.stateCount) (2*(MaskedClusterStage.dfa C E).stateCount))
    (z : Replay C E) (window : SourceWindow)
    (ref : SourceWindow→Bool→Bool→MaskedClusterStage.State C.stateCount E.stateCount→
      MaskedClusterStage.State C.stateCount E.stateCount→Bool) (label : String) : IO Nat := do
  let states:=List.ofFn (fun i : Fin (MaskedClusterStage.dfa C E).stateCount=>i)
  let mut checked:=0
  for gate in [false,true] do
    let selected:=(bankComponent bank gate).1
    let clipped:=if gate then window else SourceWindow.mk false window.lo window.hi
    for im in [false,true] do
      for om in [false,true] do
        for i in states do
          for j in states do
            let got:=selected.view (ReplayMaps.encode z) (code _ im i) (code _ om j)
            let expected:=ref clipped im om (MaskedClusterStage.decode C E i) (MaskedClusterStage.decode C E j)
            unless got=expected do
              throw (IO.userError s!"{label}: gate={gate}, modes={im}/{om}, states={i.val}/{j.val}, got={got}, expected={expected}")
            checked:=checked+1
  return checked

def checkEqual {k m : Nat} (a b : Table k m) (label : String) : IO Nat := do
  let mut checked:=0
  for key in List.ofFn (fun i : Fin k=>i) do
    for i in List.ofFn (fun i : Fin m=>i) do
      for j in List.ofFn (fun i : Fin m=>i) do
        unless a.view key i j=b.view key i j do
          throw (IO.userError s!"{label}: key={key.val}, states={i.val}/{j.val}")
        checked:=checked+1
  return checked

def checkMembers (idx : Index) (live : Array Bool) : IO Nat := do
  for p in List.range (live.size+2) do
    let got:=MaskedMutableProgression.member idx p
    let expected:=decide (idx.base≤p ∧ p<idx.base+idx.len) && live[p]?.getD false
    unless got.1=expected && got.2≤4*idx.levels+11 do
      throw (IO.userError s!"current source member {p}: got={got.1}, expected={expected}")
  return live.size+2

def erase (idx : Index) (live : Array Bool) (p : Nat) : IO (Index×Array Bool) := do
  let next:=MaskedMutableProgression.erase idx p
  unless next.work≤12*idx.levels+13 do throw (IO.userError "source erase counter exceeded")
  return (next.index,live.setIfInBounds p false)

def runDense : IO Unit := do
  let begin ←IO.monoMsNow
  let C:=seen
  let E:=last
  let w:Word Bool:=[true,false,true,false,true,false,true,false,true,false,true,false]
  let ci:=BoundaryApplication.Range.build C w
  let ei:=BoundaryApplication.Range.build E w
  let prepared:=prepare C.stateCount E.stateCount
  let book:=ReplayMaps.prepare C.stateCount E.stateCount
  let source:=Array.ofFn (fun i : Fin 12=>decide (i.val=0 ∨ i.val=2 ∨ i.val=4 ∨ i.val=7))
  let target:=Array.ofFn (fun i : Fin 12=>decide (i.val=4))
  let tc:=MaskedProgression.build target 0 w.length (prepared.K*2)
  let built:=MaskedMutableProgression.build source 0 w.length (prepared.K*2)
  unless built.work≤40*(w.length+1)*(Nat.log2 (w.length+1)+1) do
    throw (IO.userError "dense source index build counter exceeded")
  let original:=built.index
  let mut idx:=original
  let mut live:=source
  let erases:=#[0,7,4,4,2,100]
  let mut selectedCells:=0
  let mut actionCells:=0
  let mut members:=0
  let mut banks:=0
  let mut maxBankWork:=0
  for version in List.range (erases.size+1) do
    members:=members+(←checkMembers idx live)
    for window in [SourceWindow.mk true 0 12,⟨true,2,3⟩] do
      let old:=compileDenseBank C E book prepared ci ei 0 2 2 6 6 10 1 true idx target tc.counts window
      banks:=banks+1
      maxBankWork:=max maxBankWork old.2
      unless old.2≤2*denseRowPrepBudget C E w.length+(C.stateCount+E.stateCount+16*(Nat.log2 w.length+2)+6)+
          denseBankBudget C E prepared.K idx.levels+3 do
        throw (IO.userError "mutable dense bank counter exceeded")
      for L in [6,5,4] do
        let z:=(replay C E ci ei 0 L 6).maps
        selectedCells:=selectedCells+(←checkSelected C E old.1 z window
          (fun win im om=>reference C E w 0 2 2 L 6 10 1 true im om live target win)
          s!"dense snapshot {version}, shortening {L}")
      if window.hi=12 && (version=0 || version=3) then
        let z:=(replay C E ci ei 0 4 6).maps
        let tagged:=Counted.reindex (bankAction z) old.1
        let fresh:=compileDenseBank C E book prepared ci ei 0 2 2 4 6 10 1 true idx target tc.counts window
        banks:=banks+1
        actionCells:=actionCells+(←checkEqual tagged.1 fresh.1 s!"dense current-snapshot action {version}")
    if let some p:=erases[version]? then
      let next ←erase idx live p
      idx:=next.1
      live:=next.2
  members:=members+(←checkMembers original source)
  unless (MaskedMutableProgression.member original 0).1 && !(MaskedMutableProgression.member idx 0).1 &&
      target[4]?.getD false do throw (IO.userError "persistence or immutable target was lost")
  let finish ←IO.monoMsNow
  IO.println s!"mutable dense C/E=2/2: versions={erases.size+1}, erases={erases.size}, rebuilt banks={banks}, selected cells={selectedCells}, action cells={actionCells}, member checks={members}, mismatches=0, elapsed={finish-begin} ms"
  IO.println s!"mutable dense maximum tracked bank preparation={maxBankWork}; source tree height={idx.levels}"
  (←IO.getStdout).flush

def runPoint : IO Unit := do
  let begin ←IO.monoMsNow
  let C:=seen
  let E:=last
  let w:=singletonWord
  let ci:=BoundaryApplication.Range.build C w
  let ei:=BoundaryApplication.Range.build E w
  let book:=ReplayMaps.prepare C.stateCount E.stateCount
  let source:=#[false,true,false,false,false,true]
  let target:=#[false,true,false,false,false,false]
  let window:=SourceWindow.mk true 0 6
  let original:=(MaskedMutableProgression.build source 0 (w.length+1) 1).index
  let mut idx:=original
  let mut live:=source
  let erases:=#[1,1,5,6]
  let mut selectedCells:=0
  let mut actionCells:=0
  let mut members:=0
  let mut banks:=0
  let mut maxBankWork:=0
  for version in List.range (erases.size+1) do
    members:=members+(←checkMembers idx live)
    let old:=compilePointBank C E book ci ei 1 3 3 2 0 false idx target window
    banks:=banks+1
    maxBankWork:=max maxBankWork old.2
    unless old.2≤2*pointRowPrepBudget C E w.length+(C.stateCount+E.stateCount+16*(Nat.log2 w.length+2)+6)+
        pointBankBudget C E idx.levels+3 do throw (IO.userError "mutable singleton bank counter exceeded")
    for L in [3,2] do
      let z:=(replay C E ci ei 1 L 3).maps
      selectedCells:=selectedCells+(←checkSelected C E old.1 z window
        (fun win im om=>reference C E w 1 1 0 L 3 2 0 false im om live target win)
        s!"singleton snapshot {version}, shortening {L}")
    if version=0 || version=1 then
      let z:=(replay C E ci ei 1 2 3).maps
      let tagged:=Counted.reindex (bankAction z) old.1
      let fresh:=compilePointBank C E book ci ei 1 2 3 2 0 false idx target window
      banks:=banks+1
      actionCells:=actionCells+(←checkEqual tagged.1 fresh.1 s!"singleton current-snapshot action {version}")
    if let some p:=erases[version]? then
      let next ←erase idx live p
      idx:=next.1
      live:=next.2
  members:=members+(←checkMembers original source)
  unless (MaskedMutableProgression.member original w.length).1 &&
      !(MaskedMutableProgression.member idx w.length).1 && target[1]?.getD false do
    throw (IO.userError "terminal membership, persistence, or immutable point target failed")
  let finish ←IO.monoMsNow
  IO.println s!"mutable singleton C/E=2/2: versions={erases.size+1}, erases={erases.size}, rebuilt banks={banks}, selected cells={selectedCells}, action cells={actionCells}, member checks={members}, mismatches=0, elapsed={finish-begin} ms"
  IO.println s!"mutable singleton maximum tracked bank preparation={maxBankWork}; terminal n is tested for membership only"
  (←IO.getStdout).flush

structure CutTest (C E : DFA Bool) where
  lo : Nat
  hi : Nat
  gate : Bool
  inputMode : Bool
  outputMode : Bool
  input : MaskedClusterStage.State C.stateCount E.stateCount
  output : MaskedClusterStage.State C.stateCount E.stateCount

def runCut : IO Unit := do
  let begin ←IO.monoMsNow
  let B:=odd
  let C:=Regression.one
  let E:=Regression.one
  let w:Word Bool:=[true,false,true,false,true,false,true,false,true,false]
  let shared:=Cut.build B C E w
  let ci:=BoundaryApplication.Range.build C w
  let ei:=BoundaryApplication.Range.build E w
  let prepared:=prepare C.stateCount E.stateCount
  let book:=ReplayMaps.prepare C.stateCount E.stateCount
  let source:=Array.ofFn (fun i : Fin 10=>decide (i.val=0 ∨ i.val=2))
  let target:=Array.ofFn (fun i : Fin 10=>decide (i.val=4))
  let tc:=MaskedProgression.build target 0 w.length (prepared.K*2)
  let mut idx:=(MaskedMutableProgression.build source 0 w.length (prepared.K*2)).index
  let mut live:=source
  let erases:=#[0,2,4]
  let window:=SourceWindow.mk true 0 3
  let tests : List (CutTest C E):=
    [⟨4,6,true,false,false,.waiting,.gap C.initial⟩,
     ⟨5,5,true,false,false,.waiting,.gap C.initial⟩,
     ⟨6,4,true,false,false,.waiting,.gap C.initial⟩,
     ⟨4,6,false,false,false,.waiting,.gap C.initial⟩,
     ⟨4,6,false,false,false,.gap C.initial,.suffix E.initial⟩,
     ⟨4,6,true,true,false,.waiting,.gap C.initial⟩,
     ⟨4,6,true,false,true,.waiting,.gap C.initial⟩]
  let mut queries:=0
  let mut hits:=0
  let mut maxProbes:=0
  for version in List.range (erases.size+1) do
    let bank:=compileDenseBank C E book prepared ci ei 0 2 2 6 6 10 1 true idx target tc.counts window
    for test in tests do
      let got:=Cut.queryBank B C E shared bank.1 test.gate 0 test.lo test.hi 6
        (code _ test.inputMode (MaskedClusterStage.encode C E test.input))
        (code _ test.outputMode (MaskedClusterStage.encode C E test.output))
      let clipped:=if test.gate then window else SourceWindow.mk false window.lo window.hi
      let expected:=if test.lo≤test.hi ∧ test.hi≤6 then
        (List.range (test.hi+1)).any fun L=>
          decide (test.lo≤L) && B.final (B.run B.initial (Spec.slice w 0 L)) &&
            reference C E w 0 2 2 L 6 10 1 true test.inputMode test.outputMode live target clipped test.input test.output
        else false
      unless got.1.answer=expected do
        throw (IO.userError s!"mutable shared cut version={version}, query={queries}: got={got.1.answer}, expected={expected}")
      let J:=(MaskedCut.DFAIndex.jointEnum B C E).elems.length
      unless got.1.products≤3 && got.1.visits≤3*(Nat.log2 w.length+2) &&
          got.1.tupleProbes≤J*J && got.1.arithmetic≤8 && got.2=ReplayMaps.count C.stateCount E.stateCount do
        throw (IO.userError "mutable cut counters exceeded")
      queries:=queries+1
      hits:=hits+(if expected then 1 else 0)
      maxProbes:=max maxProbes got.1.tupleProbes
    if let some p:=erases[version]? then
      let next ←erase idx live p
      idx:=next.1
      live:=next.2
  let finish ←IO.monoMsNow
  IO.println s!"mutable shared-cut B/C/E=2/1/1: versions={erases.size+1}, queries={queries}, hits={hits}, max tuple probes={maxProbes}, mismatches=0, elapsed={finish-begin} ms"
  (←IO.getStdout).flush

end REWB.MaskedCluster.Mutable.Audit

def main : IO Unit := do
  REWB.MaskedCluster.Mutable.Audit.runDense
  REWB.MaskedCluster.Mutable.Audit.runPoint
  REWB.MaskedCluster.Mutable.Audit.runCut
  IO.println "Every current bank was explicitly rebuilt; source erase does not repair old cached banks. Fixed-pattern compiler/catalog/action construction and global repair selection remain separate."

#print axioms REWB.MaskedCluster.Mutable.snapshot_erase
#print axioms REWB.MaskedCluster.Mutable.sourcePairQuery_correct
#print axioms REWB.MaskedCluster.Mutable.sourcePairQuery_log_work
#print axioms REWB.MaskedCluster.Mutable.cell_direct_first
#print axioms REWB.MaskedCluster.Mutable.pointCell_target_erase
#print axioms REWB.MaskedCluster.Mutable.compileDenseBank_current
#print axioms REWB.MaskedCluster.Mutable.compilePointBank_current
#print axioms REWB.MaskedCluster.Mutable.compileDenseBank_reindex
#print axioms REWB.MaskedCluster.Mutable.compilePointBank_reindex
#print axioms REWB.MaskedCluster.Mutable.query_denseBank_correct
#print axioms REWB.MaskedCluster.Mutable.query_pointBank_correct
#print axioms REWB.MaskedCluster.Mutable.compileDenseBank_work
#print axioms REWB.MaskedCluster.Mutable.compilePointBank_work
#print axioms REWB.MaskedCluster.Mutable.Regression.rebuilt_source_deleted_target_retained
#print axioms REWB.MaskedCluster.Mutable.Regression.old_snapshot_remains
#print axioms REWB.MaskedCluster.Mutable.Regression.terminal_source_member
