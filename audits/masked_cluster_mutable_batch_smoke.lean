import REWB.MaskedClusterMutableBatchCorrect

/-! End-to-end actual enumerator -> source batch -> eraseSource -> bank
    adapter audit. A separate Boolean array supplies the literal reference.
    Run-ID search below is test setup only; production compileRun performs
    two direct lookups. Immutable target counts are prepared once.
-/
namespace REWB.MaskedCluster.Mutable.Batch.Audit
open REWB.MaskedFiniteAction

def C : DFA (Fin 2) := ⟨2,0,fun q x=>if x=1 then 1 else q,fun q=>q==1⟩
def E : DFA (Fin 2) := ⟨2,0,fun _ x=>x,fun q=>q==1⟩

def reference (w : Word (Fin 2)) (s q m L H next incoming : Nat)
    (enabled im om : Bool) (source target : Array Bool) (window : SourceWindow)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount) : Bool :=
  if im && !enabled then false else
    let I:=if im then incoming else s
    let O:=if om then s+m*q+H else next
    let jump:=(List.range (m+1)).any fun k=>
      let p:=s+k*q
      decide (I≤p) && (if om then decide (next<p+L) else decide (p+L≤next)) &&
        decide (MaskedClusterStage.direct C E w I p L O
          ((window.enabled && decide (window.lo≤p ∧ p<window.hi)) && source[p]?.getD false)
          (target[p]?.getD false) input=some output)
    if om then jump else decide (MaskedClusterStage.read C E (Spec.slice w I next) input=output) || jump

def compare (bank : Table (2*ReplayMaps.count C.stateCount E.stateCount) (2*(MaskedClusterStage.dfa C E).stateCount))
    (z : Replay C E) (window : SourceWindow)
    (ref : SourceWindow→Bool→Bool→MaskedClusterStage.State C.stateCount E.stateCount→
      MaskedClusterStage.State C.stateCount E.stateCount→Bool) (label : String) : IO Nat := do
  let states:=List.ofFn (fun i : Fin (MaskedClusterStage.dfa C E).stateCount=>i)
  let mut checked:=0
  for gate in [false,true] do
    let clipped:=if gate then window else SourceWindow.mk false window.lo window.hi
    for im in [false,true] do
      for om in [false,true] do
        for i in states do
          for j in states do
            let got:=bank.view (code _ gate (ReplayMaps.encode z)) (code _ im i) (code _ om j)
            let expected:=ref clipped im om (MaskedClusterStage.decode C E i) (MaskedClusterStage.decode C E j)
            unless got=expected do
              throw (IO.userError s!"{label}: gate={gate}, modes={im}/{om}, states={i.val}/{j.val}, got={got}, expected={expected}")
            checked:=checked+1
  return checked

def run : IO Unit := do
  let begin ←IO.monoMsNow
  let text : Array (Fin 2):=#[1,0,1,0,1,0,1,0,1,0]
  let w:=text.toList
  let source:=Array.ofFn (fun i : Fin 11=>decide (i.val=0 ∨ i.val=2 ∨ i.val=4 ∨ i.val=7 ∨ i.val=10))
  let target:=Array.ofFn (fun i : Fin 11=>decide (i.val=4 ∨ i.val=7))
  let prepared:=prepare C.stateCount E.stateCount
  let book:=ReplayMaps.prepare C.stateCount E.stateCount
  let ci:=BoundaryApplication.Range.build C w
  let ei:=BoundaryApplication.Range.build E w
  let initial:=MaskedMutableProgression.Batch.prepare text 0 source prepared.K
  let mut found:Option Nat:=none
  for id in List.range initial.runs.size do
    if let some R:=initial.runs[id]? then
      if R.lo=0 && R.hi=10 && R.period=2 then found:=some id
  let some id:=found | throw (IO.userError "actual cubic enumerator missed the audit run")
  let some R:=initial.runs[id]? | throw (IO.userError "actual run ID lookup failed")
  let tc:=MaskedProgression.build target R.lo (MaskedPeriodic.Batch.span R) (prepared.K*R.period)
  let mut sources:=initial
  let mut live:=source
  let erases:=#[0,7,4,4,2,10]
  let denseWindow:=SourceWindow.mk true 0 3
  let pointWindow:=SourceWindow.mk true 0 11
  let mut cells:=0
  let mut banks:=0
  let mut memberChecks:=0
  let mut maxDense:=0
  let mut maxPoint:=0
  for version in List.range (erases.size+1) do
    for p in List.range 13 do
      let got:=MaskedMutableProgression.member sources.singleton p
      unless got.1=live[p]?.getD false do throw (IO.userError s!"batch singleton history at {p}")
      memberChecks:=memberChecks+1
    let dense:=compileRun C E book prepared ci ei sources id 0 2 6 6 10 1 true target tc.counts denseWindow
    let some bank:=dense.1 | throw (IO.userError "valid actual run-ID adapter returned none")
    banks:=banks+1
    maxDense:=max maxDense dense.2
    let some row:=sources.indexes[id]? | throw (IO.userError "current source row missing")
    unless dense.2≤2*denseRowPrepBudget C E w.length+(C.stateCount+E.stateCount+16*(Nat.log2 w.length+2)+6)+
        denseBankBudget C E prepared.K row.levels+12 do throw (IO.userError "batch dense counter exceeded")
    for L in [6,4] do
      let z:=(replay C E ci ei 0 L 6).maps
      cells:=cells+(←compare bank z denseWindow
        (fun win im om=>reference w 0 2 2 L 6 10 1 true im om live target win)
        s!"actual run snapshot={version}, L={L}")
    let point:=compileSingleton C E book ci ei sources 7 3 3 10 8 true target pointWindow
    banks:=banks+1
    maxPoint:=max maxPoint point.2
    unless point.2≤2*pointRowPrepBudget C E w.length+(C.stateCount+E.stateCount+16*(Nat.log2 w.length+2)+6)+
        pointBankBudget C E sources.singleton.levels+4 do throw (IO.userError "batch singleton counter exceeded")
    for L in [3,2] do
      let z:=(replay C E ci ei 7 L 3).maps
      cells:=cells+(←compare point.1 z pointWindow
        (fun win im om=>reference w 7 1 0 L 3 10 8 true im om live target win)
        s!"global singleton snapshot={version}, L={L}")
    let invalid:=compileRun C E book prepared ci ei sources (sources.runs.size+5) 0 2 6 6 10 1 true target tc.counts denseWindow
    unless invalid.1.isNone && invalid.2=5 do throw (IO.userError "invalid run ID was not rejected")
    let mismatch:=compileRun C E book prepared ci ei {sources with modulus:=prepared.K+1} id 0 2 6 6 10 1 true target tc.counts denseWindow
    unless mismatch.1.isNone && mismatch.2=2 do throw (IO.userError "incompatible source modulus was not rejected")
    if let some p:=erases[version]? then
      sources:=MaskedMutableProgression.Batch.eraseSource p sources
      live:=live.setIfInBounds p false
  unless (MaskedMutableProgression.member initial.singleton 10).1 &&
      !(MaskedMutableProgression.member sources.singleton 10).1 && target[4]?.getD false && target[7]?.getD false do
    throw (IO.userError "persistent boundary source or immutable targets failed")
  let finish ←IO.monoMsNow
  IO.println s!"actual mutable batch -> banks: enumerated runs={initial.runs.size}, chosen actual ID={id}, versions={erases.size+1}, erase requests={erases.size}, rebuilt banks={banks}, physical cells={cells}, member checks={memberChecks}, rejected requests={2*(erases.size+1)}, mismatches=0, elapsed={finish-begin} ms"
  IO.println s!"maximum tracked adapter work: dense={maxDense}, singleton={maxPoint}; source memberships delivered once={sources.delivered}"
  IO.println "Target counts were prepared once. Every bank was explicitly rebuilt; global bank ownership/dirty-bank selection remains separate."

end REWB.MaskedCluster.Mutable.Batch.Audit

def main : IO Unit := REWB.MaskedCluster.Mutable.Batch.Audit.run

#print axioms REWB.MaskedCluster.Mutable.Batch.compileRun_lookup
#print axioms REWB.MaskedCluster.Mutable.Batch.compileRun_missing
#print axioms REWB.MaskedCluster.Mutable.Batch.member_current
#print axioms REWB.MaskedCluster.Mutable.Batch.cursor_current
#print axioms REWB.MaskedCluster.Mutable.Batch.run_singleton_member
#print axioms REWB.MaskedCluster.Mutable.Batch.compileRun_current
#print axioms REWB.MaskedCluster.Mutable.Batch.compileSingleton_current
#print axioms REWB.MaskedCluster.Mutable.Batch.compileRun_work
#print axioms REWB.MaskedCluster.Mutable.Batch.compileSingleton_work
