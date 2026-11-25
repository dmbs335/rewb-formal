import REWB.MaskedClusterBankRegression

/-! Bounded audit of actual fixed-mask replay banks. Every selected
    real-length matrix is compared with literal chronological text
    scans. Noninjective, noncommuting shortening actions are checked in
    their real order, including a cached product of two different local
    tails. This does not exercise global source deletion or repairs.
-/
open REWB REWB.MaskedCluster REWB.MaskedFiniteAction
open REWB.MaskedCluster.Regression (seen last)

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
    let component:=bankComponent bank gate
    let selectedWindow:=if gate then window else SourceWindow.mk false window.lo window.hi
    for inMode in [false,true] do
      for outMode in [false,true] do
        for i in states do
          for j in states do
            let got:=component.1.view (ReplayMaps.encode z) (code _ inMode i) (code _ outMode j)
            let expected:=ref selectedWindow inMode outMode (MaskedClusterStage.decode C E i)
              (MaskedClusterStage.decode C E j)
            unless got=expected do
              throw (IO.userError s!"{label}: gate={gate}, modes={inMode}/{outMode}, states={i.val}/{j.val}")
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

def differs {k m : Nat} (a b : Table k m) : Bool :=
  (List.ofFn (fun i : Fin k=>i)).any fun key=>
    (List.ofFn (fun i : Fin m=>i)).any fun i=>
      (List.ofFn (fun i : Fin m=>i)).any fun j=>a.view key i j != b.view key i j

def main : IO Unit := do
  let begin ← IO.monoMsNow
  let C:=seen
  let E:=last
  let prepared:=prepare C.stateCount E.stateCount
  let book:=ReplayMaps.prepare C.stateCount E.stateCount
  let mut selectedCells:=0
  let mut actionCells:=0
  let mut maxBankWork:=0
  let mut wrongOrderWitnesses:=0
  let w:Word Bool:=[true,false,true,false,true,false,true,false,true,false,true,false]
  let ci:=BoundaryApplication.Range.build C w
  let ei:=BoundaryApplication.Range.build E w
  let source:=Array.ofFn (fun i : Fin 12=>decide (i.val=0 ∨ i.val=2))
  let target:=Array.ofFn (fun i : Fin 12=>decide (i.val=4))
  let sc:=MaskedProgression.build source 0 w.length (prepared.K*2)
  let tc:=MaskedProgression.build target 0 w.length (prepared.K*2)
  for window in [SourceWindow.mk true 0 12,⟨true,2,3⟩] do
    let oldBank:=compileDenseBank C E book prepared ci ei 0 2 2 6 6 10 1 true source target sc.counts tc.counts 0 window
    unless oldBank.2≤2*denseRowPrepBudget C E w.length+(C.stateCount+E.stateCount+16*(Nat.log2 w.length+2)+6)+
        denseBankBudget C E prepared.K+3 do throw (IO.userError "dense bank budget exceeded")
    maxBankWork:=max maxBankWork oldBank.2
    for L in [6,5,4] do
      let z:=(replay C E ci ei 0 L 6).maps
      selectedCells:=selectedCells+(←checkSelected C E oldBank.1 z window
        (fun window inMode outMode=>reference C E w 0 2 2 L 6 10 1 true inMode outMode source target window)
        s!"dense shortening to {L}")
    let z0:=(replay C E ci ei 0 5 6).maps
    let z1:=(replay C E ci ei 0 4 5).maps
    unless ReplayMaps.mul z0 z1 != ReplayMaps.mul z1 z0 do
      throw (IO.userError "audit shortening maps unexpectedly commute")
    let tagged0:=Counted.reindex (bankAction z0) oldBank.1
    let tagged1:=Counted.reindex (bankAction z1) tagged0.1
    let fresh:=compileDenseBank C E book prepared ci ei 0 2 2 4 6 10 1 true source target sc.counts tc.counts 0 window
    actionCells:=actionCells+(←checkEqual tagged1.1 fresh.1 "actual dense bank action order")
    let backwards:=Counted.reindex (bankAction z0) (Counted.reindex (bankAction z1) oldBank.1).1
    unless differs backwards.1 fresh.1 do throw (IO.userError "audit failed to detect reversed shortening order")
    wrongOrderWitnesses:=wrongOrderWitnesses+1
  let pw:Word Bool:=[true,false,true,false,true,false,true,true,false,true]
  let pci:=BoundaryApplication.Range.build C pw
  let pei:=BoundaryApplication.Range.build E pw
  let ps:=Array.ofFn (fun i : Fin 10=>decide (i.val=0 ∨ i.val=4))
  let pt:=Array.ofFn (fun i : Fin 10=>decide (i.val=4))
  let pwindow:=SourceWindow.mk true 0 10
  unless Spec.slice pw 0 3=Spec.slice pw 4 7 do throw (IO.userError "old singleton words differ")
  unless (replay C E pci pei 0 3 4).maps != (replay C E pci pei 4 3 4).maps do
    throw (IO.userError "audit requires distinct old local replay tails")
  for (s,next,incoming,enabled) in [(0,4,0,false),(4,10,5,true)] do
    let oldBank:=compilePointBank C E book pci pei s 3 4 next incoming enabled ps pt pwindow
    unless oldBank.2≤2*pointRowPrepBudget C E pw.length+(C.stateCount+E.stateCount+16*(Nat.log2 pw.length+2)+6)+
        pointBankBudget C E+3 do throw (IO.userError "point bank budget exceeded")
    maxBankWork:=max maxBankWork oldBank.2
    for L in [3,2,1] do
      let z:=(replay C E pci pei 0 L 3).maps
      selectedCells:=selectedCells+(←checkSelected C E oldBank.1 z pwindow
        (fun window inMode outMode=>reference C E pw s 1 0 L 4 next incoming enabled inMode outMode ps pt window)
        s!"singleton {s}, shortening to {L}")
  let a:=compilePointBank C E book pci pei 0 3 4 4 0 false ps pt pwindow
  let b:=compilePointBank C E book pci pei 4 3 4 10 5 true ps pt pwindow
  let tree:=Tree.build #[a.1,b.1] 1 0
  let z:=(replay C E pci pei 0 1 3).maps
  let tagged:=Tree.reindex (bankAction z) tree.1
  let anew:=compilePointBank C E book pci pei 0 1 4 4 0 false ps pt pwindow
  let bnew:=compilePointBank C E book pci pei 4 1 4 10 5 true ps pt pwindow
  let freshProduct:=Counted.mul anew.1 bnew.1
  actionCells:=actionCells+(←checkEqual (Tree.cache tagged.1) freshProduct.1 "common-prefix root action with distinct local tails")
  let finish ← IO.monoMsNow
  IO.println s!"replay bank C/E={C.stateCount}/{E.stateCount}, replay maps={ReplayMaps.count C.stateCount E.stateCount}, source components=2"
  IO.println s!"physical selected cells={selectedCells}, action/product cells={actionCells}, wrong-order witnesses={wrongOrderWitnesses}, mismatches=0, elapsed={finish-begin} ms"
  IO.println s!"maximum tracked bank preparation={maxBankWork}; root reindex work={tagged.2}"
  IO.println "Masks are immutable; source deletion/repair and finite-compiler/pattern-catalog/action construction retain separate accounting."

#print axioms REWB.MaskedCluster.ReplayMaps.common_shortening
#print axioms REWB.MaskedCluster.tabulate_reindex
#print axioms REWB.MaskedCluster.compileDenseBank_current
#print axioms REWB.MaskedCluster.compilePointBank_current
#print axioms REWB.MaskedCluster.compileDenseBank_reindex
#print axioms REWB.MaskedCluster.compilePointBank_reindex
#print axioms REWB.MaskedCluster.compileDenseBank_select_shorter
#print axioms REWB.MaskedCluster.compilePointBank_select_shorter
#print axioms REWB.MaskedCluster.compileDenseBank_work
#print axioms REWB.MaskedCluster.compilePointBank_work
#print axioms REWB.MaskedCluster.BankRegression.maps_noncommute
