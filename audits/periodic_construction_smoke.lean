import REWB.PeriodicConstructionRegression
import REWB.PeriodicConstructionSystems
import REWB.PeriodicConstructionPattern
import REWB.MaskedClusterRegression
import REWB.MaskedPeriodicTextRegression

/-! Reproducible local-construction audit. Direct exponent scans, literal
slice scans and formula pretty-print comparisons occur only here. The
production compilers retain materialized finite inputs and AP queries. -/
namespace REWB.PeriodicConstruction.Audit
open REWB.PeriodicConstruction REWB.AffineProjection
open REWB.MaskedFiniteAction.Maps
open REWB.MaskedPeriodic.Regression (universal odd)
open REWB.MaskedCluster.Regression (seen last)

def check (ok : Bool) (label : String) : IO Unit :=
  unless ok do throw (IO.userError label)

def flush : IO Unit := do (←IO.getStdout).flush

def runOrbits : IO Unit := do
  let mut inputs:=0
  let mut points:=0
  for m in [1,2,3] do
    for step in allMaps m do
      for initial in List.ofFn (fun i : Fin m=>i) do
        for mask in List.range (2^m) do
          let bits:=Vector.ofFn (fun i : Fin m=>decide ((mask/2^i.val)%2=1))
          let o:Masked.Input m:=⟨step,initial,bits⟩
          let got:=Masked.descriptor o
          let old:=o.data.descriptor
          check (got.1.threshold=old.threshold && got.1.period=old.period &&
            got.1.initialCounts=old.initialCounts && got.1.residues=old.residues) "orbit descriptor changed"
          check (got.2≤Masked.descriptorCost m) "orbit work bound"
          for k in List.range 24 do
            check (got.1.test k=o.data.test k) s!"orbit acceptance m={m}, k={k}"
            points:=points+1
          let f:=Masked.orbitFormula o (.var 0)
          check (f.2≤(Masked.orbitBudget m).work) "orbit formula construction bound"
          check (reprStr f.1=reprStr (o.data.formula (.var 0))) "orbit formula changed"
          inputs:=inputs+1
  IO.println s!"construction orbits: inputs={inputs}, independent exponent checks={points}"
  flush

def runWindows : IO Unit := do
  let forms:List AffineProjection.Formula:=
    [[],[[]],[[.le (.lit (-1))]],[[.le (.lit 1)]],
      [[.le ((Aff.lit 3).sub (.var 0)),.le ((Aff.var 0).sub (.lit 7))]],
      [[.dvd 2 ((Aff.var 0).sub (.lit 1))]],
      [[.le (MaskedCluster.positionExpr 3 1048576)]],
      [[.le (.scale (-17) (.var 0)),.dvd 3 (.add (.var 0) (.lit 2))]]]
  let mut cases:=0
  for F in forms do
    for K in [0,1,2,3] do
      for N in [0,1,7] do
        let got:=PeriodicConstruction.allWindows K N F
        check (got.1=ExponentIntervals.allWindows K N F) "window values changed"
        check (got.2≤24*K*(Syntax.formula F+1)+3) "coefficient-independent window cost"
        cases:=cases+1
  IO.println s!"construction windows: cases={cases}, including zero modulus and large coefficients"
  flush

def runSystems : IO Unit := do
  let patterns:List (SevenDFA Bool):=
    [⟨universal,universal,universal,universal,universal,universal,universal⟩,
     ⟨seen,universal,universal,universal,universal,universal,last⟩]
  let mut cases:=0
  for P in patterns do
    for q in [1,2] do
      let I:=FullyCachedP2.prepare P (fun i=>decide (i%2=0)) q [true] [false]
      for n in [0,1,6] do
        for phase in [0,1,2] do
          let ph:P2Periodic.Layout Nat:=⟨phase,0,phase,0,phase,0,phase,0⟩
          let L:=P2Periodic.endpoints ph
          let got:=Formula.p2 P q n I L
          check (reprStr got.1=reprStr (FullyCachedP2.formula P q n I L)) "P2 assembly changed"
          check (got.2≤(Formula.p2Budget P I.a.stateCount I.h.stateCount).work) "P2 assembly work"
          let source:=Formula.source P n q 0 phase 0 I
          check (reprStr source.1=reprStr (CachedP1.source P n q 0 phase 0 I)) "P1 source assembly changed"
          check (source.2≤(Formula.sourceBudget I.a.stateCount).work) "P1 source assembly work"
          let target:P1Target.Layout Nat:=⟨phase,0,phase,0,phase⟩
          let f:=Formula.target P n q 0 0 I target
          check (reprStr f.1=reprStr (CachedP1.targetFormula P n q 0 0 I target)) "P1 target assembly changed"
          check (f.2≤(Formula.targetBudget P I.h.stateCount).work) "P1 target assembly work"
          cases:=cases+1
      let bad:P2Periodic.Layout Nat:=⟨q,q,q,q,q,q,q,q⟩
      let solve:=Formula.solveP2 P 0 q I bad
      check (solve.1=(CountedCachedP2.solveAt P 0 q I bad).accepted) "P2 measured solver value"
  IO.println s!"construction P1/P2: assembly cases={cases}, plus four actual empty searches"
  flush

def sameIndexed (a b : MaskedPeriodic.IndexedAnswer) : Bool :=
  a.result.answer=b.result.answer && a.result.slots=b.result.slots &&
    a.result.arithmetic=b.result.arithmetic && a.products=b.products && a.visits=b.visits

def runPhases : IO Unit := do
  let B:=universal
  let C:=universal
  let E:=universal
  let prep:=Pattern.preparePattern 1 1 1
  let prepared:=prep.1
  let extra:=Masked.queryExtra 1 1 1 prepared.K
  let mut cases:=0
  let mut hits:=0
  for V in [[true],[true,false],[false,true,true]] do
    for eta in List.range V.length do
      let w:Word Bool:=[false]++Periodic.repeatWord V 5++V.take eta++[true]
      let R:=1+5*V.length+eta
      let idx:=(MaskedCut.DFAIndex.build B C E w).1
      let tail:=MaskedPeriodic.Text.prepareTail B C E idx R w.length
      for mask in [Array.replicate (w.length+1) true,#[false,false,true,false,true],
          Array.ofFn (fun i : Fin (w.length+1)=>decide (i.val%3=1)),#[]] do
        let counts:=MaskedProgression.build mask 0 (w.length+1) (prepared.K*V.length)
        for s in [0,1,2,R,R+1] do
          let got:=Masked.query B C E prepared idx tail.map s R V.length counts.counts 0
          let old:=MaskedPeriodic.Text.query B C E prepared idx tail.map s R V.length counts.counts 0
          check (sameIndexed got.1 old) "phase preserved ledger/value"
          check (got.2≤MaskedPeriodic.Batch.queryCost old+extra) "phase construction inflation"
          if s≥1 then
            let expected:=MaskedPeriodic.Text.Regression.direct B C E w (w.drop R) s R V.length mask 0 (w.length+1)
            check (got.1.result.answer=expected) s!"phase direct witness s={s}, R={R}, q={V.length}"
          if got.1.result.answer then hits:=hits+1
          cases:=cases+1
  IO.println s!"construction phases: queries={cases}, accepted={hits}, actual pattern setup work={prep.2}"
  flush

def directCell (C E : DFA Bool) (w : Word Bool) (source target : Array Bool)
    (window : MaskedCluster.SourceWindow) (im om : Bool)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount) : Bool :=
  let I:=if im then 1 else 0
  let O:=if om then 10 else 10
  let jumped:=(List.range 3).any fun k=>
    let p:=2*k
    decide (I≤p) && (if om then decide (10<p+6) else decide (p+6≤10)) &&
      decide (MaskedClusterStage.direct C E w I p 6 O
        (window.allows p && source[p]?.getD false) (target[p]?.getD false) input=some output)
  if om then jumped else decide (MaskedClusterStage.read C E (Spec.slice w I 10) input=output) || jumped

def runBanks : IO Unit := do
  let C:=seen
  let E:=last
  let w:Word Bool:=[true,false,true,false,true,false,true,false,true,false,true,false]
  let ci:=BoundaryApplication.Range.build C w
  let ei:=BoundaryApplication.Range.build E w
  let prepared:=MaskedCluster.prepare C.stateCount E.stateCount
  let book:=MaskedCluster.ReplayMaps.prepare C.stateCount E.stateCount
  let target:=Array.ofFn (fun i : Fin 12=>decide (i.val=4))
  let counts:=MaskedProgression.build target 0 12 (prepared.K*2)
  let mut live:=Array.ofFn (fun i : Fin 12=>decide (i.val=0 ∨ i.val=2 ∨ i.val=4 ∨ i.val=7))
  let mut idx:=(MaskedMutableProgression.build live 0 12 (prepared.K*2)).index
  let extra:=Cluster.denseBankExtra C.stateCount E.stateCount prepared.K
  let mut banks:=0
  let mut cells:=0
  let mut direct:=0
  for version in List.range 3 do
    for window in [MaskedCluster.SourceWindow.mk true 0 12,⟨true,2,3⟩,⟨false,0,12⟩] do
      let got:=Cluster.compileDenseBank C E book prepared ci ei 0 2 2 6 6 10 1 true idx target counts.counts window
      let old:=MaskedCluster.Mutable.compileDenseBank C E book prepared ci ei 0 2 2 6 6 10 1 true idx target counts.counts window
      check (got.1.2=old.2) "bank old counter changed"
      check (got.2≤old.2+extra+3) "bank full construction additive bound"
      for key in List.ofFn (fun i : Fin (2*MaskedCluster.ReplayMaps.count C.stateCount E.stateCount)=>i) do
        for i in List.ofFn (fun i : Fin (2*(MaskedClusterStage.dfa C E).stateCount)=>i) do
          for j in List.ofFn (fun i : Fin (2*(MaskedClusterStage.dfa C E).stateCount)=>i) do
            check (got.1.1.view key i j=old.1.view key i j) "bank cell changed"
            cells:=cells+1
      for gate in [false,true] do
        let key:=MaskedCluster.code _ gate
          (MaskedCluster.ReplayMaps.encode (MaskedCluster.ReplayMaps.one C.stateCount E.stateCount))
        for im in [false,true] do
          for om in [false,true] do
            for i in List.ofFn (fun i : Fin (MaskedClusterStage.dfa C E).stateCount=>i) do
              for j in List.ofFn (fun i : Fin (MaskedClusterStage.dfa C E).stateCount=>i) do
                let expected:=directCell C E w live target (window.gate gate) im om
                  (MaskedClusterStage.decode C E i) (MaskedClusterStage.decode C E j)
                check (got.1.1.view key (MaskedCluster.code _ im i) (MaskedCluster.code _ om j)=expected)
                  s!"bank literal witness version={version}, modes={im}/{om}, states={i.val}/{j.val}"
                direct:=direct+1
      banks:=banks+1
    let p:=if version=0 then 0 else 4
    idx:=(MaskedMutableProgression.erase idx p).index
    live:=live.setIfInBounds p false
  IO.println s!"construction dense banks: rebuilt={banks}, all cell comparisons={cells}, literal checks={direct}"
  flush

def main : IO Unit := do
  let start←IO.monoMsNow
  runOrbits
  runWindows
  runSystems
  runPhases
  runBanks
  let finish←IO.monoMsNow
  IO.println s!"periodic construction audit passed in {finish-start} ms"

end REWB.PeriodicConstruction.Audit

def main : IO Unit := REWB.PeriodicConstruction.Audit.main
