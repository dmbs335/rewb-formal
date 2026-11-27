import REWB.PeriodicConstructionCacheRegression

/-! Reproducible bounded runtime comparison. Literal word scans are audit
references only. Production calls use a reader of an already materialized
array, including shifted and out-of-bounds positions with false fallback. -/
namespace REWB.PeriodicConstruction.Cache.Audit
open REWB.PeriodicConstruction.Cache.Regression

def check (ok : Bool) (label : String) : IO Unit :=
  unless ok do throw (IO.userError label)

def tableData (d : DFA Bool) (t : PeriodicCache.Table d) :=
  t.map fun phase=>phase.map fun row=>row.map Fin.val

def dfaData (d : DFA Bool) :=
  (d.stateCount,d.initial.val,(List.range d.stateCount).map fun i=>
    let v:=PeriodicCache.state d i
    (d.final v,(d.step v false).val,(d.step v true).val))

def sameShared (P : SevenDFA Bool) (x y : FullyCachedP2.Shared P) : Bool :=
  dfaData x.a=dfaData y.a && dfaData x.h=dfaData y.h &&
  tableData x.a x.ta=tableData y.a y.ta &&
  tableData P.B x.tb=tableData P.B y.tb &&
  tableData P.C x.tc=tableData P.C y.tc &&
  tableData P.D x.td=tableData P.D y.td &&
  tableData P.F x.tf=tableData P.F y.tf &&
  tableData P.G x.tg=tableData P.G y.tg &&
  tableData x.h x.th=tableData y.h y.th && x.equality=y.equality

def words (n : Nat) : List (Word Bool) :=
  (List.range (2^n)).map fun bits=>
    List.ofFn (fun i : Fin n=>decide ((bits/2^i.val)%2=1))

def literal (f : Nat→Bool) (a n : Nat) : Word Bool :=
  (List.range n).map fun i=>f (a+i)

def testTransitions (d : DFA Bool) (f : Nat→Bool) (q : Nat) : IO Nat := do
  let out:=transitions d f q
  let old:=PeriodicCache.build d f q
  check (out.1=old) "transition table or old counter changed"
  check (out.2=transitionsCost d.stateCount q) "transition exact work"
  check (out.2≤64*(d.stateCount+1)*(q+1)^2) "transition quadratic bound"
  let mut cells:=0
  for a in List.range q do
    for i in List.range d.stateCount do
      let v:=PeriodicCache.state d i
      for r in List.range (q+1) do
        let expected:=d.run v (literal f a r)
        check (PeriodicCache.lookup d out.1.1 a r v=some expected)
          s!"literal transition q={q}, phase={a}, state={i}, length={r}"
        cells:=cells+1
  pure cells

def testEquality (f : Nat→Bool) (q : Nat) : IO Nat := do
  let out:=equality f q
  let old:=PhaseEqualityCache.build f q
  check (out.1=old) "equality table or old counter changed"
  check (out.2=equalityCost q) "equality exact work"
  check (out.2≤64*(q+1)^3) "equality cubic bound"
  let mut cells:=0
  for a in List.range q do
    for c in List.range q do
      for r in List.range (q+1) do
        let expected:=decide (literal f a r=literal f c r)
        check (PhaseEqualityCache.lookup out.1.1 a c r=some expected)
          s!"literal equality q={q}, phases={a}/{c}, length={r}"
        cells:=cells+1
  pure cells

def testContexts (P : SevenDFA Bool) (w : Word Bool) :
    IO (BoundaryContexts.Index P) := do
  let out:=contexts P w
  let old:=BoundaryContexts.build P w
  check (out.1.2=old.2 && out.1.1.prefixes=old.1.prefixes &&
    out.1.1.suffixes=old.1.suffixes) "whole exterior context or old counter changed"
  check (out.2=contextsCost P.H.stateCount w.length) "context exact work"
  check (out.2≤64*old.2) "context linear bound"
  check (out.1.1.prefixes.size=w.length+1 && out.1.1.suffixes.size=w.length+1)
    "context boundary sizes"
  for cut in List.range (w.length+1) do
    check (BoundaryContexts.prefixAt P out.1.1 cut=P.A.run P.A.initial (w.take cut))
      "literal prefix state"
    for i in List.range P.H.stateCount do
      let v:=PeriodicCache.state P.H i
      check (DFACut.read P.H (BoundaryContexts.suffixAt P out.1.1 cut) v=
        P.H.run v (w.drop cut)) "literal suffix map"
  pure out.1.1

def testPrepare (P : SevenDFA Bool) (f : Nat→Bool) (q : Nat)
    (I : BoundaryContexts.Index P) (lo hi : Nat) : IO Unit := do
  let out:=prepareAt P f q I lo hi
  let old:=BoundaryContexts.countedPrepareAt P f q I lo hi
  check (out.1.2=old.2 && sameShared P out.1.1 old.1)
    "whole per-run cache or old counter changed"
  check (out.2=prepareAtCost P q) "preparation exact work"
  check (out.2≤128*(FullyCachedP2.stateSum P+1)*(q+1)^3) "preparation cubic bound"
  check (out.2≤prepareCoefficient P*(old.2+1)) "preparation old-ledger bound"
  if 0<q then
    check (out.2≤(2*prepareCoefficient P)*old.2) "positive-period old-ledger bound"
  else
    check (old.2=0 && out.2=72) "zero-period overhead"

def runSmall : IO Unit := do
  let patterns : List (SevenDFA Bool) :=
    [all,mixed,⟨seen,seen,seen,seen,seen,seen,seen⟩,
      ⟨parity,last,universal,parity,last,seen,last⟩]
  let mut transitionTables:=0
  let mut equalityTables:=0
  let mut transitionCells:=0
  let mut equalityCells:=0
  let mut contextBuilds:=0
  let mut preparations:=0
  for n in List.range 4 do
    for w in words n do
      let text:=w.toArray
      for offset in [0,n/2,n,n+1] do
        let f:=fun i=>read text (offset+i)
        for q in List.range 5 do
          for d in [universal,seen,last,parity] do
            transitionCells:=transitionCells+(←testTransitions d f q)
            transitionTables:=transitionTables+1
          equalityCells:=equalityCells+(←testEquality f q)
          equalityTables:=equalityTables+1
      for P in patterns do
        let I←testContexts P w
        contextBuilds:=contextBuilds+1
        for bounds in [(0,0),(0,n),(n,n),(n+1,n+2),(n/2,n/2)] do
          let f:=fun i=>read text (bounds.1+i)
          for q in List.range 5 do
            testPrepare P f q I bounds.1 bounds.2
            preparations:=preparations+1
  IO.println s!"periodic cache small: transition tables={transitionTables}, literal transition cells={transitionCells}, equality tables={equalityTables}, literal equality cells={equalityCells}, contexts={contextBuilds}, preparations={preparations}"
  (←IO.getStdout).flush

def runDeep : IO Unit := do
  let w:Word Bool:=(List.range 1024).map fun i=>decide (i%3=1)
  let text:=w.toArray
  let I←testContexts mixed w
  let f:=fun i=>read text (37+i)
  let tableCells←testTransitions parity f 17
  let equalityCells←testEquality f 17
  testPrepare mixed f 17 I 37 (w.length-37)
  let out:=prepareAt mixed f 17 I 37 (w.length-37)
  IO.println s!"periodic cache deep: n=1024, period=17, transition cells={tableCells}, equality cells={equalityCells}, old preparation={out.1.2}, construction work={out.2}"
  (←IO.getStdout).flush

def runWide : IO Unit := do
  let d : DFA Bool:=⟨64,0,fun v x=>if x then 0 else v,fun _=>true⟩
  let P : SevenDFA Bool:=⟨d,d,d,d,d,d,d⟩
  let I←testContexts P []
  testPrepare P (fun _=>false) 0 I 0 0
  let empty:=transitions d (fun _=>false) 0
  check (empty.2=6 && empty.1.1.size=0) "wide zero-period table performed state work"
  let cells←testTransitions d (read #[true]) 1
  IO.println s!"periodic cache wide: states=64, zero preparation=72, literal transition cells={cells}"
  (←IO.getStdout).flush

def main : IO Unit := do
  let before←IO.monoMsNow
  runSmall
  runDeep
  runWide
  let after←IO.monoMsNow
  IO.println s!"periodic cache construction audit passed in {after-before} ms"

end REWB.PeriodicConstruction.Cache.Audit

def main : IO Unit := REWB.PeriodicConstruction.Cache.Audit.main
