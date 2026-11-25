import REWB.PeriodicActualBranchCost
import REWB.Reference

/-! Bounded executable audit of the actual external periodic pipeline.
The default has ten small fixtures, thresholds 0/1/2, a genuine period-two
run, positive long/short/P2 witnesses, and rejecting/context-sensitive
machines.  It compares the actual join answer and every old join counter;
selected preparations also compare complete emitted event syntax.
Reference split enumeration is confined to these tiny audit inputs.
No residual/all-start finite row factory is enumerated here. -/
namespace REWB.PeriodicActual.Audit
open REWB.PeriodicAccounting

def any : DFA (Fin 2) := ⟨1,0,fun _ _=>0,fun _=>true⟩
def none : DFA (Fin 2) := ⟨1,0,fun _ _=>0,fun _=>false⟩
def odd : DFA (Fin 2) := ⟨2,0,fun q _=>if q=0 then 1 else 0,fun q=>q==1⟩

def pattern (mode : Nat) : SevenDFA (Fin 2) :=
  ⟨if mode=1 then none else any,any,if mode=2 then odd else any,any,any,any,any⟩

def check (ok : Bool) (label : String) : IO Unit :=
  unless ok do throw (IO.userError label)

def flush : IO Unit := do (←IO.getStdout).flush

def sameJoin (x y : CountedJoin.Result) : Bool :=
  x.value.answer==y.value.answer && x.value.tests==y.value.tests &&
  x.value.eventVisits==y.value.eventVisits && x.value.textVisits==y.value.textVisits &&
  x.value.nodes==y.value.nodes && x.sortSteps==y.sortSteps

structure Fixture where
  label : String
  word : Word (Fin 2)
  Q : Nat
  mode : Nat := 0
  expectLong : Bool := false
  expectShort : Bool := false
  expectP2 : Bool := false
  inspectEvents : Bool := false
  inspectCubic : Bool := false

def fixtures : List Fixture :=
  [⟨"empty-q0",[],0,0,false,false,false,false,true⟩,
   ⟨"empty-q1",[],1,0,false,false,false,false,false⟩,
   ⟨"empty-q2",[],2,0,false,false,false,false,false⟩,
   ⟨"single-q0",[0],0,0,false,false,false,false,false⟩,
   ⟨"unary-cubic",[0,0,0],1,0,false,true,true,true,true⟩,
   ⟨"long-inner",List.replicate 9 0,1,0,true,true,true,false,true⟩,
   ⟨"period-two",[0,1,0,1,0,1],2,0,false,true,true,true,true⟩,
   ⟨"no-cubic-run",[0,1,1,0],2,0,false,false,false,false,false⟩,
   ⟨"reject-prefix",[0,0,0],1,1,false,false,false,false,false⟩,
   ⟨"odd-gap",[0,0,0],1,2,false,false,false,false,false⟩]

def schedules : IO Nat := do
  let mut count:=0
  for q in [0,1,2] do
    let p2:=Choices.p2 q
    let p1:=Choices.p1 q
    check (p2.1.length=q^5 && p1.1.length=q^3) s!"phase cardinality q={q}"
    if q>0 then
      check (p2.2≤39*q^5 && p1.2≤23*q^3) s!"phase construction work q={q}"
    for n in [0,1,4] do
      let src:=Choices.sources q n
      let tgt:=Choices.targets q n
      check (src.1=P1SourceFamily.choices q n) s!"source choice order q={q}, n={n}"
      check (tgt.1.length=(P1PhaseFamily.targets q n).length)
        s!"target choice cardinality q={q}, n={n}"
      if q>0 then
        check (src.2≤15*((n+1)*q) && tgt.2≤35*((n+1)*q^3))
          s!"choice work q={q}, n={n}"
      let short:=Short.sourceChoices n (3*q)
      check (short.1=P1ShortSources.choices n (3*q)) s!"short choice order q={q}, n={n}"
      check (short.2≤9*((n+1)*(3*q))+7*(n+1)+6) s!"short choice work q={q}, n={n}"
      count:=count+1
  return count

def run : IO Unit := do
  let begin←IO.monoMsNow
  let choiceCases←schedules
  let mut cases:=0
  let mut longHits:=0
  let mut shortHits:=0
  let mut p2Hits:=0
  let mut eventBatches:=0
  let mut cubicCalls:=0
  let mut joinCounterComparisons:=0
  for v in fixtures do
    let tick←IO.monoMsNow
    IO.println s!"external periodic start: {v.label}, n={v.word.length}, Q={v.Q}, mode={v.mode}"
    flush
    let P:=pattern v.mode
    let text:=v.word.toArray
    let f:=ArrayText.read text 0
    let n:=text.size
    let long:=Long.solve P f n v.Q
    let oldLong:=CountedSmallPeriodP1.solve P f n v.Q
    check (sameJoin long.joined ⟨oldLong.toResult,oldLong.sortSteps⟩)
      s!"long join result/counters: {v.label}"
    let short:=Short.solve P f n v.Q
    let oldShort:=CountedShortBranch.solve P f n v.Q
    check (sameJoin short.joined ⟨oldShort.toResult,oldShort.sortSteps⟩)
      s!"short join result/counters: {v.label}"
    joinCounterComparisons:=joinCounterComparisons+12
    let p2:=P2.solve P f n v.Q
    let oldP2:=SmallPeriodP2.solve P f n v.Q
    check (p2.1=oldP2.accepted) s!"P2 accepted value: {v.label}"
    check (long.work≤Long.branchCoefficient P*(longExpr P).eval n v.Q)
      s!"long complete branch expression: {v.label}"
    check (short.work≤Short.branchCoefficient P*(shortExpr P).eval n v.Q)
      s!"short complete branch expression: {v.label}"
    check (p2.2≤P2.coefficient P*((p2Expr P).eval n v.Q*logHeight n))
      s!"P2 complete branch expression: {v.label}"
    check (p2.2≤oldP2.runComparisons+oldP2.contextEntries+oldP2.cacheWork+
      (P2.phaseBudget P+52)*oldP2.phaseCalls+5*(2*n*DyadicIndex.heightFor n)+3*n+11)
      s!"P2 actual old-counter inflation: {v.label}"
    let literal1:=Reference.nested1 P v.word
    let literal2:=Reference.nested2 P v.word
    check ((!long.answer || literal1) && (!short.answer || literal1) && (!p2.1 || literal2))
      s!"original literal semantics soundness: {v.label}"
    if v.expectLong then check long.answer s!"missing positive long fixture: {v.label}"
    if v.expectShort then check short.answer s!"missing positive short fixture: {v.label}"
    if v.expectP2 then check p2.1 s!"missing positive P2 fixture: {v.label}"
    if v.label="no-cubic-run" || v.mode=1 then
      check (!long.answer && !short.answer && !p2.1) s!"expected negative fixture: {v.label}"
    if v.label="period-two" then
      check (oldP2.phaseCalls>1) "period-two fixture did not traverse nontrivial phase schedule"
    if v.inspectEvents then
      let lp:=Long.prepare P f n v.Q
      let sp:=Short.prepare P f n v.Q
      check (lp.text=v.word && sp.text=v.word) s!"prepared text: {v.label}"
      check (reprStr lp.sources=reprStr oldLong.events.sources &&
        reprStr lp.targets=reprStr oldLong.events.targets) s!"long actual event syntax/order: {v.label}"
      check (reprStr sp.sources=reprStr oldShort.sources &&
        reprStr sp.targets=reprStr oldShort.targets.events) s!"short actual event syntax/order: {v.label}"
      check (lp.modulus=oldLong.modulus && sp.modulus=1) s!"prepared modulus: {v.label}"
      check (lp.work=long.preparationWork && sp.work=short.preparationWork)
        s!"single-call preparation ledger: {v.label}"
      eventBatches:=eventBatches+4
    if v.inspectCubic then
      let both:=Cubic.solve P f n v.Q
      check (both.1=(oldLong.answer || oldShort.answer)) s!"actual cubic answer: {v.label}"
      check (both.2=long.work+short.work+3) s!"actual cubic combined work: {v.label}"
      check (both.2≤Cubic.coefficient P*(Cubic.expr P).eval n v.Q)
        s!"cubic expression: {v.label}"
      cubicCalls:=cubicCalls+1
    if long.answer then longHits:=longHits+1
    if short.answer then shortHits:=shortHits+1
    if p2.1 then p2Hits:=p2Hits+1
    cases:=cases+1
    let done←IO.monoMsNow
    IO.println s!"external periodic passed: {v.label}; long={long.answer}, short={short.answer}, P2={p2.1}, phaseCalls={oldP2.phaseCalls}, elapsed={done-tick} ms"
    flush
  check (longHits>0 && shortHits>0 && p2Hits>0) "positive branch coverage was not exercised"
  let finish←IO.monoMsNow
  IO.println s!"external periodic: fixtures={cases}, choice schedules={choiceCases}, join answer/counter comparisons={joinCounterComparisons}, event batches={eventBatches}, actual cubic calls={cubicCalls}, long/short/P2 positives={longHits}/{shortHits}/{p2Hits}, mismatches=0, elapsed={finish-begin} ms"
  IO.println "This bounded audit uses tiny literal inputs and at most one two-state gap DFA; it does not enumerate residual/all-start row factories or certify machine-bit/allocation costs."

end REWB.PeriodicActual.Audit

def main : IO Unit := REWB.PeriodicActual.Audit.run
