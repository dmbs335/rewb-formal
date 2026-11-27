import REWB.PeriodicActualFullCostBranchCost
import REWB.Reference

/-! Bounded actual primitive-installation regression. Non-cubic P1
preparations/joins preserve all old counters. P2 additionally executes a
real positive period-one run. The known expensive positive P1 end-to-end
path is isolated in periodic_actual_diagnostic and is not reported as
passing here. Proof-only coefficient families are never evaluated. -/
namespace REWB.PeriodicActual.FullCost.Audit

def any : DFA (Fin 2) := ⟨1,0,fun _ _=>0,fun _=>true⟩
def pattern : SevenDFA (Fin 2) := ⟨any,any,any,any,any,any,any⟩

def check (ok : Bool) (label : String) : IO Unit :=
  unless ok do throw (IO.userError label)

def say (s : String) : IO Unit := do
  IO.println s
  (←IO.getStdout).flush

def sameJoin (x y : CountedJoin.Result) : Bool :=
  x.value.answer==y.value.answer && x.value.tests==y.value.tests &&
  x.value.eventVisits==y.value.eventVisits && x.value.textVisits==y.value.textVisits &&
  x.value.nodes==y.value.nodes && x.sortSteps==y.sortSteps

def sameBranch (x y : PeriodicActual.BranchResult) : Bool :=
  sameJoin x.joined y.joined && x.preparationWork==y.preparationWork &&
    x.constructionWork==y.constructionWork

def run : IO Unit := do
  let begin←IO.monoMsNow
  let cases : List (Word (Fin 2)×Nat) := [([],0),([],2),([0,1,1,0],2)]
  for v in cases do
    let text:=v.1.toArray
    let f:=ArrayText.read text (0 : Fin 2)
    say s!"refined P1 non-cubic: start n={text.size}, Q={v.2}"
    let long:=Long.solve pattern f text.size v.2
    let oldLong:=PeriodicActual.Long.solve pattern f text.size v.2
    let short:=Short.solve pattern f text.size v.2
    let oldShort:=PeriodicActual.Short.solve pattern f text.size v.2
    check (sameBranch long.1 oldLong) "refined Long changed old payload/counters"
    check (sameBranch short.1 oldShort) "refined Short changed old payload/counters"
    check (!long.1.answer && !short.1.answer) "non-cubic P1 accepted"
    check (long.2>0 && short.2>0) "refined P1 construction counters absent"
    say s!"refined P1 non-cubic: passed n={text.size}, long work={long.2}, short work={short.2}"
  let positive : Word (Fin 2) := [0,0,0]
  let text:=positive.toArray
  let f:=ArrayText.read text (0 : Fin 2)
  say "refined P2 positive: start n=3, Q=1"
  let p2:=P2.solve pattern f 3 1
  let old:=PeriodicActual.P2.solve pattern f 3 1
  check (p2.1=old) "refined P2 changed full old Bool/work pair"
  check (p2.1.1 && Reference.nested2 pattern positive) "refined P2 positive/reference failure"
  check (p2.2≥p2.1.2) "refined P2 omitted old ledger"
  say s!"refined P2 positive: passed, old work={old.2}, construction work={p2.2}"
  let empty:=ArrayText.read (#[] : Array (Fin 2)) (0 : Fin 2)
  let cubic:=Cubic.solve pattern empty 0 0
  let oldCubic:=PeriodicActual.Cubic.solve pattern empty 0 0
  check (cubic.1=oldCubic && !cubic.1.1 && cubic.2>0) "refined cubic empty full-pair failure"
  let finish←IO.monoMsNow
  say s!"refined periodic: P1 non-cubic fixtures=3, actual positive P2=1, cubic empty=1, mismatches=0, elapsed={finish-begin} ms"
  say "Positive P1 end-to-end timing is a separate unresolved diagnostic; no machine-bit or memory-management bound is asserted."

end REWB.PeriodicActual.FullCost.Audit

def main : IO Unit := REWB.PeriodicActual.FullCost.Audit.run
