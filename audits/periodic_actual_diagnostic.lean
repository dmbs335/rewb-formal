import REWB.PeriodicActualBranch
import REWB.Reference

/-! Optional isolated diagnostics for the first nonempty periodic fixture.
This is not a passing regression gate: each mode may be stopped by its
external timeout, and prints exact completed stages before the expensive
operation. No asymptotic coefficient is evaluated. -/
namespace REWB.PeriodicActual.Diagnostic
open REWB.PeriodicConstruction

def any : DFA (Fin 2) := ⟨1,0,fun _ _=>0,fun _=>true⟩
def pattern : SevenDFA (Fin 2) := ⟨any,any,any,any,any,any,any⟩
def word : Word (Fin 2) := [0,0,0]

def say (s : String) : IO Unit := do
  IO.println s
  (←IO.getStdout).flush

def rawTarget : IO AffineProjection.Formula := do
  let f:=ArrayText.read word.toArray (0 : Fin 2)
  say "target: building contexts"
  let contexts:=BoundaryContexts.build pattern word
  say s!"target: contexts complete, entries={contexts.2}"
  let cache:=BoundaryContexts.countedPrepareAt pattern f 1 contexts.1 0 3
  say s!"target: shared cache complete, old work={cache.2}"
  let phase : P1PhaseFamily.Three := ⟨0,0,0⟩
  let raw:=Formula.target pattern 3 1 0 0 cache.1 (P1PhaseFamily.extend 1 0 phase)
  say s!"target: raw DNF complete, clauses={raw.1.length}, atoms={(raw.1.map List.length).sum}, work={raw.2}"
  return raw.1

def run (mode : String) : IO Unit := do
  let begin←IO.monoMsNow
  let f:=ArrayText.read word.toArray (0 : Fin 2)
  if mode="p2" then
    say "P2: starting actual measured solve n3 q1"
    let out:=P2.solve pattern f 3 1
    say s!"P2: actual solve complete, answer={out.1}, work={out.2}"
    unless out.1=Reference.nested2 pattern word do
      throw (IO.userError "P2 literal/reference mismatch")
    say "P2: starting old result comparator"
    let old:=SmallPeriodP2.solve pattern f 3 1
    unless out.1=old.accepted do throw (IO.userError "P2 old answer mismatch")
    say s!"P2: old result comparator complete, phases={old.phaseCalls}"
  else if mode="projection" then
    let mut F←rawTarget
    for k in List.range 5 do
      say s!"projection: starting elimination {k+1}, input clauses={F.length}"
      let out:=CountedProjection.eliminateFormula F
      F:=out.1
      say s!"projection: completed elimination {k+1}, output clauses={F.length}, work={out.2}"
  else if mode="search" then
    let F←rawTarget
    say "search: starting m0 target decision"
    let out:=CountedProjection.search [0] 5 F
    say s!"search: m0 target decision complete, answer={out.1}, work={out.2}"
  else if mode="long" then
    say "Long: starting measured preparation"
    let prep:=Long.prepare pattern f 3 1
    say s!"Long: preparation complete, sources={prep.sources.length}, targets={prep.targets.length}, work={prep.work}"
    say "Long: starting actual join"
    let joined:=Join.run pattern.C prep.modulus 3 prep.text prep.sources prep.targets
    say s!"Long: join complete, answer={joined.1.value.answer}, construction={joined.2}"
  else if mode="short" then
    say "Short: starting measured preparation"
    let prep:=Short.prepare pattern f 3 1
    say s!"Short: preparation complete, sources={prep.sources.length}, targets={prep.targets.length}, work={prep.work}"
    say "Short: starting actual join"
    let joined:=Join.run pattern.C prep.modulus 3 prep.text prep.sources prep.targets
    say s!"Short: join complete, answer={joined.1.value.answer}, construction={joined.2}"
  else
    throw (IO.userError "mode must be p2, projection, search, long or short")
  let finish←IO.monoMsNow
  say s!"isolated diagnostic completed: mode={mode}, elapsed={finish-begin} ms"

end REWB.PeriodicActual.Diagnostic

def main (args : List String) : IO Unit :=
  REWB.PeriodicActual.Diagnostic.run (args.headD "p2")
