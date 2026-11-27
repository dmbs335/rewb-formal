import REWB.ResidualActualFullCostMatcherCost
import REWB.Reference

/-! Composite audit modes, with stage markers flushed before work.
The default regular mode checks actual dispatch of an already constructed
finite form list on 32 words. normalize and independent isolate the
original expensive cases; full retains the original combined cases.
independent-stages diagnoses the two actual row factories and endpoint
query separately. No mode evaluates proof-only bound coefficients.

Run through audits/run_full_matcher_composite.sh for a process address
space limit and a wall-clock limit. A limited/failed diagnostic remains
a failure; it is never silently converted to a successful regression. -/
namespace REWB.ResidualActual.FullCost.Matcher.Audit
open REWB.BoundaryRange REWB.OneUseRange

/-- The runtime flag prevents expensive diagnostic calls with a closed
pattern from being evaluated as module-initialization constants. Normal
invocation uses true; --reject separately exercises the negative flag. -/
def automaton (accepted : Bool) : DFA (Fin 2) :=
  ⟨1,0,fun _ _=>0,fun _=>accepted⟩

def none : DFA (Fin 2) := automaton false

def pattern (A : DFA (Fin 2)) : SevenDFA (Fin 2) :=
  ⟨A,A,A,A,A,A,A⟩

def check (ok : Bool) (label : String) : IO Unit :=
  unless ok do throw (IO.userError label)

def say (s : String) : IO Unit := do
  IO.println s
  (←IO.getStdout).flush

def words : List (Word (Fin 2)) :=
  ((List.range 5).flatMap fun n=>(List.range (2^n)).map fun code=>
    (List.range n).map fun i=>if code/(2^i)%2=0 then (0 : Fin 2) else 1)++
    [List.replicate 5 (0 : Fin 2)]

def regular (accepted : Bool) : IO Unit := do
  say "regular: BEGIN actual compiled-form/list dispatch; normalization is separate"
  let begin←IO.monoMsNow
  let A:=automaton accepted
  check (words.length=32) "regular fixture count"
  for word in words do
    let text:=word.toArray
    say s!"regular: START direct form-list calls n={text.size}"
    let out:=Matcher.run [.regular none,.regular A] text 0
    let rejected:=Matcher.run [.regular none] text 0
    check (out.answer==accepted) s!"regular disjunction length {text.size}"
    check (!rejected.answer) s!"regular rejection length {text.size}"
    check (out.accountedWork=(3*text.size+8)*2+1) "actual finite-list work sum"
    check (out.fixedPatternBuilds=0 && rejected.fixedPatternBuilds=0)
      "direct regular path unexpectedly built row actions"
    say s!"regular: PASS n={text.size}, work={out.accountedWork}"
  let finish←IO.monoMsNow
  say s!"regular: COMPLETE fixtures=32, mismatches=0, elapsed={finish-begin} ms"
  say "regular: no normalization or independent fixture is claimed by this mode"

structure Counts where
  regular : Nat := 0
  once : Nat := 0
  sameValue : Nat := 0
  independent : Nat := 0
  nested1 : Nat := 0
  nested2 : Nat := 0
  deriving Repr

def countForm (counts : Counts) : CompleteNormalization.Form (Fin 2)→Counts
  | .regular _ => {counts with regular:=counts.regular+1}
  | .once _ _ _ _ => {counts with once:=counts.once+1}
  | .sameValue _ => {counts with sameValue:=counts.sameValue+1}
  | .independent _ => {counts with independent:=counts.independent+1}
  | .nested1 _ => {counts with nested1:=counts.nested1+1}
  | .nested2 _ => {counts with nested2:=counts.nested2+1}

def normalize (accepted : Bool) : IO Unit := do
  say "normalize: BEGIN original atom pattern; compilation is outside the returned text ledger"
  let begin←IO.monoMsNow
  let expr : Expr (Fin 2) := .atom (automaton accepted)
  say "normalize: START isolated marked source-DFA precursor probe"
  let source:=RegularDFA.sourceDFA expr
  say s!"normalize: precursor READY states={source.stateCount}; Matcher.compile will reconstruct its own source DFA"
  say "normalize: START Matcher.compile over all control shapes"
  let compiled:=Matcher.compile expr
  let counts:=compiled.foldl countForm ({} : Counts)
  say s!"normalize: compile READY forms={compiled.length}, constructors={reprStr counts}"
  for word in words do
    let text:=word.toArray
    say s!"normalize: START Matcher.run on compiled output n={text.size}"
    let out:=Matcher.run compiled text 0
    check (out.answer==accepted) s!"normalized atom semantics length {text.size}"
    say s!"normalize: PASS n={text.size}, work={out.accountedWork}, builds={out.fixedPatternBuilds}"
  let finish←IO.monoMsNow
  say s!"normalize: COMPLETE source precursor=1, compilation=1, compiled-list fixtures=32, mismatches=0, elapsed={finish-begin} ms"

def independent (accepted : Bool) : IO Unit := do
  say "independent: BEGIN original empty independent form, actual whole dispatch"
  let begin←IO.monoMsNow
  let P:=pattern (automaton accepted)
  say "independent: START Matcher.run; includes reversed row, forward row, gap aggregate and endpoint scan"
  let out:=Matcher.run [.regular none,.independent P] (#[] : Array (Fin 2)) 0
  say s!"independent: Matcher.run READY answer={out.answer}, work={out.accountedWork}, builds={out.fixedPatternBuilds}"
  say "independent: START literal/reference comparison"
  check (out.answer==Reference.independent P []) "actual independent/reference mismatch"
  check (out.answer==accepted) "empty independent capture semantics"
  check (out.fixedPatternBuilds>0 && out.accountedWork>0) "actual independent counters missing"
  let finish←IO.monoMsNow
  say s!"independent: COMPLETE fixtures=1, mismatches=0, elapsed={finish-begin} ms"

/-- Stage diagnostic only: it executes the same component calls as
Independent.prepare/execute, with IO markers between them. The independent
mode above is the actual public whole-dispatch regression. -/
def independentStages (accepted : Bool) : IO Unit := do
  say "independent-stages: BEGIN component diagnosis, not a whole-dispatch pass"
  let begin←IO.monoMsNow
  let P:=pattern (automaton accepted)
  let text : Array (Fin 2) := #[]
  let marks:=MaskedAllStart.Rows.full text.size
  say "independent-stages: START reverse DFA constructors"
  let B:=Automata.reverse P.B
  let C:=Automata.reverse P.C
  let A:=Automata.reverse P.A
  say s!"independent-stages: reverse DFAs READY states={B.stateCount}/{C.stateCount}/{A.stateCount}"
  say "independent-stages: START actual reversed FullCost.Rows.row"
  let ends:=MaskedAllStart.FullCost.Rows.row B C A text.reverse 0 marks marks
  say s!"independent-stages: reversed row READY bits={ends.1.bits.size}, work={ends.2}"
  say "independent-stages: START actual forward FullCost.Rows.row"
  let starts:=MaskedAllStart.FullCost.Rows.row P.F P.G P.H text 0 marks marks
  say s!"independent-stages: forward row READY bits={starts.1.bits.size}, work={starts.2}"
  say "independent-stages: START actual regular-gap suffix aggregate"
  let suffix:=FarAggregate.build P.D text starts.1.bits
  say s!"independent-stages: suffix aggregate READY work={suffix.work}"
  let idx : ResidualActual.Independent.Index :=
    ⟨text.size,ends.1.bits,suffix,ends.1.work+starts.1.work+suffix.work+4*text.size+12,
      ends.1.fixedPatternBuilds+starts.1.fixedPatternBuilds+3⟩
  say "independent-stages: START actual endpoint scan"
  let checked:=ResidualCached.any (ResidualActual.Independent.query idx) (List.range (idx.length+1))
  check (checked.1==Reference.independent P []) "staged independent/reference mismatch"
  let finish←IO.monoMsNow
  say s!"independent-stages: COMPLETE answer={checked.1}, query work={checked.2}, elapsed={finish-begin} ms"
  say "independent-stages: component completion does not replace the independent mode"

/-- The original combined fixture set remains available unchanged in
scope: 32 regular/list/solve cases, followed by the empty independent case.
Additional prints isolate each call; normal invocation uses accepted=true. -/
def full (accepted : Bool) : IO Unit := do
  say "full: BEGIN original combined diagnostic; normalizer is rerun per source solve"
  let begin←IO.monoMsNow
  let A:=automaton accepted
  check (words.length=32) "original regular fixture count"
  for word in words do
    let text:=word.toArray
    say s!"full: START original direct list calls n={text.size}"
    let out:=Matcher.run [.regular none,.regular A] text 0
    let rejected:=Matcher.run [.regular none] text 0
    check (out.answer==accepted && !rejected.answer) "original direct list answer"
    say s!"full: START original Matcher.solve (.atom A) n={text.size}"
    let expr : Expr (Fin 2) := (CompleteNormalization.Form.regular A).expr
    let normalized:=Matcher.solve expr text 0
    check (normalized.answer==accepted) s!"original normalization length {text.size}"
    check (out.accountedWork=(3*text.size+8)*2+1) "original finite-list work sum"
    -- Normalization enumerates all control-shape families, including
    -- rejecting nonregular forms. Its build count need not be zero.
    -- The old zero-build assertion is valid only for direct regular lists.
    check (out.fixedPatternBuilds=0 && rejected.fixedPatternBuilds=0)
      "original direct regular path unexpectedly built row actions"
    say s!"full: original regular/list/normalization PASS n={text.size}, normalized builds={normalized.fixedPatternBuilds}"
  independent accepted
  let finish←IO.monoMsNow
  say s!"full: COMPLETE original regular fixtures=32, independent fixtures=1, elapsed={finish-begin} ms"

end REWB.ResidualActual.FullCost.Matcher.Audit

def main (args : List String) : IO Unit := do
  let mode:=args.headD "regular"
  REWB.ResidualActual.FullCost.Matcher.Audit.say s!"composite audit: ENTER main mode={mode}"
  let accepted := !((args.drop 1).contains "--reject")
  match mode with
  | "regular" => REWB.ResidualActual.FullCost.Matcher.Audit.regular accepted
  | "normalize" => REWB.ResidualActual.FullCost.Matcher.Audit.normalize accepted
  | "independent" => REWB.ResidualActual.FullCost.Matcher.Audit.independent accepted
  | "independent-stages" => REWB.ResidualActual.FullCost.Matcher.Audit.independentStages accepted
  | "full" => REWB.ResidualActual.FullCost.Matcher.Audit.full accepted
  | _ => throw (IO.userError "mode must be regular, normalize, independent, independent-stages, or full")
