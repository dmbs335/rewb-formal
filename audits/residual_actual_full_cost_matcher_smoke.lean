import REWB.ResidualActualFullCostMatcherCost
import REWB.Reference

/-! Bounded end-to-end smoke for the construction-counted dispatcher.
Regular normalized forms and finite-list composition run on 32 words.
One empty-word independent form executes the two actual FullCost rows,
the backwards gap aggregate and endpoint scan. Universal nested-row
factories and proof-only coefficient families are not enumerated here;
their exactness and bounds are kernel checked separately. -/
namespace REWB.ResidualActual.FullCost.Matcher.Audit

def any : DFA (Fin 2) := ⟨1,0,fun _ _=>0,fun _=>true⟩
def none : DFA (Fin 2) := ⟨1,0,fun _ _=>0,fun _=>false⟩
def independent : SevenDFA (Fin 2) := ⟨any,any,any,any,any,any,any⟩

def check (ok : Bool) (label : String) : IO Unit :=
  unless ok do throw (IO.userError label)

def flush : IO Unit := do (←IO.getStdout).flush

def run : IO Unit := do
  let begin←IO.monoMsNow
  let words : List (Word (Fin 2)) :=
    ((List.range 5).flatMap fun n=>(List.range (2^n)).map fun code=>
      (List.range n).map fun i=>if code/(2^i)%2=0 then (0 : Fin 2) else 1)++
      [List.replicate 5 (0 : Fin 2)]
  check (words.length=32) "regular fixture count"
  for word in words do
    let text:=word.toArray
    let out:=Matcher.run [.regular none,.regular any] text 0
    let rejected:=Matcher.run [.regular none] text 0
    let expr : Expr (Fin 2) := (CompleteNormalization.Form.regular any).expr
    let normalized:=Matcher.solve expr text 0
    check out.answer s!"regular disjunction length {text.size}"
    check (!rejected.answer) s!"regular rejection length {text.size}"
    check normalized.answer s!"actual normalization length {text.size}"
    check (out.accountedWork=(3*text.size+8)*2+1) "actual finite-list work sum"
    check (out.fixedPatternBuilds=0 && rejected.fixedPatternBuilds=0 &&
      normalized.fixedPatternBuilds=0) "regular path unexpectedly built row actions"
    IO.println s!"full-cost regular/list passed: n={text.size}"
    flush
  IO.println "full-cost independent empty: starting actual reversed and forward rows"
  flush
  let tick←IO.monoMsNow
  let out:=Matcher.run [.regular none,.independent independent] (#[] : Array (Fin 2)) 0
  check (out.answer=Reference.independent independent []) "actual independent/reference mismatch"
  check out.answer "empty independent capture must be accepted"
  check (out.fixedPatternBuilds>0 && out.accountedWork>0) "actual independent counters missing"
  let finish←IO.monoMsNow
  IO.println s!"full-cost independent empty passed: work={out.accountedWork}, action builds={out.fixedPatternBuilds}, elapsed={finish-tick} ms"
  IO.println s!"full-cost composite: regular fixtures=32, actual independent fixtures=1, mismatches=0, elapsed={finish-begin} ms"
  IO.println "This probe does not enumerate universal bound families or the full nested variant bank; machine-bit, allocation and GC costs are outside the claimed ledger."
  flush

end REWB.ResidualActual.FullCost.Matcher.Audit

def main : IO Unit := REWB.ResidualActual.FullCost.Matcher.Audit.run
