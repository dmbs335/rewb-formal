import REWB.ResidualActualRegression

/-! Bounded compiled-code audit of the new projection, concrete epsilon
reductions and the actual independent join operation. The all-start
factories themselves are covered by masked_all_start_correct_smoke;
the huge fixed-pattern residual row universes are checked universally
by the kernel and are not re-enumerated in this default runtime gate. -/
namespace REWB.ResidualActual.Audit
open REWB.BoundaryRange REWB.OneUseRange

def any : DFA (Fin 2) := ⟨1,0,fun _ _=>0,fun _=>true⟩
def odd : DFA (Fin 2) := ⟨2,0,fun q _=>if q=0 then 1 else 0,fun q=>q==1⟩

def words : Nat→List (Word (Fin 2))
  | 0 => [[]]
  | n+1 => (words n).flatMap fun w=>[0::w,1::w]

def mask (n mode : Nat) : Array Bool :=
  ((List.range (if mode=3 then n/2 else n+1)).map fun i=>
    if mode=0 then false else if mode=1 then true else decide (i%3=1)).toArray

def run : IO Unit := do
  let begin←IO.monoMsNow
  let outer:=Table.build fun i : Fin 4=>
    let inner:=Table.build fun j : Fin 3=>(i.val*7+j.val,2)
    (inner,inner.work+3)
  let cooked:=project outer fun _ cells=>project cells fun _ x=>x+9
  let mut projectionChecks:=0
  for i in List.finRange 4 do
    for j in List.finRange 3 do
      unless Table.get (Table.get cooked i) j=i.val*7+j.val+9 do
        throw (IO.userError "cached projection mismatch")
      projectionChecks:=projectionChecks+1
  let machines : List (DFA (Fin 2)) := [any,epsilon,odd,Regression.oneLetter 0]
  let patterns : List (FiveDFA (Fin 2)) :=
    [⟨any,any,any,any,any⟩,
     ⟨epsilon,Regression.oneLetter 0,any,odd,epsilon⟩,
     ⟨odd,any,epsilon,any,odd⟩,
     ⟨epsilon,epsilon,epsilon,epsilon,epsilon⟩]
  let mut joinChecks:=0
  let mut joinHits:=0
  let mut reductions:=0
  let mut regularChecks:=0
  for n in List.range 5 do
    for w in words n do
      let text:=w.toArray
      for P in patterns do
        unless Reference.same P w=Reference.nested1 (samePattern P) w do
          throw (IO.userError "same-value epsilon reduction mismatch")
        unless FullMatcher.once P.A P.B P.C P.E w=Reference.nested2 (oncePattern P.A P.B P.C P.E) w do
          throw (IO.userError "once epsilon reduction mismatch")
        reductions:=reductions+2
      for D in machines do
        let regular:=Matcher.form (.regular D) text 0
        unless regular.answer=Reference.acceptB D w do throw (IO.userError "regular actual form mismatch")
        regularChecks:=regularChecks+1
        for em in List.range 4 do
          let endMarks:=mask n em
          let reversedEnds:=Array.ofFn fun i : Fin (n+1)=>FarAggregate.bit endMarks (n-i.val)
          for sm in List.range 4 do
            let starts:=mask n sm
            let aggregate:=FarAggregate.build D text starts
            let idx : Independent.Index:=⟨n,reversedEnds,aggregate,aggregate.work,0⟩
            unless aggregate.work≤(6*D.stateCount+7)*(n+1) do
              throw (IO.userError "independent gap aggregate work mismatch")
            for t in List.range (n+2) do
              let out:=Independent.query idx t
              let expected:=decide (t≤n) && FarAggregate.bit endMarks t &&
                (List.range (n+1)).any fun s=>decide (t≤s) && FarAggregate.bit starts s &&
                  Reference.acceptB D (Spec.slice w t s)
              unless out.1=expected do
                throw (IO.userError s!"independent join mismatch n={n},end={t},endmask={em},startmask={sm}")
              unless out.2≤10 do throw (IO.userError "independent query work mismatch")
              joinChecks:=joinChecks+1
              if out.1 then joinHits:=joinHits+1
  let finish←IO.monoMsNow
  IO.println s!"actual residual components: projections={projectionChecks}, epsilon reductions={reductions}, regular dispatches={regularChecks}, joins={joinChecks}, positive joins={joinHits}, mismatches=0, elapsed={finish-begin} ms"
  IO.println "All six production branches are kernel proved; this bounded component audit does not enumerate the large residual row factories."

end REWB.ResidualActual.Audit

def main : IO Unit := REWB.ResidualActual.Audit.run

#print axioms REWB.ResidualActual.project_get
#print axioms REWB.ResidualActual.project_work
#print axioms REWB.ResidualActual.P1.inputs_get
#print axioms REWB.ResidualActual.P1.inputs_ready
#print axioms REWB.ResidualActual.P1.inputs_work
#print axioms REWB.ResidualActual.P1.inputs_builds
#print axioms REWB.ResidualActual.P2.inputs_forward
#print axioms REWB.ResidualActual.P2.inputs_backward
#print axioms REWB.ResidualActual.P2.inputs_ready
#print axioms REWB.ResidualActual.P2.inputs_work
#print axioms REWB.ResidualActual.P2.forwardRows_work
#print axioms REWB.ResidualActual.P2.backwardRows_work
#print axioms REWB.ResidualActual.P2.inputs_builds
#print axioms REWB.ResidualActual.P1.execute_correct
#print axioms REWB.ResidualActual.P1.execute_inputWork
#print axioms REWB.ResidualActual.P1.execute_builds
#print axioms REWB.ResidualActual.P1.execute_accountedWork
#print axioms REWB.ResidualActual.P1.auto_correct
#print axioms REWB.ResidualActual.P2.execute_correct
#print axioms REWB.ResidualActual.P2.execute_inputWork
#print axioms REWB.ResidualActual.P2.execute_builds
#print axioms REWB.ResidualActual.P2.execute_accountedWork
#print axioms REWB.ResidualActual.P2.auto_correct
#print axioms REWB.ResidualActual.auto_accountedWork
#print axioms REWB.ResidualActual.epsilon_accepts
#print axioms REWB.ResidualActual.samePattern_correct
#print axioms REWB.ResidualActual.oncePattern_correct
#print axioms REWB.ResidualActual.same_correct
#print axioms REWB.ResidualActual.once_correct
#print axioms REWB.ResidualActual.Independent.joined_sound
#print axioms REWB.ResidualActual.Independent.words_joined
#print axioms REWB.ResidualActual.Independent.joined_correct
#print axioms REWB.ResidualActual.Independent.ends_correct
#print axioms REWB.ResidualActual.Independent.suffix_correct
#print axioms REWB.ResidualActual.Independent.query_correct
#print axioms REWB.ResidualActual.Independent.query_work
#print axioms REWB.ResidualActual.Independent.execute_correct
#print axioms REWB.ResidualActual.Independent.execute_work
#print axioms REWB.ResidualActual.Independent.prepare_work
#print axioms REWB.ResidualActual.Independent.execute_builds
#print axioms REWB.ResidualActual.Matcher.form_correct
#print axioms REWB.ResidualActual.Matcher.run_correct
#print axioms REWB.ResidualActual.Matcher.run_work
#print axioms REWB.ResidualActual.Matcher.run_builds
#print axioms REWB.ResidualActual.Matcher.solve_correct
#print axioms REWB.ResidualActual.Matcher.matchWord_correct
#print axioms REWB.ResidualActual.Matcher.correctMatcher
#print axioms REWB.ResidualActual.Regression.independent_different_captures
#print axioms REWB.ResidualActual.Regression.independent_wrong_order
#print axioms REWB.ResidualActual.Regression.same_three_copies
#print axioms REWB.ResidualActual.Regression.once_empty_capture
#print axioms REWB.ResidualActual.Regression.cached_projection
#print axioms REWB.ResidualActual.Regression.form_eq_reference
#print axioms REWB.ResidualActual.Regression.source_expression_eq_reference
