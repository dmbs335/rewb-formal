import REWB.PeriodicConstructionRunsCost

/-! Bounded compiled comparison of complete old/new enumeration pairs
and cubic outputs, including empty input, zero thresholds and periods
beyond the text. Numeric work checks use only the explicit polynomial
run envelope, with no proof-only fixed-pattern coefficient evaluation. -/
namespace RunConstructionSmoke
open REWB
open REWB.RunGeometry

def words : Nat→List (List Bool)
  | 0=>[[]]
  | n+1=>
    let rest:=words n
    rest.map (false::·)++rest.map (true::·)

def describe (runs : List Bounds) : List (Nat×Nat×Nat) :=
  runs.map fun R=>(R.lo,R.hi,R.period)

def probe (text : Array Bool) (Q : Nat) : IO (Nat×Nat×Nat) := do
  let n:=text.size
  let f:=fun i=>text[i]?.getD false
  let old:=SmallPeriodRuns.enumerate f n Q
  let actual:=PeriodicConstruction.Runs.enumerate f n Q
  if describe actual.1.1!=describe old.1 || actual.1.2!=old.2 then
    throw (IO.userError s!"run pair mismatch n={n} Q={Q}")
  let cubic:=PeriodicConstruction.Runs.cubic f n Q
  let expected:=old.1.filter (fun R=>decide (3*R.period≤R.hi-R.lo))
  if describe cubic.1.1!=describe expected || cubic.1.2!=old.2 then
    throw (IO.userError s!"cubic pair mismatch n={n} Q={Q}")
  let bound:=160*(Q*(n+(n+1)*(2*Q*(Q+1)+1))+n+Q+1)
  if actual.2>bound ∨ cubic.2>bound ∨ actual.2=0 ∨ cubic.2=0 then
    throw (IO.userError s!"run work mismatch n={n} Q={Q}")
  return (old.1.length,old.2,cubic.2)

def main : IO Unit := do
  let begin←IO.monoMsNow
  let mut calls:=0
  let mut runs:=0
  let mut comparisons:=0
  let mut work:=0
  for n in List.range 6 do
    for w in words n do
      for q in List.range 4 do
        let ⟨r,c,a⟩←probe w.toArray q
        calls:=calls+1
        runs:=runs+r
        comparisons:=comparisons+c
        work:=work+a
  IO.println s!"run constructors: {calls} cases, {runs} runs, old comparisons={comparisons}, full work={work}, 0 mismatches"
  let homogeneous:=Array.replicate 1024 false
  let alternating:=((List.range 1024).map (fun i=>decide (i%2=0))).toArray
  for text in [homogeneous,alternating] do
    let ⟨r,c,a⟩←probe text 4
    IO.println s!"run constructors deep n={text.size} Q=4 runs={r} comparisons={c} full work={a}: PASS"
  let elapsed:=(←IO.monoMsNow)-begin
  IO.println s!"run constructor smoke elapsed={elapsed} ms"

end RunConstructionSmoke
def main : IO Unit:=RunConstructionSmoke.main
