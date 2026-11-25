import REWB.MaskedTraversalEdgeRegression

#print axioms REWB.MaskedTraversalEdge.next_spec
#print axioms REWB.MaskedTraversalEdge.invariant_between
#print axioms REWB.MaskedTraversalEdge.threshold_between
#print axioms REWB.MaskedTraversalEdge.Chain.coverage
#print axioms REWB.MaskedTraversalEdge.Chain.unique
#print axioms REWB.MaskedTraversalEdge.Band.Valid.at
#print axioms REWB.MaskedTraversalEdge.run_valid
#print axioms REWB.MaskedTraversalEdge.run_occurrences
#print axioms REWB.MaskedTraversalEdge.run_measured
#print axioms REWB.MaskedTraversalEdge.run_work_queue
#print axioms REWB.MaskedTraversalEdge.Regression.parent_event_order
#print axioms REWB.MaskedTraversalEdge.Regression.long_singleton

namespace REWB.MaskedTraversalEdge.Audit
open REWB.MaskedClusterLeaders

def check (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

/-- Literal definition over the complete finite occurrence list. -/
def leaders (xs : List Nat) (length : Nat) : List Nat :=
  xs.filter (fun p=>xs.all (fun q=>decide (q≥p ∨ length<2*(p-q))))

def adjacent (xs : List Nat) (a b : Nat) : Bool :=
  xs.contains a && xs.contains b && decide (a<b) &&
    xs.all (fun p=>decide (p≤a ∨ b≤p))

def auditOne (xs : List Nat) (high floor order : Nat) : IO (Nat×Nat×Nat) := do
  let ps:=if order=0 then xs else xs.reverse
  let ops:=(ps.map Operation.insert)++(ps.take 1).map Operation.insert
  let input:=(execute 4 high ops).state
  let scheduled:=run 16 floor high input
  let out:=scheduled.path
  check (input.occurrences.entries==xs) "bad input occurrence construction"
  check (out.state.occurrences.entries==xs) "occurrence snapshot changed on edge"
  check (out.popped+MaskedThresholdQueue.count out.state.queue==MaskedThresholdQueue.count input.queue)
    "actual pop balance mismatch"
  check (decide (out.bands.length≤out.popped+1)) "more bands than popped records plus one"
  check (decide (out.work≤(98*4+162)*(out.popped+1))) "scheduler work exceeds theorem bound"
  if floor=high then
    check (out.bands.isEmpty && scheduled.initial.isNone && out.popped==0)
      "equal-depth refinement performed a query or drain"
    return (0,out.popped,out.work)
  check (out.state.leaders.entries==leaders xs floor) "wrong final leaders"
  check ((MaskedThresholdQueue.entries out.state.queue).all (fun e=>decide (e.key<floor)))
    "parent-depth event was left pending in queue"
  let mut queries:=0
  for length in List.range (high-floor) do
    let L:=floor+length+1
    let hits:=out.bands.filter (fun b=>decide (b.lo≤L ∧ L≤b.hi))
    check (hits.length==1) s!"nonunique or missing length coverage at {L}"
    for b in hits do
      check (b.snapshot.occurrences.entries==xs) "band changed occurrence class"
      check (b.snapshot.leaders.entries==leaders xs L) s!"unstable band leaders at {L}"
      check ((MaskedThresholdQueue.entries b.snapshot.queue).all (fun e=>decide (e.key<b.lo)))
        "query band crossed a pending threshold"
      for e in b.crossing.live do
        check (adjacent xs e.value.edge.1 e.value.edge.2) "stale edge was returned live"
        check (decide (b.lo-1≤e.key)) "crossing returned an undued event"
    queries:=queries+1
  let mut expectedHigh:=high
  for b in out.bands do
    check (b.hi==expectedHigh && decide (floor<b.lo ∧ b.lo≤b.hi))
      "band order or endpoints are wrong"
    expectedHigh:=b.lo-1
  check (expectedHigh==floor) "final band did not stop at parent"
  return (queries,out.popped,out.work)

def runAudit : IO Unit := do
  let begin←IO.monoMsNow
  let mut schedules:=0
  let mut lengths:=0
  let mut popped:=0
  let mut work:=0
  for bits in List.range 256 do
    let xs:=(List.range 8).filter (fun p=>decide ((bits/2^p)%2=1))
    for high in List.range 19 do
      for floor in [0,high/2,high] do
        let out←auditOne xs high floor (bits%2)
        schedules:=schedules+1
        lengths:=lengths+out.1
        popped:=popped+out.2.1
        work:=work+out.2.2
  let sparse:=run 2 0 1000000000 Regression.singleton
  check (sparse.path.bands.length==1 && sparse.path.popped==0 && sparse.path.work==42)
    "large numeric edge regressed into a length scan"
  let finish←IO.monoMsNow
  IO.println s!"edge schedules={schedules}, literal length checks={lengths}, actual pops={popped}, measured work={work}, mismatches=0, elapsed={finish-begin} ms"
  IO.println "Checked empty/singleton/dense occurrence sets, duplicate insertions, stale and born-due events, parent-depth events, equal-depth refinements, and a billion-long one-band edge. Bank/query callback work remains separate."

end REWB.MaskedTraversalEdge.Audit

def main : IO Unit := REWB.MaskedTraversalEdge.Audit.runAudit
