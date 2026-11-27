import REWB.MaskedTraversalDriverRegression

#print axioms REWB.MaskedTraversalFrontier.insert_valid
#print axioms REWB.MaskedTraversalFrontier.merge_valid
#print axioms REWB.MaskedTraversalFrontier.merge_mem
#print axioms REWB.MaskedTraversalFrontier.merge_measured
#print axioms REWB.MaskedTraversalDriver.build_valid
#print axioms REWB.MaskedTraversalDriver.build_mem
#print axioms REWB.MaskedTraversalDriver.node_children_at_parent
#print axioms REWB.MaskedTraversalDriver.build_measured
#print axioms REWB.MaskedTraversalDriver.build_imports
#print axioms REWB.MaskedTraversalDriver.build_work
#print axioms REWB.MaskedTraversalDriver.suffix_work
#print axioms REWB.MaskedTraversalDriver.build_band_locus
#print axioms REWB.MaskedTraversalDriver.build_cover
#print axioms REWB.MaskedTraversalDriver.suffix_band_complete
#print axioms REWB.MaskedTraversalDriver.suffix_cover
#print axioms REWB.MaskedTraversalDriver.Regression.actual_suffix_coverage

namespace REWB.MaskedTraversalDriver.Audit
open REWB.MaskedTraversalFrontier REWB.MaskedRunDiscovery

def check (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

/-- These slow list/substring references belong only to the bounded audit. -/
def steps : Plan h→List (Step h)
  | .empty s => [s]
  | .leaf _ _ s => [s]
  | .node l r _ s => steps l++steps r++[s]

def patches : Plan h→List (Patch h)
  | .empty _ => []
  | .leaf _ _ _ => []
  | .node l r m _ => patches l++patches r++m.revPatches.reverse

def literalClass (w : List (Fin 2)) (base length : Nat) : List Nat :=
  (List.range (w.length+1)).filter (fun p=>
    decide (p+length≤w.length) && ((w.drop p).take length==(w.drop base).take length))

def checkText (text : Array (Fin 2)) : IO (Nat×Nat×Nat×Nat) := do
  let n:=text.size
  let h:=(n+1).log2+1
  let suffix:=prepareSuffixes text 0
  let out:=run h suffix.trie.tree
  let allSteps:=steps out.plan
  let allPatches:=patches out.plan
  let allBands:=allSteps.flatMap (fun s=>s.lowered.edge.path.bands)
  check (out.frontier.state.occurrences.entries==List.range (n+1)) "final occurrence membership"
  check (allSteps.length==MaskedOrdered.Owner.slots suffix.trie.tree) "plan node count"
  check (out.imports==MaskedOrdered.Owner.light suffix.trie.tree && allPatches.length==out.imports)
    "actual light imports/patches"
  check (out.bands==allBands.length) "cached band count"
  check (out.popped+out.discarded+MaskedThresholdQueue.count out.frontier.state.queue==out.generated)
    "global pop/discard/pending conservation"
  check (decide (out.generated≤4*(out.imports+n+1))) "generation budget"
  check (decide (out.work≤h+1+(521*h+810)*((n+1)*(n+1).log2+n+1)+(196*h+354)*(n+1)))
    "closed geometric traversal budget"
  let mut equalDepth:=0
  for s in allSteps do
    check (s.lowered.frontier.state.occurrences.entries==s.before.state.occurrences.entries)
      "child occurrence snapshot changed before parent merge"
    if s.floor==s.high then
      equalDepth:=equalDepth+1
      check (s.lowered.edge.initial.isNone && s.lowered.edge.path.bands.isEmpty)
        "equal-depth partial refinement issued query/reset event"
    if s.floor<s.high then
      check ((MaskedThresholdQueue.entries s.lowered.frontier.state.queue).all
        (fun e=>decide (e.key<s.floor))) "child failed to consume a parent-depth event"
  for patch in allPatches do
    let expected:=(List.range (n+1)).filter (fun p=>p==patch.position ||
      patch.before.state.occurrences.entries.contains p)
    check (patch.update.frontier.state.occurrences.entries==expected) "actual import patch mismatch"
  let mut complete:=0
  for b in allBands do
    let some base:=b.snapshot.occurrences.entries.head? | throw (IO.userError "empty query class")
    for i in List.range (b.hi-b.lo+1) do
      let L:=b.lo+i
      check (b.snapshot.occurrences.entries==literalClass text.toList base L)
        s!"incomplete emitted class text={text.toList} L={L}"
      complete:=complete+1
  let mut covered:=0
  for p in List.range (n+1) do
    for i in List.range (n-p) do
      let L:=i+1
      let hits:=allBands.filter (fun b=>decide (b.lo≤L ∧ L≤b.hi) &&
        b.snapshot.occurrences.entries.contains p)
      check (hits.length==1) s!"start/length missing or repeated text={text.toList} p={p} L={L}"
      covered:=covered+1
  return (complete,covered,equalDepth,out.imports)

def deep (n period : Nat) : IO Unit := do
  let text : Array (Fin 2):=Array.ofFn (fun i : Fin n=>⟨(i.val%period)%2,by omega⟩)
  let h:=(n+1).log2+1
  let suffix:=prepareSuffixes text 0
  let out:=run h suffix.trie.tree
  check (out.frontier.state.occurrences.entries==List.range (n+1)) "deep membership"
  check (out.imports==MaskedOrdered.Owner.light suffix.trie.tree) "deep import schedule"
  check (decide (out.work≤h+1+(521*h+810)*((n+1)*(n+1).log2+n+1)+(196*h+354)*(n+1)))
    "deep measured work"
  IO.println s!"deep traversal n={n}, period={period}, imports={out.imports}, bands={out.bands}, generated={out.generated}, popped={out.popped}, discarded={out.discarded}, work={out.work}"

def runAudit : IO Unit := do
  let begin←IO.monoMsNow
  let sample:=run 3 Regression.sample
  check (Regression.rows sample.plan==[(3,4,[0]),(1,2,[0,2]),(2,3,[1]),(1,1,[1,3])])
    "explicit child/child/merge/edge chronology"
  check (sample.imports==5 && sample.bands==4 && sample.generated==12 && sample.popped==4 &&
    MaskedThresholdQueue.count sample.frontier.state.queue==8) "explicit refined-trie counters"
  let mut texts:=0
  let mut complete:=0
  let mut covered:=0
  let mut equalDepth:=0
  let mut imports:=0
  for n in List.range 9 do
    for bits in List.range (2^n) do
      let text : Array (Fin 2):=Array.ofFn (fun i : Fin n=>⟨(bits/2^i.val)%2,by omega⟩)
      let stats←checkText text
      texts:=texts+1
      complete:=complete+stats.1
      covered:=covered+stats.2.1
      equalDepth:=equalDepth+stats.2.2.1
      imports:=imports+stats.2.2.2
  deep 512 1
  deep 512 3
  let finish←IO.monoMsNow
  IO.println s!"actual suffix traversals={texts}, complete band/length classes={complete}, unique source/length covers={covered}, equal-depth skips={equalDepth}, light imports={imports}, mismatches=0, elapsed={finish-begin} ms"
  IO.println "Actual queue/leader/occurrence execution and full positive-length coverage checked. Bank preparation, local cached-bank repairs, and masked reporting costs are separate."

end REWB.MaskedTraversalDriver.Audit

def main : IO Unit := REWB.MaskedTraversalDriver.Audit.runAudit
