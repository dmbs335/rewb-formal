import REWB.MaskedTraversalNeighborRegression
import REWB.MaskedTraversalDriverRegression

/-! Execute the real Driver plan with one global anchor array. Imports
and threshold records feed the real sparse dirty collectors. Reset only
at complete emitted bands; retain final-floor/equal-depth pending keys.
The literal H-copy/geometry scans here are references, never part of the
indexed traversal. Their checks include obligations beyond the proved
descriptor/bound transport lemmas (notably retained overlap mode).
-/
namespace REWB.MaskedTraversalNeighbor.Audit
open REWB.MaskedTraversalDriver REWB.MaskedTraversalFrontier
variable {h : Nat}

structure Stats where
  leaves : Nat := 0
  imports : Nat := 0
  pops : Nat := 0
  bands : Nat := 0
  requests : Nat := 0
  resets : Nat := 0
  checked : Nat := 0
  words : Nat := 0
  equalDepth : Nat := 0

structure State where
  anchors : Array (Option Nat)
  stats : Stats

def checkAway (w : Word (Fin 2)) (partition : MaskedClusterLeaders.State h) (capacity L : Nat)
    (dirty : MaskedTraversalDirty.Marked h) (st : State) : IO State := do
  let mut checked:=0
  let mut words:=0
  for first in partition.leaders.entries do
    unless dirty.keys.positions.contains first do
      let some d:=(MaskedClusterDescriptor.describeLeader partition capacity first).1 |
        throw (IO.userError "actual leader has no descriptor")
      let H:=MaskedTraversalBankReady.readAnchor st.anchors first L
      let next:=d.nextAt w.length
      unless L≤H && d.last+H≤w.length &&
          (d.previous.all (fun p=>p+H≤next)) && (d.following.all (fun p=>d.last+H≤p)) &&
          decide (next<d.last+H)=decide (next<d.last+L) do
        throw (IO.userError s!"retained local geometry failed: L={L}, H={H}, d={repr d}, dirty={dirty.keys.positions}")
      for p in partition.occurrences.entries do
        if first≤p && p≤d.last then
          unless p+H≤w.length && Spec.slice w p (p+H)=Spec.slice w first (first+H) do
            throw (IO.userError s!"retained H-copy failed: first={first}, p={p}, L={L}, H={H}")
          words:=words+1
      checked:=checked+1
  return {st with stats:={st.stats with checked:=st.stats.checked+checked,words:=st.stats.words+words}}

def process (w : Word (Fin 2)) (capacity : Nat) (step : Step h)
    (pending : MaskedTraversalDirty.Marked h) (initial : State) : IO (State×MaskedTraversalDirty.Marked h) := do
  let mut st:=initial
  let mut dirty:=pending
  let mut current:=step.before.state
  if step.floor=step.high then st:={st with stats:={st.stats with equalDepth:=st.stats.equalDepth+1}}
  if let some crossing:=step.lowered.edge.initial then
    let beforeRequests:=dirty.requests
    dirty:=MaskedTraversalDirty.crossing current crossing capacity dirty
    st:={st with stats:={st.stats with
      requests:=st.stats.requests+(dirty.requests-beforeRequests),pops:=st.stats.pops+crossing.popped}}
    current:=crossing.state
  for band in step.lowered.edge.path.bands do
    unless current.occurrences.entries=band.snapshot.occurrences.entries && current.leaders.entries=band.snapshot.leaders.entries do
      throw (IO.userError "band did not retain the executed occurrence snapshot")
    st ←checkAway w band.snapshot capacity band.hi dirty st
    let fresh:=MaskedTraversalRepair.anchorsLoop band.hi dirty.keys.positions st.anchors 0
    st:={st with anchors:=fresh.1,stats:={st.stats with
      bands:=st.stats.bands+1,resets:=st.stats.resets+dirty.keys.positions.length}}
    st ←checkAway w band.snapshot capacity band.hi (MaskedTraversalDirty.empty h) st
    dirty:=MaskedTraversalDirty.crossing band.snapshot band.crossing capacity (MaskedTraversalDirty.empty h)
    st:={st with stats:={st.stats with requests:=st.stats.requests+dirty.requests,pops:=st.stats.pops+band.crossing.popped}}
    current:=band.crossing.state
    st ←checkAway w current capacity (band.lo-1) dirty st
  st ←checkAway w step.lowered.frontier.state capacity step.floor dirty st
  return (st,dirty)

def visit (w : Word (Fin 2)) (capacity : Nat) : MaskedTraversalDriver.Plan h→State→IO (State×MaskedTraversalDirty.Marked h)
  | .empty step,st => process w capacity step (MaskedTraversalDirty.empty h) st
  | .leaf p inserted step,st => do
    let dirty:=MaskedTraversalDirty.markChange (MaskedClusterLeaders.empty h).leaders inserted.frontier.state.leaders
      capacity p (MaskedTraversalDirty.empty h)
    let st:={st with stats:={st.stats with leaves:=st.stats.leaves+1,requests:=st.stats.requests+dirty.requests}}
    process w capacity step dirty st
  | .node left right merged step,st => do
    let (st,leftPending) ←visit w capacity left st
    let (st,rightPending) ←visit w capacity right st
    let pending:=if merged.keptLeft then leftPending else rightPending
    let dirty:=MaskedTraversalDirty.patches capacity merged.revPatches pending
    let st:={st with stats:={st.stats with
      imports:=st.stats.imports+merged.imports,requests:=st.stats.requests+(dirty.requests-pending.requests)}}
    let st ←checkAway w step.before.state capacity step.high dirty st
    process w capacity step dirty st

def one (text : Array (Fin 2)) : IO Stats := do
  let h:=(text.size+1).log2+1
  let capacity:=2^h
  let trie:=REWB.MaskedRunDiscovery.prepareSuffixes text 0
  let driver:=REWB.MaskedTraversalDriver.run h trie.trie.tree
  let initial : State:=⟨Array.replicate (text.size+1) none,{}⟩
  let (done,_) ←visit text.toList capacity driver.plan initial
  let stats:=done.stats
  unless stats.leaves=text.size+1 && stats.imports=driver.imports && stats.pops=driver.popped && stats.bands=driver.bands do
    throw (IO.userError "chronology counters disagree with actual Driver")
  unless stats.requests≤9*(stats.leaves+stats.imports+stats.pops) && stats.resets≤stats.requests do
    throw (IO.userError "deduplicated complete-band resets exceeded actual operation budget")
  return stats

def run : IO Unit := do
  let begin ←IO.monoMsNow
  let mut texts:=0
  let mut bands:=0
  let mut checked:=0
  let mut words:=0
  let mut imports:=0
  let mut pops:=0
  let mut requests:=0
  let mut resets:=0
  let mut equalDepth:=0
  for n in List.range 8 do
    for mask in List.range (2^n) do
      let text:=Array.ofFn (fun i : Fin n=>if mask.testBit i.val then (1:Fin 2) else 0)
      let stats ←one text
      texts:=texts+1
      bands:=bands+stats.bands
      checked:=checked+stats.checked
      words:=words+stats.words
      imports:=imports+stats.imports
      pops:=pops+stats.pops
      requests:=requests+stats.requests
      resets:=resets+stats.resets
      equalDepth:=equalDepth+stats.equalDepth
  let finish ←IO.monoMsNow
  IO.println s!"actual pending-anchor Driver: texts={texts}, complete bands={bands}, imports={imports}, queue pops={pops}, requested dirty keys={requests}, complete-band reset keys={resets}, safe unmarked clusters={checked}, retained H-copy checks={words}, equal-depth skips={equalDepth}, mismatches=0, elapsed={finish-begin} ms"
  for q in [1,3] do
    let text:=Array.ofFn (fun i : Fin 128=>if q=1 || i.val%3<2 then (0:Fin 2) else 1)
    let stats ←one text
    IO.println s!"deep n=128/q={q}: bands={stats.bands}, imports={stats.imports}, pops={stats.pops}, reset keys={stats.resets}, H-copy checks={stats.words}, equal-depth skips={stats.equalDepth}, mismatches=0"
  IO.println "Insertion, validated threshold and heavy-merge descriptor locality plus pending anchor-bound transport are kernel proved. This execution also tests retained H-copy/overlap invariants; their full global bank/aggregate coherence proof remains separate."

end REWB.MaskedTraversalNeighbor.Audit

def main : IO Unit := REWB.MaskedTraversalNeighbor.Audit.run

#print axioms REWB.MaskedTraversalNeighbor.around_left
#print axioms REWB.MaskedTraversalNeighbor.around_right
#print axioms REWB.MaskedTraversalNeighbor.describe_insert_away
#print axioms REWB.MaskedTraversalNeighbor.add_describe_away
#print axioms REWB.MaskedTraversalNeighbor.describe_additions_away
#print axioms REWB.MaskedTraversalNeighbor.shorten_describe_away
#print axioms REWB.MaskedTraversalNeighbor.crossing_describe_unmarked
#print axioms REWB.MaskedTraversalNeighbor.importLoop_describe_unmarked
#print axioms REWB.MaskedTraversalNeighbor.merge_describe_unmarked
#print axioms REWB.MaskedTraversalNeighbor.add_anchorBoundsAway
#print axioms REWB.MaskedTraversalNeighbor.crossing_anchorBoundsAway
#print axioms REWB.MaskedTraversalNeighbor.merge_anchorBoundsAway
