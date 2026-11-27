import REWB.MaskedTraversalIncomingRegression
import REWB.MaskedTraversalDriverRegression

/-! Execute actual postorder imports, threshold crossings, complete-band
resets and all represented lengths. Full scans below are references used
to compare predecessor/cursor data, never an implementation repair pass.
-/
namespace REWB.MaskedTraversalIncoming.Audit
open REWB.MaskedTraversalDriver REWB.MaskedTraversalFrontier REWB.MaskedTraversalBankReady
variable {h : Nat}

structure Stats where
  transitions : Nat := 0
  contexts : Nat := 0
  checked : Nat := 0
  enabled : Nat := 0
  resetOnly : Nat := 0

structure State where
  anchors : Array (Option Nat)
  stats : Stats

def check (before after : MaskedClusterLeaders.State h) (capacity old fresh : Nat)
    (oldAnchors newAnchors : Array (Option Nat)) (dirty : MaskedTraversalDirty.Marked h)
    (initial : Stats) : IO Stats := do
  let contexts:=MaskedTraversalContext.successors after.leaders capacity dirty.keys.positions (MaskedTraversalDirty.empty h)
  let mut stats:={initial with transitions:=initial.transitions+1,contexts:=initial.contexts+contexts.keys.positions.length}
  for first in after.leaders.entries do
    unless contexts.keys.positions.contains first do
      let oldPred:=(MaskedOrdered.Tree.pred before.leaders capacity first).1
      let newPred:=(MaskedOrdered.Tree.pred after.leaders capacity first).1
      unless oldPred=newPred do throw (IO.userError s!"unmarked predecessor changed at {first}")
      let a:=incoming before capacity first old oldAnchors
      let b:=incoming after capacity first fresh newAnchors
      unless a.cursor=b.cursor && a.enabled=b.enabled do
        throw (IO.userError s!"unmarked incoming changed: first={first}, old={old}, fresh={fresh}, old-data={repr a}, new-data={repr b}, dirty={dirty.keys.positions}, contexts={contexts.keys.positions}")
      stats:={stats with checked:=stats.checked+1,enabled:=stats.enabled+(if a.enabled then 1 else 0)}
    if contexts.keys.positions.contains first && !(dirty.keys.positions.contains first) then
      stats:={stats with resetOnly:=stats.resetOnly+1}
  return stats

def process (capacity : Nat) (step : Step h) (pending : MaskedTraversalDirty.Marked h)
    (initial : State) : IO (State×MaskedTraversalDirty.Marked h) := do
  let mut st:=initial
  let mut dirty:=pending
  let mut current:=step.before.state
  if let some crossing:=step.lowered.edge.initial then
    dirty:=MaskedTraversalDirty.crossing current crossing capacity dirty
    let stats ←check current crossing.state capacity step.high step.high st.anchors st.anchors dirty st.stats
    st:={st with stats:=stats}
    current:=crossing.state
  for band in step.lowered.edge.path.bands do
    let nextAnchors:=(MaskedTraversalRepair.anchorsLoop band.hi dirty.keys.positions st.anchors 0).1
    let stats ←check band.snapshot band.snapshot capacity band.hi band.hi st.anchors nextAnchors dirty st.stats
    st:={anchors:=nextAnchors,stats:=stats}
    for offset in List.range (band.hi-band.lo+1) do
      let stats ←check band.snapshot band.snapshot capacity band.hi (band.lo+offset)
        st.anchors st.anchors (MaskedTraversalDirty.empty h) st.stats
      st:={st with stats:=stats}
    dirty:=MaskedTraversalDirty.crossing band.snapshot band.crossing capacity (MaskedTraversalDirty.empty h)
    let stats ←check band.snapshot band.crossing.state capacity band.hi (band.lo-1) st.anchors st.anchors dirty st.stats
    st:={st with stats:=stats}
    current:=band.crossing.state
  return (st,dirty)

def visit (capacity : Nat) : MaskedTraversalDriver.Plan h→State→IO (State×MaskedTraversalDirty.Marked h)
  | .empty step,st => process capacity step (MaskedTraversalDirty.empty h) st
  | .leaf p inserted step,st =>
    process capacity step
      (MaskedTraversalDirty.markChange (MaskedClusterLeaders.empty h).leaders inserted.frontier.state.leaders
        capacity p (MaskedTraversalDirty.empty h)) st
  | .node left right merged step,st => do
    let (st,leftPending) ←visit capacity left st
    let (st,rightPending) ←visit capacity right st
    let pending:=if merged.keptLeft then leftPending else rightPending
    let dirty:=MaskedTraversalDirty.patches capacity merged.revPatches pending
    let mut stats:=st.stats
    for patch in merged.revPatches do
      let localDirty:=MaskedTraversalDirty.markChange patch.before.state.leaders patch.update.frontier.state.leaders
        capacity patch.position (MaskedTraversalDirty.empty h)
      stats ←check patch.before.state patch.update.frontier.state capacity step.high step.high
        st.anchors st.anchors localDirty stats
    let kept:=if merged.keptLeft then (MaskedTraversalDriver.Regression.top left).lowered.frontier.state
      else (MaskedTraversalDriver.Regression.top right).lowered.frontier.state
    stats ←check kept step.before.state capacity step.high step.high st.anchors st.anchors dirty stats
    process capacity step dirty {st with stats:=stats}

def one (text : Array (Fin 2)) : IO Stats := do
  let h:=(text.size+1).log2+1
  let capacity:=2^h
  let trie:=MaskedRunDiscovery.prepareSuffixes text 0
  let driver:=MaskedTraversalDriver.run h trie.trie.tree
  let initial : State:=⟨Array.replicate (text.size+1) none,{}⟩
  let (done,_) ←visit capacity driver.plan initial
  return done.stats

def run : IO Unit := do
  let begin ←IO.monoMsNow
  let mut texts:=0
  let mut total : Stats:={}
  for n in List.range 8 do
    for mask in List.range (2^n) do
      let text:=Array.ofFn (fun i : Fin n=>if mask.testBit i.val then (1:Fin 2) else 0)
      let st ←one text
      texts:=texts+1
      total:=⟨total.transitions+st.transitions,total.contexts+st.contexts,total.checked+st.checked,
        total.enabled+st.enabled,total.resetOnly+st.resetOnly⟩
  let finish ←IO.monoMsNow
  IO.println s!"actual incoming locality: texts={texts}, transitions={total.transitions}, context keys={total.contexts}, unmarked predecessor/cursor comparisons={total.checked}, active incoming comparisons={total.enabled}, successor-only candidates={total.resetOnly}, mismatches=0, elapsed={finish-begin} ms"
  for q in [1,3] do
    let text:=Array.ofFn (fun i : Fin 128=>if q=1 || i.val%3<2 then (0:Fin 2) else 1)
    let st ←one text
    IO.println s!"deep n=128/q={q}: transitions={st.transitions}, comparisons={st.checked}, active incoming={st.enabled}, successor-only candidates={st.resetOnly}, mismatches=0"
  IO.println "Predecessor and incoming transport is kernel proved for actual add, merge, crossing, reset and band reads. Global store/aggregate integration remains separate."

end REWB.MaskedTraversalIncoming.Audit

def main : IO Unit := REWB.MaskedTraversalIncoming.Audit.run

#print axioms REWB.MaskedTraversalIncoming.previous_unmarked
#print axioms REWB.MaskedTraversalIncoming.predecessor_preserved
#print axioms REWB.MaskedTraversalIncoming.incoming_transport
#print axioms REWB.MaskedTraversalIncoming.retained_transport
#print axioms REWB.MaskedTraversalIncoming.add_incoming_away
#print axioms REWB.MaskedTraversalIncoming.merge_incoming_away
#print axioms REWB.MaskedTraversalIncoming.crossing_incoming_away
#print axioms REWB.MaskedTraversalIncoming.reset_preserves_transport
#print axioms REWB.MaskedTraversalIncoming.populated_length
#print axioms REWB.MaskedTraversalIncoming.band_incoming
#print axioms REWB.MaskedTraversalIncoming.config_preserved
#print axioms REWB.MaskedTraversalIncoming.retained_config_preserved
