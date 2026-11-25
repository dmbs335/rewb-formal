import REWB.MaskedTraversalRetainedRegression
import REWB.MaskedTraversalDriverRegression

/-! Reference execution of actual Driver chronology with actual populated
anchor slots. Unlike the earlier endpoint audit, every represented length
inside each emitted band is tested. The AP-grid/word scans are reference
checks only; none occurs in the bank implementation or measured scheduler.
-/
namespace REWB.MaskedTraversalRetained.Audit
open REWB.MaskedTraversalDriver REWB.MaskedTraversalFrontier
variable {h : Nat}

structure Stats where
  bands : Nat := 0
  lengths : Nat := 0
  clusters : Nat := 0
  retained : Nat := 0
  words : Nat := 0

structure State where
  anchors : Array (Option Nat)
  stats : Stats

def check (w : Word (Fin 2)) (partition : MaskedClusterLeaders.State h) (capacity L : Nat)
    (dirty : MaskedTraversalDirty.Marked h) (st : State) : IO State := do
  let mut st:=st
  for first in partition.leaders.entries do
    unless dirty.keys.positions.contains first do
      let some d:=(MaskedClusterDescriptor.describeLeader partition capacity first).1 |
        throw (IO.userError "actual leader has no descriptor")
      let some H:=(st.anchors[first]?).join |
        throw (IO.userError s!"unmarked actual leader lacks populated anchor: first={first}, L={L}")
      let next:=d.nextAt w.length
      unless L≤H && d.last+H≤w.length &&
          d.previous.all (fun p=>p+H≤next) && d.following.all (fun p=>d.last+H≤p) &&
          decide (next<d.last+H)=decide (next<d.last+L) do
        throw (IO.userError s!"retained certificate failed: first={first}, L={L}, H={H}, d={repr d}")
      let mut words:=0
      for p in copies d do
        unless p+H≤w.length && Spec.slice w p (p+H)=Spec.slice w first (first+H) do
          throw (IO.userError s!"retained grid word failed: first={first}, p={p}, L={L}, H={H}")
        words:=words+1
      st:={st with stats:={st.stats with
        clusters:=st.stats.clusters+1,retained:=st.stats.retained+(if L<H then 1 else 0),words:=st.stats.words+words}}
  return st

def process (w : Word (Fin 2)) (capacity : Nat) (step : Step h)
    (pending : MaskedTraversalDirty.Marked h) (initial : State) : IO (State×MaskedTraversalDirty.Marked h) := do
  let mut st:=initial
  let mut dirty:=pending
  let mut current:=step.before.state
  if let some crossing:=step.lowered.edge.initial then
    dirty:=MaskedTraversalDirty.crossing current crossing capacity dirty
    current:=crossing.state
  for band in step.lowered.edge.path.bands do
    unless current.occurrences.entries=band.snapshot.occurrences.entries && current.leaders.entries=band.snapshot.leaders.entries do
      throw (IO.userError "emitted band changed the actual occurrence snapshot")
    st ←check w band.snapshot capacity band.hi dirty st
    st:={st with
      anchors:=(MaskedTraversalRepair.anchorsLoop band.hi dirty.keys.positions st.anchors 0).1
      stats:={st.stats with bands:=st.stats.bands+1}}
    for offset in List.range (band.hi-band.lo+1) do
      st ←check w band.snapshot capacity (band.lo+offset) (MaskedTraversalDirty.empty h) st
      st:={st with stats:={st.stats with lengths:=st.stats.lengths+1}}
    dirty:=MaskedTraversalDirty.crossing band.snapshot band.crossing capacity (MaskedTraversalDirty.empty h)
    current:=band.crossing.state
    st ←check w current capacity (band.lo-1) dirty st
  st ←check w step.lowered.frontier.state capacity step.floor dirty st
  return (st,dirty)

def visit (w : Word (Fin 2)) (capacity : Nat) : MaskedTraversalDriver.Plan h→State→IO (State×MaskedTraversalDirty.Marked h)
  | .empty step,st => process w capacity step (MaskedTraversalDirty.empty h) st
  | .leaf p inserted step,st =>
    process w capacity step
      (MaskedTraversalDirty.markChange (MaskedClusterLeaders.empty h).leaders inserted.frontier.state.leaders
        capacity p (MaskedTraversalDirty.empty h)) st
  | .node left right merged step,st => do
    let (st,leftPending) ←visit w capacity left st
    let (st,rightPending) ←visit w capacity right st
    let pending:=if merged.keptLeft then leftPending else rightPending
    let dirty:=MaskedTraversalDirty.patches capacity merged.revPatches pending
    let st ←check w step.before.state capacity step.high dirty st
    process w capacity step dirty st

def one (text : Array (Fin 2)) : IO Stats := do
  let h:=(text.size+1).log2+1
  let capacity:=2^h
  let trie:=MaskedRunDiscovery.prepareSuffixes text 0
  let driver:=MaskedTraversalDriver.run h trie.trie.tree
  let initial : State:=⟨Array.replicate (text.size+1) none,{}⟩
  let (done,_) ←visit text.toList capacity driver.plan initial
  unless done.stats.bands=driver.bands do throw (IO.userError "actual band count differs")
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
      total:=⟨total.bands+st.bands,total.lengths+st.lengths,total.clusters+st.clusters,
        total.retained+st.retained,total.words+st.words⟩
  let elapsed ←IO.monoMsNow
  IO.println s!"all-length retained anchors: texts={texts}, bands={total.bands}, represented lengths={total.lengths}, actual populated certificates={total.clusters}, strict H>L certificates={total.retained}, AP-copy checks={total.words}, mismatches=0, elapsed={elapsed-begin} ms"
  for q in [1,3] do
    let text:=Array.ofFn (fun i : Fin 128=>if q=1 || i.val%3<2 then (0:Fin 2) else 1)
    let st ←one text
    IO.println s!"deep n=128/q={q}: bands={st.bands}, represented lengths={st.lengths}, strict H>L={st.retained}, AP-copy checks={st.words}, mismatches=0"
  IO.println "Actual per-transition and per-band retained certificates are kernel proved. Global slot/aggregate/source-erasure coherence remains a separate integration obligation."

end REWB.MaskedTraversalRetained.Audit

def main : IO Unit := REWB.MaskedTraversalRetained.Audit.run

#print axioms REWB.MaskedTraversalRetained.copies_mem
#print axioms REWB.MaskedTraversalRetained.anchorsLoop_slot
#print axioms REWB.MaskedTraversalRetained.reset_own
#print axioms REWB.MaskedTraversalRetained.reset_all
#print axioms REWB.MaskedTraversalRetained.next_marks_first
#print axioms REWB.MaskedTraversalRetained.overlap_record
#print axioms REWB.MaskedTraversalRetained.mode_away
#print axioms REWB.MaskedTraversalRetained.mode_between
#print axioms REWB.MaskedTraversalRetained.band_own
#print axioms REWB.MaskedTraversalRetained.add_away
#print axioms REWB.MaskedTraversalRetained.merge_away
#print axioms REWB.MaskedTraversalRetained.crossing_away
#print axioms REWB.MaskedTraversalRetained.band_all
#print axioms REWB.MaskedTraversalRetained.crossing_reset_all
