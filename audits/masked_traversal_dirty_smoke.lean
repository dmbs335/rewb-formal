import REWB.MaskedTraversalRepairRegression

/-! Bounded exhaustive metadata audit plus an actual complete-class reset
execution. The reference list scans occur only here. The locality checks
are regression evidence, not a substitute for the still-open general
descriptor/cursor locality theorem. -/
namespace REWB.MaskedTraversalDirty.Audit
open REWB.MaskedCluster REWB.MaskedFiniteAction

def neighbors (xs : List Nat) (p : Nat) : List Nat :=
  let left:=(xs.filter (·≤p)).getLast?
  let right:=xs.find? (fun x=>p<x)
  let earlier:=left.bind (fun q=>(xs.filter (·<q)).getLast?)
  let later:=right.bind (fun q=>xs.find? (fun x=>q<x))
  earlier.toList++left.toList++right.toList++later.toList

def referenceKeys (before after : List Nat) (p : Nat) : List Nat :=
  p::(neighbors before p++neighbors after p)

def check (before after : MaskedClusterLeaders.State 3) (old fresh : Nat)
    (keys : Marked 3) (expected : List Nat) : IO (Nat×Nat) := do
  let positions:=keys.keys.positions
  unless positions.eraseDups.length=positions.length && positions.length=keys.keys.tree.count do
    throw (IO.userError "sparse dirty set lost deduplication or cached count")
  let anchors:=Array.ofFn (fun i : Fin 8=>some (20+i.val%3))
  let mut unchanged:=0
  let mut changed:=0
  for x in List.range 8 do
    unless (MaskedOrdered.Tree.contains keys.keys.tree 8 x).1=positions.contains x &&
        positions.contains x=expected.contains x do
      throw (IO.userError s!"dirty reference mismatch at {x}")
    let a:=(MaskedClusterDescriptor.describeLeader before 8 x).1
    let b:=(MaskedClusterDescriptor.describeLeader after 8 x).1
    if a != b then changed:=changed+1
    unless positions.contains x do
      unless a=b do
        throw (IO.userError s!"unmarked descriptor changed: key={x}, old={old}, fresh={fresh}, before={before.occurrences.entries}, after={after.occurrences.entries}, dirty={positions}")
      if after.leaders.entries.contains x then
        let ai:=MaskedTraversalBankReady.incoming before 8 x old anchors
        let bi:=MaskedTraversalBankReady.incoming after 8 x fresh anchors
        unless ai.cursor=bi.cursor && ai.enabled=bi.enabled do
          throw (IO.userError s!"unmarked incoming context changed: key={x}, old={old}, fresh={fresh}")
      unchanged:=unchanged+1
  return (unchanged,changed)

def metadata : IO Unit := do
  let begin ←IO.monoMsNow
  let mut inserts:=0
  let mut crossings:=0
  let mut popped:=0
  let mut liveRecords:=0
  let mut requests:=0
  let mut dedup:=0
  let mut unchanged:=0
  let mut changed:=0
  for mask in List.range 256 do
    let positions:=(List.range 8).filter (fun p=>mask.testBit p)
    for L in List.range 9 do
      let imported:=MaskedTraversalFrontier.importLoop 8 L positions
        (MaskedTraversalFrontier.initial (MaskedTraversalFrontier.empty 3))
      let before:=imported.frontier
      for p in List.range 8 do
        let out:=MaskedTraversalFrontier.importLoop 8 L [p] (MaskedTraversalFrontier.initial before)
        let keys:=patches 8 out.revPatches (empty 3)
        let after:=out.frontier
        unless keys.requests≤9 && keys.keys.positions.length≤9 && keys.work≤1+(308*3+274)+1 do
          throw (IO.userError "actual insertion dirty budget exceeded")
        let result ←check before.state after.state L L keys
          (referenceKeys before.state.leaders.entries after.state.leaders.entries p)
        unchanged:=unchanged+result.1
        changed:=changed+result.2
        inserts:=inserts+1
        requests:=requests+keys.requests
        dedup:=dedup+keys.keys.positions.length
      for fresh in List.range (L+1) do
        let after:=MaskedClusterLeaders.shorten 8 fresh before.state
        let keys:=crossing before.state after 8 (empty 3)
        unless keys.requests≤9*after.popped && keys.keys.positions.length≤9*after.popped &&
            keys.work≤1+(308*3+274)*after.popped+1 do
          throw (IO.userError "actual crossing dirty budget exceeded")
        let expected:=after.live.flatMap (fun e=>referenceKeys before.state.leaders.entries after.state.leaders.entries e.value.edge.2)
        let result ←check before.state after.state L fresh keys expected
        unchanged:=unchanged+result.1
        changed:=changed+result.2
        crossings:=crossings+1
        popped:=popped+after.popped
        liveRecords:=liveRecords+after.live.length
        requests:=requests+keys.requests
        dedup:=dedup+keys.keys.positions.length
  let finish ←IO.monoMsNow
  IO.println s!"actual dirty provenance: insertion patches={inserts}, actual threshold crossings={crossings}, queue pops={popped}, validated live records={liveRecords}, requested keys={requests}, dedup keys={dedup}, unchanged outside-key descriptors={unchanged}, changed descriptors captured={changed}, mismatches=0, elapsed={finish-begin} ms"

def C : DFA (Fin 3) := ⟨2,0,fun q x=>if x.val=1 then 1 else q,fun q=>q==1⟩
def E : DFA (Fin 3) := ⟨2,0,fun _ x=>if x.val=1 then 1 else 0,fun q=>q==1⟩

def physical (w : Word (Fin 3)) (cfg : Mutable.Store.Config) (im om : Bool)
    (source target : Array Bool) (gate : Bool)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount) : Bool :=
  if im && !cfg.incomingEnabled then false else
    let d:=cfg.descriptor
    let I:=if im then cfg.incoming else d.first
    let next:=d.nextAt w.length
    let O:=if om then d.last+cfg.anchor else next
    let jump:=(List.range (d.repetitions+1)).any fun k=>
      let p:=d.first+k*d.period
      decide (I≤p) && (if om then decide (next<p+cfg.length) else decide (p+cfg.length≤next)) &&
        decide (MaskedClusterStage.direct C E w I p cfg.length O
          ((gate && cfg.window.enabled && decide (cfg.window.lo≤p ∧ p<cfg.window.hi)) && source[p]?.getD false)
          (target[p]?.getD false) input=some output)
    if om then jump else decide (MaskedClusterStage.read C E (Spec.slice w I next) input=output) || jump

def resetFixture (text : Array (Fin 3)) (L : Nat) : IO Nat := do
  let n:=text.size
  let h:=(n+1).log2+1
  let cap:=2^h
  let w:=text.toList
  let occurrences:=(List.range (n+1)).filter fun p=>
    decide (p+L≤n ∧ Spec.slice w p (p+L)=Spec.slice w 0 L)
  let imported:=MaskedTraversalFrontier.importLoop cap L occurrences.reverse
    (MaskedTraversalFrontier.initial (MaskedTraversalFrontier.empty h))
  let partition:=imported.frontier.state
  let keys:=patches cap imported.revPatches (empty h)
  let source:=Array.ofFn (fun i : Fin (n+1)=>decide (i.val%4!=1))
  let target:=Array.ofFn (fun i : Fin (n+1)=>decide (i.val%3=0 ∨ i.val%5=2))
  let prepared:=REWB.MaskedCluster.prepare C.stateCount E.stateCount
  let book:=ReplayMaps.prepare C.stateCount E.stateCount
  let sources:=MaskedMutableProgression.Batch.run text 0 source prepared.K [0,7,n+5]
  let live:=((source.setIfInBounds 0 false).setIfInBounds 7 false).setIfInBounds (n+5) false
  let catalog:=MaskedRunCatalog.ofBatch target sources
  let classes:=MaskedSuffixClass.prepare text 0
  let ci:=BoundaryApplication.Range.build C w
  let ei:=BoundaryApplication.Range.build E w
  -- Deliberately unsafe stale marked anchors. The first pass repairs all
  -- current leaders before any bank computes its predecessor cursor.
  let anchors:=Array.replicate (n+1) (some 100)
  let initial:=Mutable.Store.empty C E sources
  let out:=MaskedTraversalRepair.reset C E book prepared ci ei partition cap L anchors ⟨true,0,n+1⟩
    catalog classes target keys initial
  unless out.work≤(85*h+52*MaskedRunCatalog.width n+149+Mutable.Store.bankLimit C E prepared.K n)*
      keys.keys.positions.length+6 do throw (IO.userError "two-pass actual reset budget exceeded")
  unless out.store.rebuilds=keys.keys.positions.length && out.store.writes=keys.keys.positions.length do
    throw (IO.userError "two-pass bank request count is not deduplicated-key count")
  let mut cells:=0
  let replay:=ReplayMaps.encode (ReplayMaps.one C.stateCount E.stateCount)
  let states:=List.ofFn (fun i : Fin (MaskedClusterStage.dfa C E).stateCount=>i)
  for first in partition.leaders.entries do
    let some entry:=out.store.slots[first]?.join | throw (IO.userError "two-pass reset missed an actual leader")
    unless entry.config.anchor=L do throw (IO.userError "selected anchor was not reset")
    let previous:=(occurrences.filter (·<first)).getLast?
    let expected:=previous.map (·+L)
    unless entry.config.incoming=expected.getD first && entry.config.incomingEnabled=(expected.any (fun p=>first<p)) do
      throw (IO.userError "bank observed an unreset predecessor anchor")
    for gate in [false,true] do
      for im in [false,true] do
        for om in [false,true] do
          for i in states do
            for j in states do
              let actual:=entry.bank.view (code _ gate replay) (code _ im i) (code _ om j)
              let reference:=physical w entry.config im om live target gate
                (MaskedClusterStage.decode C E i) (MaskedClusterStage.decode C E j)
              unless actual=reference do throw (IO.userError "two-pass physical cursor mismatch")
              cells:=cells+1
  IO.println s!"two-pass reset: n={n}, complete occurrences={occurrences.length}, leaders={partition.leaders.count}, dedup reset keys={keys.keys.positions.length}, writes={out.store.writes}, physical cells={cells}, tracked work={out.work}, mismatches=0"
  return cells

def run : IO Unit := do
  metadata
  let _ ←resetFixture #[0,1,0,1,0,1,0,1,2,2,0,1,0,1,0,1,2,2,0,1,0,1] 4
  let _ ←resetFixture #[0,0,1,0,0,1,0,0,1,0] 4
  IO.println "Dirty-set locality was tested exhaustively on bounded sets; its general theorem and global lazy aggregate/frontier coherence remain open. Reset correctness/cost and actual patch/live-record provenance are kernel checked."

end REWB.MaskedTraversalDirty.Audit

def main : IO Unit := REWB.MaskedTraversalDirty.Audit.run

#print axioms REWB.MaskedTraversalDirty.markChange_spec
#print axioms REWB.MaskedTraversalDirty.importLoop_patches
#print axioms REWB.MaskedTraversalDirty.merge_patches
#print axioms REWB.MaskedTraversalDirty.patches_spec
#print axioms REWB.MaskedTraversalDirty.live_spec
#print axioms REWB.MaskedTraversalDirty.crossing_spec
#print axioms REWB.MaskedTraversalRepair.anchorsLoop_read
#print axioms REWB.MaskedTraversalRepair.anchorsLoop_bounds
#print axioms REWB.MaskedTraversalRepair.banksLoop_selected
#print axioms REWB.MaskedTraversalRepair.banksLoop_budget
#print axioms REWB.MaskedTraversalRepair.reset_current
#print axioms REWB.MaskedTraversalRepair.reset_work
