import REWB.MaskedTraversalRepairCoherenceRegression

/-! Actual reset/context/aggregate execution after lazy shortening. Every
leaf is compared with its current-length compiler, and every active leaf
with literal physical cursor transitions. All scans are audit references.
-/
namespace REWB.MaskedTraversalRepairCoherence.Audit
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedTraversalAggregate

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

def fixture (label : String) (text : Array (Fin 3)) (H L : Nat) (resets : List Nat)
    (retired : Option Nat:=none) : IO (Nat×Nat×Nat) := do
  let n:=text.size
  let h:=(n+1).log2+1
  let capacity:=2^h
  let w:=text.toList
  let oldOccurrences:=(List.range (n+1)).filter fun p=>
    decide (p+H≤n ∧ Spec.slice w p (p+H)=Spec.slice w 0 H)
  let occurrences:=(List.range (n+1)).filter fun p=>
    decide (p+L≤n ∧ Spec.slice w p (p+L)=Spec.slice w 0 L)
  unless oldOccurrences=occurrences do throw (IO.userError "fixture changed occurrence class")
  let oldPartition:=(MaskedClusterLeaders.execute h H (oldOccurrences.map MaskedClusterLeaders.Operation.insert)).state
  let partition:=(MaskedClusterLeaders.execute h L (occurrences.map MaskedClusterLeaders.Operation.insert)).state
  unless oldPartition.leaders.entries=partition.leaders.entries do throw (IO.userError "fixture changed cluster leaders")
  let source:=Array.ofFn (fun i : Fin (n+1)=>decide (i.val%5 != 2))
  let target:=Array.ofFn (fun i : Fin (n+1)=>decide (i.val%3=0 ∨ i.val%7=4))
  let live:=(source.setIfInBounds 0 false).setIfInBounds 7 false
  let prepared:=MaskedCluster.prepare C.stateCount E.stateCount
  let book:=ReplayMaps.prepare C.stateCount E.stateCount
  let sources:=MaskedMutableProgression.Batch.run text 0 source prepared.K [0,7,n+5]
  let catalog:=MaskedRunCatalog.ofBatch target sources
  let classes:=MaskedSuffixClass.prepare text 0
  let ci:=BoundaryApplication.Range.build C w
  let ei:=BoundaryApplication.Range.build E w
  let env : Env C E n (MaskedSuffixClass.height n):=⟨⟨book,prepared,ci,ei,target⟩,⟨true,1,n⟩,catalog,classes⟩
  let anchors:=Array.replicate (n+1) (some H)
  let mut st:=Mutable.Store.empty C E sources
  for first in oldPartition.leaders.entries do
    st:=MaskedTraversalBankReady.write C E book prepared ci ei oldPartition capacity first H anchors
      env.window catalog classes target st
  let template:=MaskedTraversalAggregate.prepare C E h
  let mut tree:=(refreshMany st oldPartition.leaders.entries template.blank).1
  let replay:=ReplayMaps.word C E (Spec.slice w L H)
  tree:=(MaskedTraversalAggregate.shorten (bankAction replay) tree).1
  if let some p:=retired then
    let first:=oldPartition.leaders.entries.head!
    let some entry:=st.slots[first]?.join | throw (IO.userError "retired fixture donor absent")
    st:={st with slots:=st.slots.setIfInBounds p (some entry)}
    tree:=(refresh st p tree).1
  let keys:=MaskedTraversalDirty.markList capacity (resets++retired.toList) (MaskedTraversalDirty.empty h)
  for first in partition.leaders.entries do
    unless keys.keys.positions.contains first do
      let some d:=(MaskedClusterDescriptor.describeLeader partition capacity first).1 | throw (IO.userError "descriptor absent")
      let anchor:=MaskedTraversalBankReady.readAnchor anchors first L
      let next:=d.nextAt n
      unless L≤anchor && d.last+anchor≤n && d.previous.all (fun p=>p+anchor≤next) &&
          d.following.all (fun p=>d.last+anchor≤p) &&
          decide (next<d.last+anchor)=decide (next<d.last+L) do
        throw (IO.userError "fixture violates the unmarked retained-certificate premise")
      for p in MaskedTraversalRetained.copies d do
        unless p+anchor≤n && Spec.slice w p (p+anchor)=Spec.slice w first (first+anchor) do
          throw (IO.userError "fixture violates the unmarked H-word premise")
  let oldWrites:=st.writes
  let out:=apply env partition capacity L anchors keys st tree
  unless out.work≤repairBudget C E prepared.K n h*keys.keys.positions.length+16 do
    throw (IO.userError "whole repair exceeded proved local bound")
  unless out.store.writes=oldWrites+keys.keys.positions.length+out.contexts.keys.positions.length do
    throw (IO.userError "bank writes differ from actual sparse primary/context lengths")
  for p in List.range (n+1) do
    let a:=(MaskedMutableProgression.member out.store.sources.singleton p).1
    unless a=live[p]?.getD false do throw (IO.userError "bank repair changed source history")
  let leaves:=out.tree.leaves.toArray
  let rows:=List.ofFn (fun i : Fin (2*ReplayMaps.count C.stateCount E.stateCount)=>i)
  let states:=List.ofFn (fun i : Fin (2*(MaskedClusterStage.dfa C E).stateCount)=>i)
  let modes:=List.ofFn (fun i : Fin (MaskedClusterStage.dfa C E).stateCount=>i)
  let identity:=ReplayMaps.encode (ReplayMaps.one C.stateCount E.stateCount)
  let mut replayCells:=0
  let mut physicalCells:=0
  let mut retainedRaw:=0
  for p in List.range capacity do
    let leaf:=leaves[p]?.getD View.one
    if partition.leaders.entries.contains p then
      let some raw:=out.store.slots[p]?.join | throw (IO.userError "actual leader lost its raw slot")
      let some desc:=(MaskedClusterDescriptor.describeLeader partition capacity p).1 | throw (IO.userError "leader descriptor absent")
      let incoming:=MaskedTraversalBankReady.incoming partition capacity p L out.anchors
      unless raw.config.descriptor=desc && raw.config.anchor=MaskedTraversalBankReady.readAnchor out.anchors p L &&
          raw.config.incoming=incoming.cursor && raw.config.incomingEnabled=incoming.enabled do
        throw (IO.userError "actual raw descriptor/anchor/context linkage failed")
      let cfg:=withLength raw.config L
      let some expected:=(Clip.compiled env.shared out.store cfg).1 | throw (IO.userError "current compiler absent")
      for row in rows do
        for i in states do
          for j in states do
            unless leaf row i j=expected.view row i j do
              throw (IO.userError s!"{label}: aggregate/current bank mismatch at {p}, raw L={raw.config.length}, current L={L}")
            replayCells:=replayCells+1
      for gate in [false,true] do
        for im in [false,true] do
          for om in [false,true] do
            for i in modes do
              for j in modes do
                unless leaf (code _ gate identity) (code _ im i) (code _ om j)=
                    physical w cfg im om live target gate (MaskedClusterStage.decode C E i) (MaskedClusterStage.decode C E j) do
                  throw (IO.userError s!"{label}: physical cursor mismatch at {p}")
                physicalCells:=physicalCells+1
      if L<raw.config.length then retainedRaw:=retainedRaw+1
    else
      for row in rows do
        for i in states do
          for j in states do
            unless leaf row i j=decide (i=j) do throw (IO.userError "inactive/retired aggregate leaf is not identity")
            replayCells:=replayCells+1
  if let some p:=retired then
    unless (out.store.slots[p]?.join).isNone do throw (IO.userError "retired raw slot was not cleared")
  IO.println s!"{label}: H={H}, L={L}, primary={keys.keys.positions}, context={out.contexts.keys.positions}, retained old raw lengths={retainedRaw}, all replay cells={replayCells}, physical cells={physicalCells}, measured work={out.work}, mismatches=0"
  return (replayCells,physicalCells,retainedRaw)

def run : IO Unit := do
  let begin ←IO.monoMsNow
  let dense : Array (Fin 3):=#[0,0,1,0,0,1,0,0,0,1,0,0,1,0,0,1,0,0,2,2,2,2,0,0,1,0,0,1,0,0]
  let point : Array (Fin 3):=#[0,0,1,0,0,1,0,0,1,0,0]
  let a ←fixture "dense retained H plus lazy old raw length" dense 8 7 [0]
  let b ←fixture "singleton retained H plus incoming change" point 5 4 [0]
  let c ←fixture "adjacent primary resets" point 5 4 [0,3]
  let d ←fixture "retired leaf cleared" dense 8 7 [0] (some 1)
  -- Dense H=8 -> L=7 above crosses the first cluster's overlap boundary
  -- and requires its real reset. Use the stable point band for no-op.
  let e ←fixture "empty update retains lazy shortened banks" point 5 4 []
  unless a.2.2+d.2.2+e.2.2>0 do throw (IO.userError "stale raw-length case was not exercised")
  let finish ←IO.monoMsNow
  IO.println s!"actual repair coherence: fixtures=5, replay cells={a.1+b.1+c.1+d.1+e.1}, physical cells={a.2.1+b.2.1+c.2.1+d.2.1+e.2.1}, mismatches=0, elapsed={finish-begin} ms"
  IO.println "Actual two-pass repair, retained successor refresh, current raw-length normalization and sparse aggregate replacement agree. Whole-Driver pending-invariant induction and global repair charging remain separate."

end REWB.MaskedTraversalRepairCoherence.Audit

def main : IO Unit := REWB.MaskedTraversalRepairCoherence.Audit.run

#print axioms REWB.MaskedTraversalRepairCoherence.apply_sources
#print axioms REWB.MaskedTraversalRepairCoherence.apply_represents
#print axioms REWB.MaskedTraversalRepairCoherence.compile_present
#print axioms REWB.MaskedTraversalRepairCoherence.reset_runBacked
#print axioms REWB.MaskedTraversalRepairCoherence.refreshLoop_selected
#print axioms REWB.MaskedTraversalRepairCoherence.resetBanks_present
#print axioms REWB.MaskedTraversalRepairCoherence.resetBanks_raw
#print axioms REWB.MaskedTraversalRepairCoherence.model_get
#print axioms REWB.MaskedTraversalRepairCoherence.apply_selected
#print axioms REWB.MaskedTraversalRepairCoherence.apply_coherent
#print axioms REWB.MaskedTraversalRepairCoherence.apply_linked
#print axioms REWB.MaskedTraversalRepairCoherence.apply_complete
#print axioms REWB.MaskedTraversalRepairCoherence.apply_anchors
#print axioms REWB.MaskedTraversalRepairCoherence.raw_geometry
#print axioms REWB.MaskedTraversalRepairCoherence.apply_work
