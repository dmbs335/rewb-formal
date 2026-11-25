import REWB.MaskedTraversalRepairSnapshotRegression

/-! Repeated real report erasures interleaved with the same permanent
repair operation. The current source state comes from actual eraseMany;
the audit never substitutes a reconstructed Batch.run snapshot.
-/
namespace REWB.MaskedTraversalRepairCoherence.SnapshotAudit
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedTraversalAggregate

def C : DFA (Fin 3) := ⟨1,0,fun _ _=>0,fun _=>true⟩
def E : DFA (Fin 3) := ⟨1,0,fun _ _=>0,fun _=>true⟩

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
          (gate && source[p]?.getD false) (target[p]?.getD false) input=some output)
    if om then jump else decide (MaskedClusterStage.read C E (Spec.slice w I next) input=output) || jump

def run : IO Unit := do
  let begin ←IO.monoMsNow
  let text : Array (Fin 3):=#[0,1,0,1,0,1,0,1,2,2,0,1,0,1,0,1,2,2,0,1,0,1]
  let n:=text.size
  let w:=text.toList
  let L:=4
  let h:=(n+1).log2+1
  let capacity:=2^h
  let occurrences:=(List.range (n+1)).filter fun p=>decide (p+L≤n ∧ Spec.slice w p (p+L)=Spec.slice w 0 L)
  let partition:=(MaskedClusterLeaders.execute h L (occurrences.map MaskedClusterLeaders.Operation.insert)).state
  let source:=Array.ofFn (fun i : Fin (n+1)=>decide (i.val%3 != 1))
  let target:=Array.ofFn (fun i : Fin (n+1)=>decide (i.val%5 != 3))
  let prepared:=MaskedCluster.prepare C.stateCount E.stateCount
  let book:=ReplayMaps.prepare C.stateCount E.stateCount
  let sources:=MaskedMutableProgression.Batch.prepare text 0 source prepared.K
  let env : Env C E n (MaskedSuffixClass.height n):=
    ⟨⟨book,prepared,BoundaryApplication.Range.build C w,BoundaryApplication.Range.build E w,target⟩,
      ⟨true,0,n+1⟩,MaskedRunCatalog.ofBatch target sources,MaskedSuffixClass.prepare text 0⟩
  let mut st:=Mutable.Store.empty C E sources
  let mut anchors:=Array.replicate (n+1) none
  let mut tree:=(MaskedTraversalAggregate.prepare C E h).blank
  let initialKeys:=MaskedTraversalDirty.markList capacity partition.leaders.entries (MaskedTraversalDirty.empty h)
  let initial:=apply env partition capacity L anchors initialKeys st tree
  st:=initial.store
  anchors:=initial.anchors
  tree:=initial.tree
  let mut live:=source
  let mut requests:=0
  let mut cells:=0
  let mut totalWork:=initial.work
  let identity:=ReplayMaps.encode (ReplayMaps.one C.stateCount E.stateCount)
  let states:=List.ofFn (fun i : Fin (MaskedClusterStage.dfa C E).stateCount=>i)
  for deleted in [[0,2,10],[2,99],[12,18],[]] do
    let erased:=MaskedTraversalAggregate.eraseMany env.shared partition capacity L deleted st tree
    unless erased.ready && erased.calls≤deleted.length do throw (IO.userError "actual report erase failed")
    for p in deleted do live:=live.setIfInBounds p false
    requests:=requests+deleted.length
    let keys:=MaskedTraversalDirty.markList capacity [0] (MaskedTraversalDirty.empty h)
    let out:=apply env partition capacity L anchors keys erased.store erased.tree
    unless out.work≤repairBudget C E prepared.K n h*keys.keys.positions.length+16 do throw (IO.userError "snapshot repair budget exceeded")
    unless out.store.sources.runs=sources.runs do throw (IO.userError "actual run provenance changed")
    let leaves:=out.tree.leaves.toArray
    for first in partition.leaders.entries do
      let some entry:=out.store.slots[first]?.join | throw (IO.userError "snapshot lost active bank")
      unless entry.config.window.enabled && entry.config.window.lo=0 && entry.config.window.hi=n+1 do
        throw (IO.userError "permanent full window changed")
      let leaf:=leaves[first]?.getD View.one
      for gate in [false,true] do
        for im in [false,true] do
          for om in [false,true] do
            for i in states do
              for j in states do
                unless leaf (code _ gate identity) (code _ im i) (code _ om j)=
                    physical w entry.config im om live target gate (MaskedClusterStage.decode C E i) (MaskedClusterStage.decode C E j) do
                  throw (IO.userError "snapshot repair disagrees with actual erased mask")
                cells:=cells+1
    for p in List.range (n+1) do
      unless (MaskedMutableProgression.member out.store.sources.singleton p).1=live[p]?.getD false do
        throw (IO.userError "source history changed during repair")
    st:=out.store
    anchors:=out.anchors
    tree:=out.tree
    totalWork:=totalWork+out.work
  let finish ←IO.monoMsNow
  IO.println s!"actual report/repair snapshots: reports=4, erase requests={requests}, physical cells={cells}, repair work={totalWork}, source update work={st.sources.updateWork}, mismatches=0, elapsed={finish-begin} ms"
  IO.println "Current validity/n/modulus and immutable run provenance suffice; no entire Batch.run or historical counter equality is assumed."

end REWB.MaskedTraversalRepairCoherence.SnapshotAudit

def main : IO Unit := REWB.MaskedTraversalRepairCoherence.SnapshotAudit.run

#print axioms REWB.MaskedTraversalRepairTransport.old_context_unmarked
#print axioms REWB.MaskedTraversalRepairTransport.repartition
#print axioms REWB.MaskedTraversalRepairTransport.add_pending
#print axioms REWB.MaskedTraversalRepairTransport.merge_pending
#print axioms REWB.MaskedTraversalRepairCoherence.apply_unclipped
#print axioms REWB.MaskedTraversalRepairCoherence.Snapshot.runBacked
#print axioms REWB.MaskedTraversalRepairCoherence.snapshot_reset_selected
#print axioms REWB.MaskedTraversalRepairCoherence.snapshot_reset_present
#print axioms REWB.MaskedTraversalRepairCoherence.snapshot_reset_raw
#print axioms REWB.MaskedTraversalRepairCoherence.snapshot_apply_selected
#print axioms REWB.MaskedTraversalRepairCoherence.snapshot_apply_present
#print axioms REWB.MaskedTraversalRepairCoherence.snapshot_apply_maintained
#print axioms REWB.MaskedTraversalRepairCoherence.snapshot_apply_anchors
#print axioms REWB.MaskedTraversalRepairCoherence.compile_snapshot_work
#print axioms REWB.MaskedTraversalRepairCoherence.reset_snapshot_work
#print axioms REWB.MaskedTraversalRepairCoherence.apply_snapshot_work
