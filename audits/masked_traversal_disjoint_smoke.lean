import REWB.MaskedTraversalAnswersRegression
import REWB.MaskedTraversalAggregateCollectCost

/-! Two actual disjoint occurrence frontiers share one mutable source
batch, bank store and anchor array. Reporting and repairing the first
must retain every compiled cell of the suspended second, which then
reports against the globally updated source snapshot.
-/
namespace REWB.MaskedTraversalAggregate.DisjointAudit
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedTraversalRepairCoherence

deriving instance BEq for SourceWindow
deriving instance BEq for Mutable.Store.Config

abbrev all : DFA (Fin 3) := ⟨1,0,fun _ _=>0,fun _=>true⟩

def check (b : Bool) (message : String) : IO Unit := unless b do throw (IO.userError message)

def run : IO Unit := do
  let begin←IO.monoMsNow
  let text : Array (Fin 3):=#[0,1,0,1,0,1,0,1,0,2,2,2,0,1,0,1,0]
  let n:=text.size
  let h:=(n+1).log2+1
  let capacity:=2^h
  let A:=(MaskedClusterLeaders.execute h 4 ([0,2,4,12].map MaskedClusterLeaders.Operation.insert)).state
  let S:=(MaskedClusterLeaders.execute h 4 ([1,3,5,13].map MaskedClusterLeaders.Operation.insert)).state
  let source:=Array.ofFn fun p : Fin (n+1)=>[0,1,2,3,4,5,12,13].contains p.val
  let target:=Array.ofFn fun p : Fin (n+1)=>[12,13].contains p.val
  let prepared:=MaskedCluster.prepare all.stateCount all.stateCount
  let batch:=MaskedMutableProgression.Batch.prepare text 0 source prepared.K
  let env : Env all all n (MaskedSuffixClass.height n):=
    ⟨⟨ReplayMaps.prepare all.stateCount all.stateCount,prepared,
      BoundaryApplication.Range.build all text.toList,BoundaryApplication.Range.build all text.toList,target⟩,
      ⟨true,0,n+1⟩,MaskedRunCatalog.ofBatch target batch,MaskedSuffixClass.prepare text 0⟩
  let blank:=(MaskedTraversalAggregate.prepare all all h).blank
  let empty:=Mutable.Store.empty all all batch
  let initialAnchors:=Array.replicate (n+1) none
  let keysA:=MaskedTraversalDirty.markList capacity A.leaders.entries (MaskedTraversalDirty.empty h)
  let keysS:=MaskedTraversalDirty.markList capacity S.leaders.entries (MaskedTraversalDirty.empty h)
  let builtA:=apply env A capacity 4 initialAnchors keysA empty blank
  let builtS:=apply env S capacity 4 builtA.anchors keysS builtA.store blank
  let cut:=Cut.build all all all text.toList
  let answers:=MaskedTraversalAnswers.fromBits (Array.replicate (n+1) false)
  let outA:=Collect.run all all all cut env.shared builtS.store A capacity builtA.tree 0 4 4 4 answers
  check (outA.band.reported.starts==[0,2,4] && outA.band.repaired.ready) "first actual report"
  let resetA:=apply env A capacity 4 builtS.anchors keysA outA.band.repaired.store outA.band.repaired.tree
  let mut cells:=0
  for first in S.leaders.entries do
    let some previous:=builtS.store.slots[first]?.join | throw (IO.userError "saved initial bank absent")
    let some after:=resetA.store.slots[first]?.join | throw (IO.userError "saved bank overwritten")
    check (previous.config==after.config) "saved configuration changed"
    check (resetA.anchors[first]?==builtS.anchors[first]?) "saved anchor overwritten"
    let some actual:=(Clip.compiled env.shared resetA.store after.config).1 | throw (IO.userError "saved current compiler rejected")
    for a in List.ofFn (fun i : Fin (2*ReplayMaps.count all.stateCount all.stateCount)=>i) do
      for i in List.ofFn (fun i : Fin (2*(MaskedClusterStage.dfa all all).stateCount)=>i) do
        for j in List.ofFn (fun i : Fin (2*(MaskedClusterStage.dfa all all).stateCount)=>i) do
          check (previous.bank.view a i j==after.bank.view a i j && after.bank.view a i j==actual.view a i j)
            "suspended compiled bank changed after global source erasure"
          cells:=cells+1
  let outS:=Collect.run all all all cut env.shared resetA.store S capacity builtS.tree 1 4 4 4 outA.answers
  check (outS.band.reported.starts==[1,3,5] && outS.band.repaired.ready) "suspended report against current sources"
  check (outS.answers.history==[5,3,1,4,2,0] && outS.answers.count==6 && outS.answers.history.Nodup) "cross-frontier output history"
  for p in List.range (n+1) do
    check (MaskedProgression.readMask outS.answers.bits p==[0,1,2,3,4,5].contains p) "physical output union"
    check ((MaskedMutableProgression.member outS.band.repaired.store.sources.singleton p).1==[12,13].contains p)
      "global live sources after two frontiers"
  check (env.shared.target==target && env.shared.target[12]?.getD false && env.shared.target[13]?.getD false) "immutable target masks"
  let again:=Reporting.run all all all cut env.shared outS.band.repaired.store A capacity resetA.tree 0 4 4 4
  check (again.reported.starts.isEmpty && again.reported.calls==1 && again.repaired.ready) "prior frontier regained removed sources"
  let finish←IO.monoMsNow
  IO.println s!"disjoint suspended frontiers: reports=2 outputs=6 savedCells={cells} queries={outA.band.reported.calls+outS.band.reported.calls+again.reported.calls} mismatches=0 elapsed={finish-begin}ms"

end REWB.MaskedTraversalAggregate.DisjointAudit

def main : IO Unit := REWB.MaskedTraversalAggregate.DisjointAudit.run
