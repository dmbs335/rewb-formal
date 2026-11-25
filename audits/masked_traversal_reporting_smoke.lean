import REWB.MaskedTraversalAggregateReportingCorrect
import REWB.MaskedTraversalBankReadySemantics

/-! Execute the actual shared-cut interval reporter and current-length
erase fold, comparing every emitted source with independent text cuts.
The same fixed complete class supports lazy shortening and a band with
two possible lengths. Reported source bits are removed, targets retained.
-/
namespace REWB.MaskedTraversalAggregate.ReportingAudit
open REWB.MaskedCluster REWB.MaskedFiniteAction

abbrev all : DFA (Fin 3) := ⟨1,0,fun _ _=>0,fun _=>true⟩
def parity (even : Bool) : DFA (Fin 3) :=
  ⟨2,0,fun q _=>if q==0 then 1 else 0,fun q=>if even then q==0 else q==1⟩
def check (b : Bool) (message : String) : IO Unit := unless b do throw (IO.userError message)

def reference (C : DFA (Fin 3)) (w : Word (Fin 3)) (source target : Array Bool)
    (partition : MaskedClusterLeaders.State h) (capacity lo hi : Nat) : List Nat :=
  (List.range (w.length+1)).filter fun p=>source[p]?.getD false &&
    (List.range (hi+1-lo)).any fun offset=>
      let L:=lo+offset
      (List.range (w.length+1)).any fun j=>target[j]?.getD false &&
        decide (p+L≤j ∧ j+L≤w.length) &&
        (Spec.slice w p (p+L)==Spec.slice w 0 L) &&
        (Spec.slice w p (p+L)==Spec.slice w j (j+L)) &&
        decide ((MaskedClusterDescriptor.locate partition capacity p).1≠(MaskedClusterDescriptor.locate partition capacity j).1) &&
        C.final (C.run C.initial (Spec.slice w (p+L) j))

def runOne (even shortened : Bool) (removed : List Nat) : IO (Nat×Nat) := do
  let text : Array (Fin 3):=#[0,1,0,1,0,1,0,1,0,2,2,2,0,1,0,1,0]
  let w:=text.toList
  let n:=text.size
  let h:=(n+1).log2+1
  let capacity:=2^h
  let C:=parity even
  let original:=Array.ofFn fun p : Fin (n+1)=>[0,2,4,12].contains p.val
  let live:=removed.foldl (fun a p=>a.setIfInBounds p false) original
  let target:=Array.ofFn fun p : Fin (n+1)=>p.val==12
  let occurrences:=[0,2,4,12]
  for L in [4,5] do
    let actual:=(List.range (n+1)).filter fun p=>decide (p+L≤n) && (Spec.slice w p (p+L)==Spec.slice w 0 L)
    check (actual==occurrences) "fixture complete class changed"
  let partition:=(MaskedClusterLeaders.execute h 5 (occurrences.reverse.map MaskedClusterLeaders.Operation.insert)).state
  let book:=ReplayMaps.prepare C.stateCount all.stateCount
  let prepared:=MaskedCluster.prepare C.stateCount all.stateCount
  let ci:=BoundaryApplication.Range.build C w
  let ei:=BoundaryApplication.Range.build all w
  let env:Clip.Env C all:=⟨book,prepared,ci,ei,target⟩
  let batch:=MaskedMutableProgression.Batch.prepare text 0 original prepared.K
  let sources:=MaskedMutableProgression.Batch.eraseMany removed batch
  let catalog:=MaskedRunCatalog.ofBatch target batch
  let classes:=MaskedSuffixClass.prepare text 0
  let anchors:=Array.replicate (n+1) (some 5)
  let mut st:=Mutable.Store.empty C all sources
  for first in partition.leaders.entries do
    st:=MaskedTraversalBankReady.write C all book prepared ci ei partition capacity first 5 anchors
      ⟨true,0,n+1⟩ catalog classes target st
  let initial:=(refreshMany st partition.leaders.entries (fresh (prepare C all h)).1).1
  let tree:=if shortened then (shorten (bankAction (replay C all ci ei 0 4 5).maps) initial).1 else initial
  let old:=if shortened then 4 else 5
  let cut:=Cut.build all C all w
  let expected:=reference C w live target partition capacity 4 old
  let out:=Reporting.run all C all cut env st partition capacity tree 0 4 old old
  check (out.reported.starts==expected) s!"report mismatch even={even} shortened={shortened} removed={removed} got={out.reported.starts} expected={expected}"
  check out.repaired.ready "current source repair rejected"
  check (decide (out.reported.calls≤1+2*h*expected.length)) "output-sensitive call bound"
  check (decide (out.repaired.calls≤expected.length)) "one affected bank per report"
  let budget:=Reporting.queryBudget all C all prepared.K h n
  check (decide (out.reported.queryWork≤budget*out.reported.calls)) "actual query budget"
  let R:=11*h+25+Mutable.Store.bankLimit C all prepared.K n+
    (h+1)*Tree.replaceBudget (2*ReplayMaps.count C.stateCount all.stateCount) (2*(MaskedClusterStage.dfa C all).stateCount)+
    MaskedMutableProgression.Batch.requestBudget n
  check (decide (MaskedReporting.totalWork out.reported+out.repaired.work+out.repaired.store.sources.updateWork+
    st.sources.delivered*MaskedMutableProgression.Batch.rowBudget n≤st.sources.updateWork+(budget+1)+
    ((2*budget+3)*h+R)*expected.length+out.repaired.store.sources.delivered*MaskedMutableProgression.Batch.rowBudget n)) "combined repair/fanout charge"
  check (out.repaired.store.sources.delivered+out.repaired.store.sources.sources.memberships==
    st.sources.delivered+st.sources.sources.memberships) "fanout balance"
  for p in List.range (n+1) do
    let active:=(MaskedMutableProgression.member out.repaired.store.sources.singleton p).1
    check (active==(live[p]?.getD false && !expected.contains p)) s!"actual source removal p={p}"
  let again:=Reporting.run all C all cut env out.repaired.store partition capacity out.repaired.tree 0 4 old old
  check (again.reported.starts.isEmpty && again.reported.calls==1 && again.repaired.ready) "band not exhausted"
  check (env.target==target && env.target[12]?.getD false) "target was removed"
  check ((Reporting.run all C all cut env st partition capacity tree 0 4 old old).reported.starts==expected) "persistent pre-report state changed"
  IO.println s!"bandReport even={even} shortened={shortened} prior={removed} starts={out.reported.starts} calls={out.reported.calls} repairCalls={out.repaired.calls} queryUnits={out.reported.queryWork} repairUnits={out.repaired.work} fanoutDelivered={out.repaired.store.sources.delivered-st.sources.delivered} exhausted=true mismatches=0"
  return (out.reported.calls,expected.length)

end REWB.MaskedTraversalAggregate.ReportingAudit

def main : IO Unit := do
  let begin←IO.monoMsNow
  let mut calls:=0
  let mut outputs:=0
  let mut cases:=0
  for even in [false,true] do
    for shortened in [false,true] do
      for removed in [[],[2],[0,4],[0,2,4],[12]] do
        let (c,k)←REWB.MaskedTraversalAggregate.ReportingAudit.runOne even shortened removed
        calls:=calls+c
        outputs:=outputs+k
        cases:=cases+1
  let finish←IO.monoMsNow
  IO.println s!"bandReportComplete cases={cases} calls={calls} outputs={outputs} mismatches=0 elapsed={finish-begin}ms"
