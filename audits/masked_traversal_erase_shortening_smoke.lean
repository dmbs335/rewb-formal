import REWB.MaskedTraversalAggregateErase
import REWB.MaskedTraversalBankReadySemantics

/-! A source repair must compile at the current aggregate length. The
fixture has a stable dense q=2 cluster when H=5 is shortened to L=4;
reloading the historical stored length changes both positive and negative
answers. The production eraseCurrent path is compared with raw cuts.
-/
namespace REWB.MaskedTraversalAggregate.EraseAudit
open REWB.MaskedCluster REWB.MaskedFiniteAction

abbrev all : DFA (Fin 3) := ⟨1,0,fun _ _=>0,fun _=>true⟩
def parity (even : Bool) : DFA (Fin 3) :=
  ⟨2,0,fun q _=>if q==0 then 1 else 0,fun q=>if even then q==0 else q==1⟩

def check (b : Bool) (message : String) : IO Unit := unless b do throw (IO.userError message)

def reference (C : DFA (Fin 3)) (w : Word (Fin 3)) (source target : Array Bool) (L : Nat) : Bool :=
  (List.range (w.length+1)).any fun p=>(List.range (w.length+1)).any fun j=>
    source[p]?.getD false && target[j]?.getD false && decide (p+L≤j ∧ j+L≤w.length) &&
    (Spec.slice w p (p+L)==Spec.slice w j (j+L)) && C.final (C.run C.initial (Spec.slice w (p+L) j))

def runOne (even : Bool) : IO Nat := do
  let text : Array (Fin 3):=#[0,1,0,1,0,1,0,1,0,2,2,2,0,1,0,1,0]
  let w:=text.toList
  let n:=text.size
  let h:=(n+1).log2+1
  let capacity:=2^h
  let C:=parity even
  let source:=Array.ofFn fun p : Fin (n+1)=>[0,2,4,12].contains p.val
  let target:=Array.ofFn fun p : Fin (n+1)=>p.val==12
  let occurrences:=(List.range (n+1)).filter fun p=>
    decide (p+5≤n) && (Spec.slice w p (p+5)==Spec.slice w 0 5)
  let shorter:=(List.range (n+1)).filter fun p=>
    decide (p+4≤n) && (Spec.slice w p (p+4)==Spec.slice w 0 4)
  check (occurrences==[0,2,4,12] && shorter==occurrences) "fixture class changes"
  let partition:=(MaskedClusterLeaders.execute h 5
    (occurrences.reverse.map MaskedClusterLeaders.Operation.insert)).state
  check (partition.leaders.entries==[0,12]) "fixture dense geometry"
  let book:=ReplayMaps.prepare C.stateCount all.stateCount
  let prepared:=MaskedCluster.prepare C.stateCount all.stateCount
  let ci:=BoundaryApplication.Range.build C w
  let ei:=BoundaryApplication.Range.build all w
  let env:Clip.Env C all:=⟨book,prepared,ci,ei,target⟩
  let sources:=MaskedMutableProgression.Batch.prepare text 0 source prepared.K
  let catalog:=MaskedRunCatalog.ofBatch target sources
  let classes:=MaskedSuffixClass.prepare text 0
  let anchors:=Array.replicate (n+1) (some 5)
  let mut st:=Mutable.Store.empty C all sources
  for first in partition.leaders.entries do
    st:=MaskedTraversalBankReady.write C all book prepared ci ei partition capacity first 5 anchors
      ⟨true,0,n+1⟩ catalog classes target st
  let initial:=(refreshMany st partition.leaders.entries (fresh (prepare C all h)).1).1
  let z:=(replay C all ci ei 0 4 5).maps
  let mut tree:=(shorten (bankAction z) initial).1
  let cut:=Cut.build all C all w
  let ask:=fun t=>queryBand all C all cut t 0 (n+1) 0 4 4 4
  let expected:=reference C w source target 4
  check ((ask tree).answer==expected && expected==even) "initial shortening mismatch"
  let legacy:=Mutable.Store.eraseSource C all book prepared ci ei partition capacity target 0 st
  let stale:=(refresh legacy 0 tree).1
  let afterZero:=source.setIfInBounds 0 false
  let expectedZero:=reference C w afterZero target 4
  check ((ask stale).answer != expectedZero) "fixture failed to expose historical-length reload"
  let mut live:=source
  let mut checks:=1
  let mut maxWork:=0
  for p in [12,0,2,4,1] do
    let beforeTree:=tree
    let prior:=(ask beforeTree).answer
    let changed:=eraseCurrent env partition capacity 4 p st tree
    check changed.ready "actual current-length repair rejected"
    check (decide (changed.calls≤1)) "more than one compilation"
    st:=changed.store
    tree:=changed.tree
    live:=live.setIfInBounds p false
    let expectedNow:=reference C w live target 4
    check ((ask tree).answer==expectedNow) s!"erasure mismatch even={even} p={p}"
    check ((ask beforeTree).answer==prior) "persistent tree mutated"
    if let some first:=(MaskedClusterDescriptor.locate partition capacity p).1 then
      let some entry:=st.slots[first]?.join | throw (IO.userError "selected slot missing")
      check (entry.config.length==4 && entry.config.anchor==5) "current length/retained anchor mismatch"
    maxWork:=max maxWork changed.work
    checks:=checks+1
  IO.println s!"eraseAfterShortening even={even} old=5 current=4 densePeriod=2 checks={checks} historicalReloadCounterexample=true maxRepairWork={maxWork} targetRetained=true mismatches=0"
  return checks

end REWB.MaskedTraversalAggregate.EraseAudit

def main : IO Unit := do
  let begin←IO.monoMsNow
  let a←REWB.MaskedTraversalAggregate.EraseAudit.runOne false
  let b←REWB.MaskedTraversalAggregate.EraseAudit.runOne true
  let finish←IO.monoMsNow
  IO.println s!"eraseAfterShorteningComplete checks={a+b} mismatches=0 elapsed={finish-begin}ms"
