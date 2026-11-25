import REWB.MaskedTraversalExecuteSupport
import REWB.MaskedTraversalInitial

/-! Concrete end-to-end execution probe, including actual initialization,
all geometric plan operations, sparse banks, shared-cut reports and source
erasure. The finite nested loop below is only the independent audit oracle.
Universal Driver correctness and global repair charging are separate proof
obligations, not inferred from these finite comparisons.
-/
namespace REWB.MaskedTraversalExecute.Audit
open REWB.MaskedCluster REWB.MaskedTraversalAggregate

def B : DFA (Fin 2) := ⟨2,0,fun q _=>if q=0 then 1 else 0,fun q=>q==1⟩
def C : DFA (Fin 2) := ⟨1,0,fun _ _=>0,fun _=>true⟩
def E : DFA (Fin 2) := ⟨1,0,fun _ _=>0,fun _=>true⟩

def direct (w : Word (Fin 2)) (source target : Array Bool) (s : Nat) : Bool :=
  source[s]?.getD false && (List.range (w.length+1)).any fun L=>
    (List.range (w.length+1)).any fun j=>
      decide (s+L≤j ∧ j+L≤w.length) && target[j]?.getD false &&
        decide (Spec.slice w s (s+L)=Spec.slice w j (j+L)) &&
        B.final (B.run B.initial (Spec.slice w s (s+L))) &&
        C.final (C.run C.initial (Spec.slice w (s+L) j)) &&
        E.final (E.run E.initial (Spec.slice w (j+L) w.length))

def words : Nat→List (List (Fin 2))
  | 0=>[[]]
  | k+1=>(words k).flatMap fun w=>[0::w,1::w]

def probe (text : Array (Fin 2)) (mode : Nat) : IO (Nat×Nat×Nat×Nat) := do
  let n:=text.size
  let w:=text.toList
  let h:=(n+1).log2+1
  let source:=Array.ofFn fun p : Fin (n+1)=>if mode=0 then true else decide ((p.val*3+mode)%5 != 1)
  let target:=Array.ofFn fun p : Fin (n+1)=>if mode=0 then true else decide ((p.val*p.val+mode)%7≤3)
  let prepared:=MaskedCluster.prepare C.stateCount E.stateCount
  let started:=MaskedTraversalInitial.start B C E text 0 source target prepared.K
  let repair : MaskedTraversalRepairCoherence.Env C E n (MaskedSuffixClass.height n):=
    ⟨⟨ReplayMaps.prepare C.stateCount E.stateCount,prepared,
        BoundaryApplication.Range.build C w,BoundaryApplication.Range.build E w,target⟩,
      ⟨true,0,n+1⟩,MaskedRunCatalog.ofBatch target started.sources,MaskedSuffixClass.prepare text 0⟩
  let env : Env B C E n (MaskedSuffixClass.height n):=⟨repair,Cut.build B C E w⟩
  let template:=MaskedTraversalAggregate.prepare C E h
  let geometry:=MaskedTraversalDriver.run h (MaskedRunDiscovery.prepareSuffixes text 0).trie.tree
  let global : Global C E:=⟨Array.replicate (n+1) none,Mutable.Store.empty C E started.sources,started.answers,{}⟩
  let out:=plan env template.capacity template geometry.plan global
  unless out.global.stats.bands=geometry.bands do throw (IO.userError "band omitted or duplicated")
  unless out.global.stats.actionBuilds=geometry.bands do throw (IO.userError "replay selection count mismatch")
  unless out.global.answers.count≤n+1 do throw (IO.userError "duplicate reported source")
  unless out.global.store.sources.runs=started.sources.runs do throw (IO.userError "immutable run array changed")
  unless out.global.answers.history.length=out.global.answers.count do throw (IO.userError "answer count mismatch")
  for s in List.range (n+2) do
    let got:=out.global.answers.bits[s]?.getD false
    let expected:=direct w source target s
    unless got=expected do
      throw (IO.userError s!"actual Driver mismatch text={w}, mode={mode}, source={s}, got={got}, expected={expected}")
    let live:=(MaskedMutableProgression.member out.global.store.sources.singleton s).1
    unless live=(source[s]?.getD false && !got) do throw (IO.userError "global source/output partition mismatch")
  return (n+2,out.global.stats.bands,out.global.stats.queryCalls,out.global.stats.reported)

def run : IO Unit := do
  let begin←IO.monoMsNow
  let mut cases:=0
  let mut comparisons:=0
  let mut bands:=0
  let mut calls:=0
  let mut reported:=0
  for n in List.range 3 do
    for w in words n do
      for mode in [0,1,4] do
        let (a,b,c,d)←probe w.toArray mode
        cases:=cases+1
        comparisons:=comparisons+a
        bands:=bands+b
        calls:=calls+c
        reported:=reported+d
    IO.println s!"completed length {n}, cases={cases}"
    (←IO.getStdout).flush
  for w in [[0,1,0,1,0,1,1,0],[0,0,0,0,0,0,0,0],[0,1,1,0,0,1,0,1,1,0]] do
    let (a,b,c,d)←probe w.toArray 4
    cases:=cases+1
    comparisons:=comparisons+a
    bands:=bands+b
    calls:=calls+c
    reported:=reported+d
  let finish←IO.monoMsNow
  IO.println s!"actual Driver execution: cases={cases}, mask/source comparisons={comparisons}, bands={bands}, query calls={calls}, newly reported={reported}, mismatches=0, elapsed={finish-begin} ms"
  IO.println "Initialization, all plan bands, source deletion and immutable target masks use actual implementations; universal Driver induction/global cost remain separate."

end REWB.MaskedTraversalExecute.Audit

def main : IO Unit:=REWB.MaskedTraversalExecute.Audit.run

#print axioms REWB.MaskedTraversalRepairTransport.reindexed_get
#print axioms REWB.MaskedTraversalRepairTransport.shortened_entry
#print axioms REWB.MaskedTraversalRepairTransport.crossing_same_pending
#print axioms REWB.MaskedTraversalRepairTransport.crossing_pending
#print axioms REWB.MaskedTraversalRepairTransport.reindexed_unclipped
#print axioms REWB.MaskedTraversalExecute.band_count
#print axioms REWB.MaskedTraversalExecute.band_actions
#print axioms REWB.MaskedTraversalExecute.bands_count
#print axioms REWB.MaskedTraversalExecute.bands_actions
#print axioms REWB.MaskedTraversalExecute.edge_equal
#print axioms REWB.MaskedTraversalExecute.supported_mono
#print axioms REWB.MaskedTraversalExecute.coherent_supported
#print axioms REWB.MaskedTraversalExecute.supported_reindexed
#print axioms REWB.MaskedTraversalExecute.dirty_empty
#print axioms REWB.MaskedTraversalExecute.change_supported
#print axioms REWB.MaskedTraversalExecute.marked_supported
#print axioms REWB.MaskedTraversalExecute.add_supported
#print axioms REWB.MaskedTraversalExecute.crossing_supported
