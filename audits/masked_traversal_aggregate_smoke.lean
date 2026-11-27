import REWB.MaskedTraversalAggregateWindow
import REWB.MaskedTraversalBankReadySemantics

/-! Independent bounded cross-cluster cut enumeration. Production queries
use actual automatically prepared banks and one shared cut index. -/
namespace REWB.MaskedTraversalAggregate.Audit
open REWB.MaskedCluster REWB.MaskedFiniteAction

abbrev all : DFA (Fin 3) := ⟨1,0,fun _ _=>0,fun _=>true⟩
abbrev seen : DFA (Fin 3) := ⟨2,0,fun q x=>if x.val=1 then 1 else q,fun q=>q==1⟩
abbrev eps : DFA (Fin 3) := ⟨2,0,fun _ _=>1,fun q=>q==0⟩
abbrev odd : DFA (Fin 3) := ⟨2,0,fun q _=>if q==0 then 1 else 0,fun q=>q==1⟩

def accepts (A : DFA α) (w : Word α) : Bool := A.final (A.run A.initial w)

def check (b : Bool) (message : String) : IO Unit := unless b do throw (IO.userError message)

def reference (B C E : DFA (Fin 3)) (w : Word (Fin 3)) (members : List (Nat×Nat))
    (source target : Array Bool) (lo hi low high : Nat) (physicalWindow : Bool:=false) : Bool :=
  (List.range (high-low+1)).any fun offset=>
    let L:=low+offset
    members.any fun src=>members.any fun dst=>
      let position:=if physicalWindow then src.1 else src.2
      src.2!=dst.2 && decide (lo≤position ∧ position<hi ∧ src.1+L≤dst.1 ∧ dst.1+L≤w.length) &&
      source[src.1]?.getD false && target[dst.1]?.getD false &&
      (Spec.slice w src.1 (src.1+L)==Spec.slice w dst.1 (dst.1+L)) &&
      accepts B (Spec.slice w src.1 (src.1+L)) && accepts C (Spec.slice w (src.1+L) dst.1) &&
      accepts E (Spec.slice w (dst.1+L) w.length)

def fixture (label : String) (B C E : DFA (Fin 3)) (text : Array (Fin 3))
    (old low base : Nat) (targetOnly : Option Nat) (erases : List Nat) (storedCuts : Bool:=false) : IO (Nat×Nat) := do
  let w:=text.toList
  let n:=text.size
  let height:=(n+1).log2+1
  let capacity:=2^height
  let occurrences:=(List.range (n+1)).filter fun p=>
    decide (p+old≤n) && (Spec.slice w p (p+old)==Spec.slice w base (base+old))
  let partition:=(MaskedClusterLeaders.execute height old
    (occurrences.reverse.map MaskedClusterLeaders.Operation.insert)).state
  let leaders:=partition.leaders.entries
  let source:=Array.ofFn fun p : Fin (n+1)=>decide (p.val%2=0 ∨ p.val%3=0)
  let target:=Array.ofFn fun p : Fin (n+1)=>match targetOnly with
    | none => decide (p.val%3≠1)
    | some q => decide (p.val=q)
  let book:=ReplayMaps.prepare C.stateCount E.stateCount
  let prepared:=MaskedCluster.prepare C.stateCount E.stateCount
  let ci:=BoundaryApplication.Range.build C w
  let ei:=BoundaryApplication.Range.build E w
  let sources:=MaskedMutableProgression.Batch.prepare text 0 source prepared.K
  let catalog:=MaskedRunCatalog.ofBatch target sources
  let classes:=MaskedSuffixClass.prepare text 0
  let anchors:=Array.replicate (n+1) (some old)
  let mut st:=Mutable.Store.empty C E sources
  for first in leaders do
    st:=MaskedTraversalBankReady.write C E book prepared ci ei partition capacity first old anchors
      ⟨true,0,n+1⟩ catalog classes target st
  let template:=prepare C E height
  let mut tree:=(refreshMany st leaders (fresh template).1).1
  check ((fresh template).2==1) "frontier rebuilt identity template"
  let mut members:List (Nat×Nat):=[]
  for first in leaders do
    let some entry:=st.slots[first]?.join | throw (IO.userError "actual prepared bank missing")
    let d:=entry.config.descriptor
    members:=members++(List.range (d.repetitions+1)).map (fun k=>(d.first+k*d.period,first))
  let cut:=if storedCuts then none else some (Cut.build B C E w)
  let env:Clip.Env C E:=⟨book,prepared,ci,ei,target⟩
  let ask : BankTree C E height→Nat→Nat→Nat→Nat→BandResult := fun tree lo hi lengthLo lengthHi=>
    match cut with
    | some cut=>queryBand B C E cut tree lo hi base lengthLo lengthHi old
    | none=>
      let product:=region tree lo hi
      let bank:=close C E product.1
      let cuts:=MatrixTable.ofRel (MaskedCut.DFAIndex.jointEnum B C E) fun p s=>
        (List.range (lengthHi-lengthLo+1)).any fun offset=>
          let L:=lengthLo+offset
          decide (MaskedCut.DFAIndex.jointWord B C E (Spec.slice w base (base+L))=p ∧
            MaskedCut.DFAIndex.jointWord B C E (Spec.slice w (base+L) (base+old))=s)
      let out:=Cut.scanCells B C E bank.1 0 0 cuts
      BandResult.mk out.1 product.2 bank.2 0 0 out.2 3
  let mut live:=source
  let mut queries:=0
  let mut positive:=0
  let mut maximum:=0
  let mut clippedQueries:=0
  let ranges:=[(0,n+1),(0,0),(n+1,n+1)]++leaders.flatMap (fun p=>[(p,p+1),(0,p),(p,n+1)])
  for version in List.range (erases.length+1) do
    for bounds in ranges do
      for lengths in [(low,old),(old,old)] do
        let out:=ask tree bounds.1 bounds.2 lengths.1 lengths.2
        let expected:=reference B C E w members live target bounds.1 bounds.2 lengths.1 lengths.2
        check (out.answer==expected)
          s!"{label}: query mismatch version={version} bounds={bounds} lengths={lengths} actual={out.answer} expected={expected}"
        check (decide (out.cutProducts≤3 ∧ out.cutVisits≤3*(n.log2+2) ∧ out.arithmetic≤11)) "cut counters"
        queries:=queries+1
        if out.answer then positive:=positive+1
        maximum:=max maximum out.aggregateWork
    if let some shared:=cut then
      let windows:=[(0,n+1),(0,0),(n+1,n+1),(n+1,n+2),(1,n),(2,n-1)]++
        members.flatMap (fun p=>[(p.1,p.1+1),(p.1+1,n+1),(0,p.1)])
      for bounds in windows do
        let out:=queryWindow B C E shared env st partition capacity tree bounds.1 bounds.2 base low old old
        let expected:=reference B C E w members live target bounds.1 bounds.2 low old true
        check (out.band.answer==expected)
          s!"{label}: physical-window mismatch version={version} bounds={bounds} actual={out.band.answer} expected={expected}"
        check (decide (out.bankCalls≤2 ∧ out.queries≤1)) "window recompilation/query counters"
        clippedQueries:=clippedQueries+1
        queries:=queries+1
        if out.band.answer then positive:=positive+1
    if let some p:=erases[version]? then
      let owner:=MaskedClusterDescriptor.locate partition capacity p
      let oldTree:=tree
      let oldAnswer:=(ask oldTree 0 (n+1) low old).answer
      st:=Mutable.Store.eraseSource C E book prepared ci ei partition capacity target p st
      live:=live.setIfInBounds p false
      if let some first:=owner.1 then tree:=(refresh st first tree).1
      check ((ask oldTree 0 (n+1) low old).answer==oldAnswer) "persistent aggregate changed"
  -- Clear one actual slot, refresh once, then restore it from the retained
  -- store. Compare all answers with the unchanged complete aggregate.
  if let some first:=leaders.head? then
    let erased:={st with slots:=st.slots.setIfInBounds first none}
    let cleared:=(refresh erased first tree).1
    let restored:=(refresh st first cleared).1
    for bounds in ranges do
      check ((ask restored bounds.1 bounds.2 low old).answer==
        (ask tree bounds.1 bounds.2 low old).answer) "retired/restore aggregate mismatch"
  IO.println s!"aggregateFixture {label} n={n} classes={leaders.length} members={members.length} queries={queries} clippedQueries={clippedQueries} positive={positive} maxAggregate={maximum} fullCutIndex={!storedCuts} sourceOnlyErases=true"
  (←IO.getStdout).flush
  return (queries,positive)

def run : IO Unit := do
  let begin←IO.monoMsNow
  let points : Array (Fin 3):=#[0,1,2,0,1,2,0,1]
  let dense : Array (Fin 3):=#[0,1,0,1,0,1,0,1,2,2,0,1,0,1,0,1,2,2,0,1,0,1]
  let overlap : Array (Fin 3):=#[0,0,1,0,0,1,0,0,1,0]
  let inconsistent : Array (Fin 3):=#[0,1,2,0,1]
  let a←fixture "point-length-band" all all all points 2 1 0 none [0,3,8]
  let b←fixture "dense-and-point" all seen all dense 4 4 0 none [0,2,10]
  let c←fixture "overshoot" all all all overlap 4 4 0 none [0,3]
  let d←fixture "stored-common-length-rejection" odd all eps inconsistent 2 1 0 (some 3) [] true
  check (d.2==0 && a.2>0 && b.2>0 && c.2>0) "required positive/common-cut branches absent"
  let finish←IO.monoMsNow
  IO.println s!"aggregateComplete queries={a.1+b.1+c.1+d.1} positive={a.2+b.2+c.2+d.2} mismatches=0 elapsed={finish-begin}ms"
  IO.println "Independent references enumerate ordered copies in different actual clusters, including source windows cutting inside dense clusters. The J=16 correlation test scans actual-word stored tuples; the complete shared-index path is tested with smaller universes. Global geometry-repair coherence remains separate."

end REWB.MaskedTraversalAggregate.Audit

def main (args : List String) : IO Unit := do
  if args.contains "--points" then
    let _←REWB.MaskedTraversalAggregate.Audit.fixture "point-length-band"
      REWB.MaskedTraversalAggregate.Audit.all REWB.MaskedTraversalAggregate.Audit.all
      REWB.MaskedTraversalAggregate.Audit.all #[0,1,2,0,1,2,0,1] 2 1 0 none [0,3,8]
  else REWB.MaskedTraversalAggregate.Audit.run
