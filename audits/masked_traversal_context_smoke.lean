import REWB.MaskedTraversalContextRegression

/-! Actual successor collection and retained-anchor bank refresh. Direct
list scans and literal word runs below are audit-only references. -/
namespace REWB.MaskedTraversalContext.Audit
open REWB.MaskedCluster REWB.MaskedFiniteAction

def metadata : IO Unit := do
  let begin ←IO.monoMsNow
  let anchors:=Array.ofFn (fun i : Fin 8=>some (10+i.val%3))
  let mut cases:=0
  let mut unchanged:=0
  let mut keys:=0
  for mask in List.range 64 do
    let positions:=(List.range 6).filter (fun p=>mask.testBit p)
    for L in [1,2,3,4,6] do
      let partition:=(MaskedClusterLeaders.execute 3 L
        (positions.reverse.map MaskedClusterLeaders.Operation.insert)).state
      let leaders:=partition.leaders.entries
      for resetMask in List.range 64 do
        let resets:=(List.range 6).filter (fun p=>resetMask.testBit p)
        let selected:=successors partition.leaders 8 resets (MaskedTraversalDirty.empty 3)
        let reference:=resets.flatMap fun p=>
          if leaders.contains p then (leaders.find? (fun q=>p<q)).toList else []
        unless selected.requests≤resets.length && selected.keys.positions.length≤resets.length &&
            selected.work≤1+(39*3+34)*resets.length+1 do
          throw (IO.userError "actual successor pass exceeded budget")
        unless selected.keys.positions.eraseDups.length=selected.keys.positions.length do
          throw (IO.userError "successor keys were not deduplicated")
        let updated:=(MaskedTraversalRepair.anchorsLoop L resets anchors 0).1
        for p in List.range 8 do
          unless selected.keys.positions.contains p=reference.contains p do
            throw (IO.userError "actual successor set differs from direct reference")
        for first in leaders do
          unless selected.keys.positions.contains first do
            let a:=MaskedTraversalBankReady.incoming partition 8 first L anchors
            let b:=MaskedTraversalBankReady.incoming partition 8 first L updated
            unless a.cursor=b.cursor && a.enabled=b.enabled do
              throw (IO.userError "anchor reset changed an unselected leader's incoming context")
            unchanged:=unchanged+1
        cases:=cases+1
        keys:=keys+selected.keys.positions.length
  let finish ←IO.monoMsNow
  IO.println s!"successor-only propagation: cases={cases}, actual dedup successor keys={keys}, unchanged incoming contexts={unchanged}, mismatches=0, elapsed={finish-begin} ms"

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

def sameBank (a b : Mutable.Store.Bank C E) : IO Nat := do
  let mut cells:=0
  for key in List.ofFn (fun i : Fin (2*ReplayMaps.count C.stateCount E.stateCount)=>i) do
    for i in List.ofFn (fun i : Fin (2*(MaskedClusterStage.dfa C E).stateCount)=>i) do
      for j in List.ofFn (fun i : Fin (2*(MaskedClusterStage.dfa C E).stateCount)=>i) do
        unless a.view key i j=b.view key i j do throw (IO.userError "unrelated raw bank changed during context refresh")
        cells:=cells+1
  return cells

def fixture (label : String) (text : Array (Fin 3)) (H L : Nat) (resets : List Nat) : IO Unit := do
  let n:=text.size
  let h:=(n+1).log2+1
  let capacity:=2^h
  let w:=text.toList
  let oldOccurrences:=(List.range (n+1)).filter fun p=>
    decide (p+H≤n ∧ Spec.slice w p (p+H)=Spec.slice w 0 H)
  let occurrences:=(List.range (n+1)).filter fun p=>
    decide (p+L≤n ∧ Spec.slice w p (p+L)=Spec.slice w 0 L)
  unless oldOccurrences=occurrences do throw (IO.userError "retained-context fixture changed occurrence class")
  let oldPartition:=(MaskedClusterLeaders.execute h H (oldOccurrences.map MaskedClusterLeaders.Operation.insert)).state
  let partition:=(MaskedClusterLeaders.execute h L (occurrences.map MaskedClusterLeaders.Operation.insert)).state
  unless oldPartition.leaders.entries=partition.leaders.entries do
    throw (IO.userError "retained-context fixture changed leader partition")
  let source:=Array.ofFn (fun i : Fin (n+1)=>decide (i.val%5!=2))
  let target:=Array.ofFn (fun i : Fin (n+1)=>decide (i.val%3=0 ∨ i.val%7=4))
  let live:=(source.setIfInBounds 0 false).setIfInBounds 7 false
  let prepared:=REWB.MaskedCluster.prepare C.stateCount E.stateCount
  let book:=ReplayMaps.prepare C.stateCount E.stateCount
  let sources:=MaskedMutableProgression.Batch.run text 0 source prepared.K [0,7,n+5]
  let catalog:=MaskedRunCatalog.ofBatch target sources
  let classes:=MaskedSuffixClass.prepare text 0
  let ci:=BoundaryApplication.Range.build C w
  let ei:=BoundaryApplication.Range.build E w
  let anchors:=Array.replicate (n+1) (some H)
  let mut st:=Mutable.Store.empty C E sources
  for first in oldPartition.leaders.entries do
    st:=MaskedTraversalBankReady.write C E book prepared ci ei oldPartition capacity first H anchors
      ⟨true,0,n+1⟩ catalog classes target st
    unless (st.slots[first]?.join).isSome do throw (IO.userError "initial reset bank missing")
  let resetKeys:=MaskedTraversalDirty.markList capacity resets (MaskedTraversalDirty.empty h)
  let middle:=MaskedTraversalRepair.reset C E book prepared ci ei partition capacity L anchors ⟨true,0,n+1⟩
    catalog classes target resetKeys st
  let contexts:=successors partition.leaders capacity resetKeys.keys.positions (MaskedTraversalDirty.empty h)
  let final:=applyLoop C E book prepared ci ei partition capacity L middle.anchors target contexts.keys.positions middle.store
  unless final.repairWork≤middle.store.repairWork+(85*h+130+Mutable.Store.bankLimit C E prepared.K n)*
      contexts.keys.positions.length+1 do throw (IO.userError "actual context loop exceeded budget")
  unless final.writes=middle.store.writes+contexts.keys.positions.length &&
      final.rebuilds=middle.store.rebuilds+contexts.keys.positions.length do
    throw (IO.userError "context write count differs from dedup successor count")
  let replay:=ReplayMaps.encode (ReplayMaps.one C.stateCount E.stateCount)
  let states:=List.ofFn (fun i : Fin (MaskedClusterStage.dfa C E).stateCount=>i)
  let mut physicalCells:=0
  let mut unchangedCells:=0
  let mut retainedDense:=0
  let mut retainedPoint:=0
  for first in partition.leaders.entries do
    let some a:=middle.store.slots[first]?.join | throw (IO.userError "middle bank missing")
    let some b:=final.slots[first]?.join | throw (IO.userError "context refresh erased a valid unchanged descriptor")
    if contexts.keys.positions.contains first then
      unless b.config.anchor=a.config.anchor && b.config.runId=a.config.runId &&
          b.config.targetCounts=a.config.targetCounts && b.config.window.enabled=a.config.window.enabled &&
          b.config.window.lo=a.config.window.lo && b.config.window.hi=a.config.window.hi && b.config.length=L do
        throw (IO.userError "context refresh changed retained anchor/run/count/window")
      if L<b.config.anchor then
        if b.config.descriptor.repetitions=0 then retainedPoint:=retainedPoint+1
        else retainedDense:=retainedDense+1
      for gate in [false,true] do
        for im in [false,true] do
          for om in [false,true] do
            for i in states do
              for j in states do
                let actual:=b.bank.view (code _ gate replay) (code _ im i) (code _ om j)
                let reference:=physical w b.config im om live target gate
                  (MaskedClusterStage.decode C E i) (MaskedClusterStage.decode C E j)
                unless actual=reference do
                  throw (IO.userError s!"retained H physical mismatch: {label}, first={first}, H={b.config.anchor}, L={L}, modes={im}/{om}, state={i.val}/{j.val}")
                physicalCells:=physicalCells+1
    else unchangedCells:=unchangedCells+(←sameBank a.bank b.bank)
  -- A stale structural descriptor is rejected by the actual guard.
  let first:=partition.leaders.entries.head!
  let some entry:=final.slots[first]?.join | throw (IO.userError "guard-test bank missing")
  let stale : Mutable.Store.Entry C E:={entry with
    config:={entry.config with descriptor:={entry.config.descriptor with last:=entry.config.descriptor.last+1}}}
  let corrupted:={final with slots:=final.slots.setIfInBounds first (some stale)}
  let cleared:=write C E book prepared ci ei partition capacity first L middle.anchors target corrupted
  unless (cleared.slots[first]?.join).isNone do throw (IO.userError "stale descriptor was silently accepted")
  IO.println s!"{label}: H={H}, L={L}, occurrences={occurrences}, leaders={partition.leaders.entries}, reset keys={resetKeys.keys.positions}, successor keys={contexts.keys.positions}, retained dense={retainedDense}, retained singleton={retainedPoint}, physical cells={physicalCells}, untouched replay cells={unchangedCells}, work={final.repairWork-middle.store.repairWork}, mismatches=0"

def run : IO Unit := do
  metadata
  let dense : Array (Fin 3):=#[0,0,1,0,0,1,0,0,0,1,0,0,1,0,0,1,0,0,2,2,2,2,0,0,1,0,0,1,0,0]
  let point : Array (Fin 3):=#[0,0,1,0,0,1,0,0,1,0,0]
  fixture "dense retained H, no cascade to next leader" dense 8 7 [0]
  fixture "singleton retained H, positive incoming" point 5 4 [0]
  fixture "adjacent simultaneous resets" point 5 4 [0,3]
  fixture "empty reset and refresh" point 5 5 []
  IO.println "All current-source physical checks passed. Own anchors and stored run IDs/counts were retained, and unrelated banks were unchanged. Structural dirty-set locality and whole traversal/aggregate coherence remain separate."

end REWB.MaskedTraversalContext.Audit

def main : IO Unit := REWB.MaskedTraversalContext.Audit.run

#print axioms REWB.MaskedTraversalContext.successors_spec
#print axioms REWB.MaskedTraversalContext.pred_next
#print axioms REWB.MaskedTraversalContext.incoming_unchanged
#print axioms REWB.MaskedTraversalContext.prepare_some
#print axioms REWB.MaskedTraversalContext.compile_selected
#print axioms REWB.MaskedTraversalContext.runBacked_context
#print axioms REWB.MaskedTraversalContext.retained_geometry
#print axioms REWB.MaskedTraversalContext.store_current
#print axioms REWB.MaskedTraversalContext.compile_current
#print axioms REWB.MaskedTraversalContext.write_ready
#print axioms REWB.MaskedTraversalContext.compile_work
#print axioms REWB.MaskedTraversalContext.applyLoop_work
