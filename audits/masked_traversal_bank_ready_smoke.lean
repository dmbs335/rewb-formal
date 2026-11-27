import REWB.MaskedTraversalBankReadyRegression

/-! Runtime references below enumerate actual words, masks and states only
for validation. The tested preparation uses the shared suffix/rank index,
the explicit-ID run catalog, predecessor descriptors and direct slot writes;
it receives no discovered run IDs or externally selected target arrays. -/
namespace REWB.MaskedTraversalBankReady.Audit
open REWB.MaskedCluster REWB.MaskedFiniteAction

def C : DFA (Fin 3) := ⟨2,0,fun q x=>if x.val=1 then 1 else q,fun q=>q==1⟩
def E : DFA (Fin 3) := ⟨2,0,fun _ x=>if x.val=1 then 1 else 0,fun q=>q==1⟩

def direct (w : Word (Fin 3)) (cfg : Mutable.Store.Config)
    (im om : Bool) (source target : Array Bool) (gate : Bool)
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

def physical (w : Word (Fin 3)) (entry : Mutable.Store.Entry C E)
    (source target : Array Bool) : IO Nat := do
  let mut cells:=0
  let replay:=ReplayMaps.encode (ReplayMaps.one C.stateCount E.stateCount)
  let states:=List.ofFn (fun i : Fin (MaskedClusterStage.dfa C E).stateCount=>i)
  for gate in [false,true] do
    for im in [false,true] do
      for om in [false,true] do
        for i in states do
          for j in states do
            let got:=entry.bank.view (code _ gate replay) (code _ im i) (code _ om j)
            let expected:=direct w entry.config im om source target gate
              (MaskedClusterStage.decode C E i) (MaskedClusterStage.decode C E j)
            unless got=expected do
              throw (IO.userError s!"physical leader={entry.config.descriptor.first}, modes={im}/{om}, gate={gate}, states={i.val}/{j.val}, got={got}, expected={expected}")
            cells:=cells+1
  return cells

def sameBank (a b : Mutable.Store.Bank C E) : IO Nat := do
  let mut cells:=0
  for key in List.ofFn (fun i : Fin (2*ReplayMaps.count C.stateCount E.stateCount)=>i) do
    for i in List.ofFn (fun i : Fin (2*(MaskedClusterStage.dfa C E).stateCount)=>i) do
      for j in List.ofFn (fun i : Fin (2*(MaskedClusterStage.dfa C E).stateCount)=>i) do
        unless a.view key i j=b.view key i j do
          throw (IO.userError s!"whole-bank mismatch at {key.val}/{i.val}/{j.val}")
        cells:=cells+1
  return cells

structure Stats where
  preparations : Nat := 0
  physicalCells : Nat := 0
  replayCells : Nat := 0
  incomingEnabled : Nat := 0
  dense : Nat := 0
  singleton : Nat := 0
  cleared : Nat := 0
  erases : Nat := 0
  work : Nat := 0
  deriving Repr

def fixture (label : String) (text : Array (Fin 3)) (L base : Nat)
    (erases : Array Nat) (clipped : Bool) : IO Stats := do
  let w:=text.toList
  let occurrences:=(List.range (text.size+1)).filter fun p=>
    decide (p+L≤text.size ∧ Spec.slice w p (p+L)=Spec.slice w base (base+L))
  let height:=(text.size+1).log2+1
  let capacity:=2^height
  let partition:=(MaskedClusterLeaders.execute height L
    (occurrences.reverse.map MaskedClusterLeaders.Operation.insert)).state
  let leaders:=partition.leaders.entries
  unless !leaders.isEmpty do throw (IO.userError s!"{label}: empty test class")
  let source:=Array.ofFn (fun i : Fin (text.size+1)=>decide (i.val%5!=3))
  let target:=Array.ofFn (fun i : Fin (text.size+1)=>decide (i.val%3=0 ∨ i.val%7=4))
  let prepared:=REWB.MaskedCluster.prepare C.stateCount E.stateCount
  let book:=ReplayMaps.prepare C.stateCount E.stateCount
  let ci:=BoundaryApplication.Range.build C w
  let ei:=BoundaryApplication.Range.build E w
  let sources:=MaskedMutableProgression.Batch.prepare text 0 source prepared.K
  let catalog:=MaskedRunCatalog.ofBatch target sources
  let classes:=MaskedSuffixClass.prepare text 0
  let anchors:=Array.replicate (text.size+1) (some L)
  let mut st:=Mutable.Store.empty C E sources
  let mut stats:Stats:={}
  for first in leaders do
    let window:=if clipped then SourceWindow.mk true first (first+1)
      else SourceWindow.mk true 0 (text.size+1)
    let old:=st
    st:=write C E book prepared ci ei partition capacity first L anchors window catalog classes target st
    unless st.rebuilds=old.rebuilds+1 && st.writes=old.writes+1 && st.slots.size=old.slots.size do
      throw (IO.userError s!"{label}: write counters/size changed")
    unless (st.slots[first]?.join).isSome do throw (IO.userError s!"{label}: automatic initial preparation missing")
  let mut live:=source
  for version in List.range (erases.size+1) do
    for first in leaders do
      let some entry:=st.slots[first]?.join | throw (IO.userError s!"{label}: leader slot missing")
      let cfg:=entry.config
      let out:=compile C E book prepared ci ei partition capacity first L anchors cfg.window catalog classes st.sources target
      let some fresh:=out.1 | throw (IO.userError s!"{label}: automatic compile rejected current snapshot")
      unless out.2≤85*height+52*MaskedRunCatalog.width text.size+137+
          Mutable.Store.bankLimit C E prepared.K text.size do
        throw (IO.userError s!"{label}: automatic compiler exceeded proved bound")
      unless cfg.descriptor.first=first && cfg.length=L && cfg.anchor=L do
        throw (IO.userError s!"{label}: selected descriptor or reset anchor changed")
      let previousLast:=(occurrences.filter (·<first)).getLast?
      let expectedCursor:=match previousLast with | none=>first | some p=>p+L
      let expectedEnabled:=previousLast.isSome && decide (first<expectedCursor)
      unless cfg.incoming=expectedCursor && cfg.incomingEnabled=expectedEnabled do
        throw (IO.userError s!"{label}: actual predecessor cursor mismatch at {first}")
      if cfg.incomingEnabled then stats:={stats with incomingEnabled:=stats.incomingEnabled+1}
      if cfg.descriptor.repetitions=0 then
        unless cfg.runId.isNone && cfg.targetCounts.isEmpty do
          throw (IO.userError s!"{label}: singleton performed a run lookup")
        stats:={stats with singleton:=stats.singleton+1}
      else
        let some id:=cfg.runId | throw (IO.userError s!"{label}: dense run ID missing")
        let some R:=st.sources.runs[id]? | throw (IO.userError s!"{label}: dense run array ID invalid")
        unless R.period=cfg.descriptor.period && R.lo≤first && cfg.descriptor.last+L≤R.hi do
          throw (IO.userError s!"{label}: discovered run does not contain complete cluster")
        unless cfg.targetCounts=(MaskedProgression.build target R.lo (MaskedPeriodic.Batch.span R)
            (prepared.K*R.period)).counts do
          throw (IO.userError s!"{label}: target counts not the catalog's immutable row")
        stats:={stats with dense:=stats.dense+1}
      stats:={stats with preparations:=stats.preparations+1,work:=stats.work+out.2}
      stats:={stats with physicalCells:=stats.physicalCells+(←physical w fresh live target)}
      stats:={stats with replayCells:=stats.replayCells+(←sameBank entry.bank fresh.bank)}
    if let some p:=erases[version]? then
      st:=Mutable.Store.eraseSource C E book prepared ci ei partition capacity target p st
      live:=live.setIfInBounds p false
      stats:={stats with erases:=stats.erases+1}
  -- Direct replacement must clear a retired key and leave every other key
  -- unchanged; populate the chosen invalid slot deliberately for this check.
  let invalid:=(List.range (text.size+1)).find? (fun p=>!leaders.contains p)
  if let some p:=invalid then
    let first:=leaders.head!
    let some oldEntry:=st.slots[first]?.join | throw (IO.userError "reference leader missing")
    st:={st with slots:=st.slots.setIfInBounds p (some oldEntry)}
    let old:=st
    st:=write C E book prepared ci ei partition capacity p L anchors ⟨true,0,text.size+1⟩ catalog classes target st
    unless (st.slots[p]?.join).isNone do throw (IO.userError s!"{label}: retired leader was not cleared")
    for other in leaders do
      let some a:=old.slots[other]?.join | throw (IO.userError "unrelated old slot missing")
      let some b:=st.slots[other]?.join | throw (IO.userError "unrelated new slot missing")
      stats:={stats with replayCells:=stats.replayCells+(←sameBank a.bank b.bank)}
    stats:={stats with cleared:=stats.cleared+1}
  IO.println s!"{label}: occurrences={occurrences}, leaders={leaders}, catalog runs={sources.runs.size}, {repr stats}"
  return stats

def run : IO Unit := do
  let begin ←IO.monoMsNow
  let mixed : Array (Fin 3):=#[0,1,0,1,0,1,0,1,2,2,0,1,0,1,0,1,2,2,0,1,0,1]
  let overlap : Array (Fin 3):=#[0,0,1,0,0,1,0,0,1,0]
  let unary : Array (Fin 3):=#[0,0,0,0,0,0,0,0]
  let a ←fixture "mixed dense/singleton, full source window" mixed 4 0 #[1,0,11,12,2,4,10,18,22,18,100] false
  let b ←fixture "mixed dense/singleton, one-source clipping" mixed 4 0 #[0,4,10,12,18,100] true
  let c ←fixture "positive incoming overshoot" overlap 4 0 #[0,3,6,6,100] false
  let d ←fixture "unary dense endpoint" unary 2 0 #[0,1,3,5,6,8,100] true
  unless a.dense>0 && a.singleton>0 && c.incomingEnabled>0 && d.dense>0 do
    throw (IO.userError "audit branches were not exercised")
  let stats:=[a,b,c,d]
  let finish ←IO.monoMsNow
  IO.println s!"auto bank preparation: fixtures=4, preparations={(stats.map (·.preparations)).sum}, physical cells={(stats.map (·.physicalCells)).sum}, replay cells={(stats.map (·.replayCells)).sum}, erase requests={(stats.map (·.erases)).sum}, retired clears={(stats.map (·.cleared)).sum}, mismatches=0, elapsed={finish-begin} ms"
  IO.println "Actual catalog IDs, current erased-source rows, predecessor-derived incoming cursors and immutable target counts were used throughout. Global dirty-neighborhood completeness and lazy aggregate/frontier coherence remain separate."

end REWB.MaskedTraversalBankReady.Audit

def main : IO Unit := REWB.MaskedTraversalBankReady.Audit.run

#print axioms REWB.MaskedTraversalBankReady.prepare_dense_reset
#print axioms REWB.MaskedTraversalBankReady.compile_reset_present
#print axioms REWB.MaskedTraversalBankReady.anchorBounds_reset
#print axioms REWB.MaskedTraversalBankReady.previous_next
#print axioms REWB.MaskedTraversalBankReady.incoming_bound
#print axioms REWB.MaskedTraversalBankReady.prepare_reset_geometry
#print axioms REWB.MaskedTraversalBankReady.prepare_work
#print axioms REWB.MaskedTraversalBankReady.compile_reset_work
#print axioms REWB.MaskedTraversalBankReady.compile_reset_current
#print axioms REWB.MaskedTraversalBankReady.write_selected
#print axioms REWB.MaskedTraversalBankReady.write_other
#print axioms REWB.MaskedTraversalBankReady.write_sources
