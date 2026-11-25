import REWB.MaskedClusterMutableStoreRegression

/-! Actual complete occurrence class -> leader descriptors -> owned slots
    -> located source erase -> one-slot repair. The fixture has two dense
    components and one singleton. Deleted non-occurrences at 1 and 11 lie
    inside dense hulls and must update sources without rebuilding a bank.
    Reference masks and literal chronological scans are audit-only.
-/
namespace REWB.MaskedCluster.Mutable.Store.Audit
open REWB.MaskedFiniteAction

def C : DFA (Fin 3) := ⟨2,0,fun q x=>if x.val=1 then 1 else q,fun q=>q==1⟩
def E : DFA (Fin 3) := ⟨2,0,fun _ x=>if x.val=1 then 1 else 0,fun q=>q==1⟩

def direct (w : Word (Fin 3)) (cfg : Config) (im om : Bool) (source target : Array Bool) (gate : Bool)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount) : Bool :=
  if im && !cfg.incomingEnabled then false else
    let d:=cfg.descriptor
    let I:=if im then cfg.incoming else d.first
    let next:=d.nextAt w.length
    let O:=if om then d.first+d.repetitions*d.period+cfg.anchor else next
    let jump:=(List.range (d.repetitions+1)).any fun k=>
      let p:=d.first+k*d.period
      decide (I≤p) && (if om then decide (next<p+cfg.length) else decide (p+cfg.length≤next)) &&
        decide (MaskedClusterStage.direct C E w I p cfg.length O
          ((gate && cfg.window.enabled && decide (cfg.window.lo≤p ∧ p<cfg.window.hi)) && source[p]?.getD false)
          (target[p]?.getD false) input=some output)
    if om then jump else decide (MaskedClusterStage.read C E (Spec.slice w I next) input=output) || jump

def compareBanks (a b : Bank C E) (label : String) : IO Nat := do
  let mut cells:=0
  for key in List.ofFn (fun i : Fin (2*ReplayMaps.count C.stateCount E.stateCount)=>i) do
    for i in List.ofFn (fun i : Fin (2*(MaskedClusterStage.dfa C E).stateCount)=>i) do
      for j in List.ofFn (fun i : Fin (2*(MaskedClusterStage.dfa C E).stateCount)=>i) do
        unless a.view key i j=b.view key i j do
          throw (IO.userError s!"{label}: key={key.val}, states={i.val}/{j.val}")
        cells:=cells+1
  return cells

def physical (w : Word (Fin 3)) (entry : Entry C E) (source target : Array Bool) : IO Nat := do
  let mut cells:=0
  let pref:=ReplayMaps.encode (ReplayMaps.one C.stateCount E.stateCount)
  let states:=List.ofFn (fun i : Fin (MaskedClusterStage.dfa C E).stateCount=>i)
  for gate in [false,true] do
    for im in [false,true] do
      for om in [false,true] do
        for i in states do
          for j in states do
            let got:=entry.bank.view (code _ gate pref) (code _ im i) (code _ om j)
            let expected:=direct w entry.config im om source target gate
              (MaskedClusterStage.decode C E i) (MaskedClusterStage.decode C E j)
            unless got=expected do
              throw (IO.userError s!"physical leader={entry.config.descriptor.first}, modes={im}/{om}, source gate={gate}, states={i.val}/{j.val}, got={got}, expected={expected}")
            cells:=cells+1
  return cells

def run : IO Unit := do
  let begin ←IO.monoMsNow
  let text : Array (Fin 3):=#[0,1,0,1,0,1,0,1,2,2,0,1,0,1,0,1,2,2,0,1,0,1]
  let w:=text.toList
  let L:=4
  let occurrences:=(List.range (w.length+1)).filter fun p=>
    decide (p+L≤w.length ∧ Spec.slice w p (p+L)=Spec.slice w 0 L)
  unless occurrences=[0,2,4,10,12,18] do throw (IO.userError "fixture complete occurrence class changed")
  let partition:=(MaskedClusterLeaders.execute 5 L (occurrences.reverse.map MaskedClusterLeaders.Operation.insert)).state
  let capacity:=32
  let leaders:=partition.leaders.entries
  unless leaders=[0,10,18] do throw (IO.userError "actual leader partition changed")
  let source:=Array.ofFn (fun i : Fin 23=>decide (i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=4 ∨
    i.val=10 ∨ i.val=11 ∨ i.val=12 ∨ i.val=18 ∨ i.val=22))
  let target:=Array.ofFn (fun i : Fin 23=>decide (i.val=4 ∨ i.val=12 ∨ i.val=18))
  let prepared:=prepare C.stateCount E.stateCount
  let book:=ReplayMaps.prepare C.stateCount E.stateCount
  let ci:=BoundaryApplication.Range.build C w
  let ei:=BoundaryApplication.Range.build E w
  let sources:=MaskedMutableProgression.Batch.prepare text 0 source prepared.K
  let mut st:=empty C E sources
  let mut targetPreps:=0
  for first in leaders do
    let some d:=(MaskedClusterDescriptor.describeLeader partition capacity first).1 |
      throw (IO.userError "actual descriptor was missing")
    let mut runId:Option Nat:=none
    let mut counts:Array Nat:=#[]
    if d.repetitions>0 then
      for id in List.range sources.runs.size do
        if let some R:=sources.runs[id]? then
          if R.period=d.period && R.lo≤d.first && d.last+L≤R.hi+1 && runId.isNone then
            runId:=some id
            counts:=(MaskedProgression.build target R.lo (MaskedPeriodic.Batch.span R) (prepared.K*R.period)).counts
            targetPreps:=targetPreps+1
      unless runId.isSome do throw (IO.userError "actual cubic enumeration supplied no containing run")
    let window:=if first=0 then SourceWindow.mk true 0 3 else
      if first=10 then SourceWindow.mk true 10 11 else SourceWindow.mk true 18 19
    st:=install C E book prepared ci ei partition capacity first L L 0 false window runId target counts st
    unless (st.slots[first]?.join).isSome do throw (IO.userError "actual install failed")
  let initialRebuilds:=st.rebuilds
  let initialWrites:=st.writes
  let initialWork:=st.repairWork
  let erases:=#[1,0,11,12,2,4,10,18,22,18,100]
  let mut live:=source
  let mut allMapCells:=0
  let mut physicalCells:=0
  let mut untouchedCells:=0
  let mut memberChecks:=0
  let mut noOwner:=0
  for version in List.range (erases.size+1) do
    for p in List.range 25 do
      unless (MaskedMutableProgression.member st.sources.singleton p).1=live[p]?.getD false do
        throw (IO.userError s!"global source snapshot at {p}")
      memberChecks:=memberChecks+1
    for first in leaders do
      let some entry:=st.slots[first]?.join | throw (IO.userError "complete store lost a leader")
      let fresh:=compile C E book prepared ci ei st.sources target entry.config
      let some freshBank:=fresh.1 | throw (IO.userError "fresh compiler rejected installed configuration")
      unless fresh.2≤bankLimit C E prepared.K w.length do throw (IO.userError "concrete bank limit exceeded")
      allMapCells:=allMapCells+(←compareBanks entry.bank freshBank s!"cached snapshot={version}, leader={first}")
      physicalCells:=physicalCells+(←physical w entry live target)
    if let some p:=erases[version]? then
      let old:=st
      let owner:=MaskedClusterDescriptor.locate partition capacity p
      let refOwner:=if occurrences.contains p then (leaders.filter (·≤p)).getLast? else none
      unless owner.1=refOwner do throw (IO.userError "actual dirty-bank locator disagrees")
      if owner.1.isNone then noOwner:=noOwner+1
      let expectedRebuilds:=if owner.1.isSome then 1 else 0
      let selectedWork:=selectedBankWork C E book prepared ci ei partition capacity target p st
      st:=eraseSource C E book prepared ci ei partition capacity target p st
      live:=live.setIfInBounds p false
      unless st.rebuilds=old.rebuilds+expectedRebuilds && st.writes=old.writes+expectedRebuilds &&
          st.slots.size=old.slots.size do throw (IO.userError "erase rebuilt or wrote more than the located slot")
      unless st.repairWork≤old.repairWork+(11*5+19)+selectedWork do
        throw (IO.userError "located repair work exceeded")
      for first in leaders do
        if owner.1!=some first then
          let some a:=old.slots[first]?.join | throw (IO.userError "old slot missing")
          let some b:=st.slots[first]?.join | throw (IO.userError "unrelated slot missing")
          untouchedCells:=untouchedCells+(←compareBanks a.bank b.bank s!"unrelated leader={first}, erased={p}")
  unless target[4]?.getD false && target[12]?.getD false && target[18]?.getD false do
    throw (IO.userError "target source dual use was changed")
  let finish ←IO.monoMsNow
  IO.println s!"owned fixed-partition repair: occurrences={occurrences.length}, leaders={leaders.length}, actual cubic runs={sources.runs.size}, target preparations={targetPreps}, erase requests={erases.size}, no-owner requests={noOwner}, bank repairs={st.rebuilds-initialRebuilds}, slot writes={st.writes-initialWrites}, mismatches=0, elapsed={finish-begin} ms"
  IO.println s!"stored/fresh replay cells={allMapCells}, chronological physical cells={physicalCells}, untouched-slot cells={untouchedCells}, current member checks={memberChecks}, tracked repair work={st.repairWork-initialWork}, actual source fanout deliveries={st.sources.delivered}"
  IO.println "Non-occurrences inside dense hulls were erased with zero bank repairs. Targets and complete occurrence/leader trees stayed fixed. Run-ID discovery and global traversal/frontier maintenance remain separate."

end REWB.MaskedCluster.Mutable.Store.Audit

def main : IO Unit := REWB.MaskedCluster.Mutable.Store.Audit.run

#print axioms REWB.MaskedCluster.Mutable.compileDenseBank_same
#print axioms REWB.MaskedCluster.Mutable.compilePointBank_same
#print axioms REWB.MaskedCluster.Mutable.Batch.compileRun_erase
#print axioms REWB.MaskedCluster.Mutable.Store.compile_presence_erase
#print axioms REWB.MaskedCluster.Mutable.Store.eraseSource_other
#print axioms REWB.MaskedCluster.Mutable.Store.eraseSource_coherent
#print axioms REWB.MaskedCluster.Mutable.Store.eraseSource_complete
#print axioms REWB.MaskedCluster.Mutable.Store.install_coherent
#print axioms REWB.MaskedCluster.Mutable.Store.eraseSource_counts
#print axioms REWB.MaskedCluster.Mutable.Store.compile_work
#print axioms REWB.MaskedCluster.Mutable.Store.eraseSource_combined_work
#print axioms REWB.MaskedCluster.Mutable.Store.describe_reset_geometry
#print axioms REWB.MaskedCluster.Mutable.Store.eraseSource_geometry
#print axioms REWB.MaskedCluster.Mutable.Store.Regression.inside_dense_hulls
#print axioms REWB.MaskedCluster.Mutable.Store.Regression.nonoccurrence_no_bank_repair
#print axioms REWB.MaskedCluster.Mutable.Store.Regression.other_cluster_shared
