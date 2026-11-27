import REWB.MaskedClusterMutableErase
import REWB.MaskedClusterDescriptorAnchor

/-! A concrete bank store for one fixed occurrence-class partition.
    Slots are keyed by physical leader position, so locating a dirty bank
    uses the actual occurrence/leader predecessor index and one indexed
    slot read. Each slot contains a materialized bank and fixed geometry.

    Dense configuration refers to an actual run ID; its period and window
    coverage are checked against the immutable run descriptor array. The
    discovery of a suitable run ID is an initialization obligation, not
    an affected-bank oracle. Immutable target counts are prepared once.

    The work model counts unit indexed array reads/writes, as elsewhere in
    the batch. The store is intended to be consumed with owned array
    updates; retaining an old whole-array snapshot can incur runtime
    copy-on-write costs outside that abstract model. Source-tree updates
    and their fanout counters remain in `sources.updateWork`.
-/
namespace REWB.MaskedCluster.Mutable.Store
open REWB.MaskedFiniteAction REWB.RunGeometry
variable {α : Type} {h : Nat}

abbrev Bank (C E : DFA α) := Table (2*ReplayMaps.count C.stateCount E.stateCount)
  (2*(MaskedClusterStage.dfa C E).stateCount)

structure Config where
  descriptor : MaskedClusterDescriptor.Descriptor
  length : Nat
  anchor : Nat
  incoming : Nat
  incomingEnabled : Bool
  window : SourceWindow
  runId : Option Nat
  targetCounts : Array Nat
  deriving Repr

def compile (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (sources : Batch.Sources) (target : Array Bool) (cfg : Config) : Option (Bank C E)×Nat :=
  let d:=cfg.descriptor
  if d.repetitions=0 then
    let out:=Batch.compileSingleton C E book ci ei sources d.first cfg.length cfg.anchor
      (d.nextAt sources.n) cfg.incoming cfg.incomingEnabled target cfg.window
    (some out.1,out.2+1)
  else
    match cfg.runId with
    | none => (none,2)
    | some id =>
      match sources.runs[id]? with
      | none => (none,4)
      | some R =>
        if R.period=d.period ∧ R.lo≤d.first ∧ d.last+cfg.anchor≤R.hi+1 then
          let out:=Batch.compileRun C E book prepared ci ei sources id d.first d.repetitions
            cfg.length cfg.anchor (d.nextAt sources.n) cfg.incoming cfg.incomingEnabled target cfg.targetCounts cfg.window
          (out.1,out.2+9)
        else (none,8)

theorem compile_erase (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (source : Array Bool) (removed : List Nat) (sources : Batch.Sources)
    (hv : MaskedMutableProgression.Batch.Valid source removed sources)
    (target : Array Bool) (cfg : Config) (p : Nat)
    (hp : Batch.Candidates cfg.descriptor.first cfg.descriptor.period cfg.descriptor.repetitions p→cfg.window.allows p=false) :
    (compile C E book prepared ci ei (MaskedMutableProgression.Batch.eraseSource p sources) target cfg).1=
      (compile C E book prepared ci ei sources target cfg).1 := by
  unfold compile
  by_cases hm : cfg.descriptor.repetitions=0
  · simp only [hm,if_true,MaskedMutableProgression.Batch.eraseSource_n]
    exact congrArg Option.some (Batch.compileSingleton_erase C E book ci ei source removed sources hv
      cfg.descriptor.first cfg.length cfg.anchor (cfg.descriptor.nextAt sources.n) cfg.incoming cfg.incomingEnabled target cfg.window p
      (fun he=>hp ⟨0,by omega,by simpa only [Nat.zero_mul,Nat.add_zero] using he⟩))
  · simp only [hm,if_false]
    cases hid : cfg.runId with
    | none => rfl
    | some id =>
      simp only [MaskedMutableProgression.Batch.eraseSource_runs,MaskedMutableProgression.Batch.eraseSource_n]
      cases hR : sources.runs[id]? with
      | none => rfl
      | some R =>
        simp only
        by_cases hc : R.period=cfg.descriptor.period ∧ R.lo≤cfg.descriptor.first ∧ cfg.descriptor.last+cfg.anchor≤R.hi+1
        · simp only [hc,if_true]
          apply Batch.compileRun_erase C E book prepared ci ei source removed sources hv id R hR
          intro hh
          apply hp
          simpa only [hc.1] using hh
        · simp only [hc,if_false]

structure Entry (C E : DFA α) where
  config : Config
  bank : Bank C E

structure State (C E : DFA α) where
  sources : Batch.Sources
  slots : Array (Option (Entry C E))
  repairWork : Nat := 0
  rebuilds : Nat := 0
  writes : Nat := 0

def empty (C E : DFA α) (sources : Batch.Sources) : State C E :=
  ⟨sources,Array.replicate (sources.n+1) none,sources.n+1,0,0⟩

def rebuild (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (target : Array Bool) (first : Nat) (st : State C E) : State C E :=
  match st.slots[first]? with
  | some (some entry) =>
    let out:=compile C E book prepared ci ei st.sources target entry.config
    {st with
      slots:=st.slots.setIfInBounds first (out.1.map fun bank=>⟨entry.config,bank⟩)
      repairWork:=st.repairWork+out.2+8
      rebuilds:=st.rebuilds+1
      writes:=st.writes+1}
  | _ => {st with repairWork:=st.repairWork+3}

def eraseSource (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (partition : MaskedClusterLeaders.State h) (capacity : Nat) (target : Array Bool) (p : Nat)
    (st : State C E) : State C E :=
  let owner:=MaskedClusterDescriptor.locate partition capacity p
  let next:={st with
    sources:=MaskedMutableProgression.Batch.eraseSource p st.sources
    repairWork:=st.repairWork+owner.2+2}
  match owner.1 with
  | none => next
  | some first => rebuild C E book prepared ci ei target first next

/-- Installation queries the actual descriptor. It does not accept a
    caller-supplied descriptor or bank. Failure leaves the slot empty. -/
def install (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (partition : MaskedClusterLeaders.State h) (capacity first L H incoming : Nat) (enabled : Bool)
    (window : SourceWindow) (runId : Option Nat) (target : Array Bool) (targetCounts : Array Nat)
    (st : State C E) : State C E :=
  let described:=MaskedClusterDescriptor.describeLeader partition capacity first
  match described.1 with
  | none => {st with repairWork:=st.repairWork+described.2+2}
  | some d =>
    let cfg:Config:=⟨d,L,H,incoming,enabled,window,runId,targetCounts⟩
    let out:=compile C E book prepared ci ei st.sources target cfg
    {st with
      slots:=st.slots.setIfInBounds first (out.1.map fun bank=>⟨cfg,bank⟩)
      repairWork:=st.repairWork+described.2+out.2+8
      rebuilds:=st.rebuilds+1,writes:=st.writes+1}

def Coherent (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (partition : MaskedClusterLeaders.State h) (capacity : Nat) (target : Array Bool)
    (st : State C E) : Prop :=
  ∀(first : Nat) (entry : Entry C E),st.slots[first]?=some (some entry)→
    (MaskedClusterDescriptor.describeLeader partition capacity first).1=some entry.config.descriptor ∧
      (compile C E book prepared ci ei st.sources target entry.config).1=some entry.bank

def Complete (C E : DFA α) (partition : MaskedClusterLeaders.State h) (st : State C E) : Prop :=
  ∀first,first∈partition.leaders.entries→∃entry,st.slots[first]?=some (some entry)

theorem rebuild_sources (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (target : Array Bool) (first : Nat) (st : State C E) :
    (rebuild C E book prepared ci ei target first st).sources=st.sources := by
  unfold rebuild
  split <;> rfl

theorem eraseSource_sources (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (partition : MaskedClusterLeaders.State h) (capacity : Nat) (target : Array Bool) (p : Nat)
    (st : State C E) :
    (eraseSource C E book prepared ci ei partition capacity target p st).sources=
      MaskedMutableProgression.Batch.eraseSource p st.sources := by
  cases he : (MaskedClusterDescriptor.locate partition capacity p).1 <;>
    simp only [eraseSource,he,rebuild_sources]

theorem rebuild_other (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (target : Array Bool) (first other : Nat) (st : State C E) (hne : first≠other) :
    (rebuild C E book prepared ci ei target first st).slots[other]?=st.slots[other]? := by
  unfold rebuild
  split
  · exact Array.getElem?_setIfInBounds_ne hne
  · rfl

theorem eraseSource_other (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (partition : MaskedClusterLeaders.State h) (capacity : Nat) (target : Array Bool) (p other : Nat)
    (st : State C E) (hne : (MaskedClusterDescriptor.locate partition capacity p).1≠some other) :
    (eraseSource C E book prepared ci ei partition capacity target p st).slots[other]?=st.slots[other]? := by
  cases he : (MaskedClusterDescriptor.locate partition capacity p).1 with
  | none => simp only [eraseSource,he]
  | some first =>
    simp only [eraseSource,he]
    apply rebuild_other C E book prepared ci ei target first other
    intro hh
    subst first
    exact hne he

end REWB.MaskedCluster.Mutable.Store
