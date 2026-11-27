import REWB.MaskedClusterMutableStoreCost
import REWB.MaskedRunCatalogDiscovery

/-! Automatic current-bank preparation from actual descriptor, anchor,
neighbor and shared run-catalog reads. No run ID, target prefix array,
incoming cursor, or bank table is supplied by an answer oracle.

The caller owns one global slot/anchor array and passes the already built
shared indexes. This does not allocate an n-cell store for each leaf.
Reset keys must have their anchors written before this preparation pass;
successor-only context refreshes retain their existing anchors.

Correct maintenance of the complete active frontier and proof that every
changed descriptor/cursor was marked remain separate obligations.
-/
namespace REWB.MaskedTraversalBankReady
open REWB.MaskedCluster REWB.MaskedFiniteAction
variable {α : Type} {h h' n : Nat}

def readAnchor (anchors : Array (Option Nat)) (first current : Nat) : Nat :=
  (anchors[first]?).join.getD current

def resetAnchor (anchors : Array (Option Nat)) (first current : Nat) : Array (Option Nat) :=
  anchors.setIfInBounds first (some current)

theorem resetAnchor_read (anchors : Array (Option Nat)) (first current : Nat)
    (hb : first<anchors.size) : readAnchor (resetAnchor anchors first current) first current=current := by
  simp only [readAnchor,resetAnchor,Array.getElem?_setIfInBounds_self_of_lt hb]
  rfl

structure Incoming where
  cursor : Nat
  enabled : Bool
  work : Nat
  deriving Repr

/-- The previous cluster's actual last occurrence and retained anchor
determine the incoming overshoot. Missing metadata defaults to a reset at
the current length; correctness of retained anchors is a separate invariant. -/
def incoming (partition : MaskedClusterLeaders.State h) (capacity first current : Nat)
    (anchors : Array (Option Nat)) : Incoming :=
  let previous:=MaskedOrdered.Tree.pred partition.leaders capacity first
  match previous.1 with
  | none => ⟨first,false,previous.2+2⟩
  | some p =>
    let described:=MaskedClusterDescriptor.describeLeader partition capacity p
    match described.1 with
    | none => ⟨first,false,previous.2+described.2+4⟩
    | some d =>
      let cursor:=d.last+readAnchor anchors p current
      ⟨cursor,decide (first<cursor),previous.2+described.2+10⟩

theorem incoming_work (partition : MaskedClusterLeaders.State h) (capacity first current : Nat)
    (anchors : Array (Option Nat)) : (incoming partition capacity first current anchors).work≤46*h+52 := by
  have hp:=MaskedOrdered.Tree.pred_work partition.leaders capacity first
  simp only [incoming]
  cases he : (MaskedOrdered.Tree.pred partition.leaders capacity first).1 with
  | none => simp only [he]; omega
  | some p =>
    have hd:=MaskedClusterDescriptor.describeLeader_work partition capacity p
    simp only [he]
    cases hd' : (MaskedClusterDescriptor.describeLeader partition capacity p).1 <;>
      simp only [hd'] <;> omega

def prepare (partition : MaskedClusterLeaders.State h) (capacity first current : Nat)
    (anchors : Array (Option Nat)) (window : SourceWindow)
    (catalog : MaskedRunCatalog.Index) (classes : MaskedSuffixClass.Index n h') :
    Option Mutable.Store.Config×Nat :=
  let described:=MaskedClusterDescriptor.describeLeader partition capacity first
  match described.1 with
  | none => (none,described.2+2)
  | some d =>
    let entered:=incoming partition capacity first current anchors
    let found:=MaskedRunCatalog.descriptorShared catalog classes d current
    let id:=found.1.map MaskedRunCatalog.Found.id
    let counts:=(found.1.map (fun e=>e.value.counts)).getD #[]
    (some ⟨d,current,readAnchor anchors first current,entered.cursor,entered.enabled,window,id,counts⟩,
      described.2+entered.work+found.2+9)

theorem prepare_none (partition : MaskedClusterLeaders.State h) (capacity first current : Nat)
    (anchors : Array (Option Nat)) (window : SourceWindow)
    (catalog : MaskedRunCatalog.Index) (classes : MaskedSuffixClass.Index n h')
    (hd : (MaskedClusterDescriptor.describeLeader partition capacity first).1=none) :
    (prepare partition capacity first current anchors window catalog classes).1=none := by
  simp only [prepare,hd]

def compile (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (partition : MaskedClusterLeaders.State h) (capacity first current : Nat)
    (anchors : Array (Option Nat)) (window : SourceWindow)
    (catalog : MaskedRunCatalog.Index) (classes : MaskedSuffixClass.Index n h')
    (sources : Mutable.Batch.Sources) (target : Array Bool) :
    Option (Mutable.Store.Entry C E)×Nat :=
  let config:=prepare partition capacity first current anchors window catalog classes
  match config.1 with
  | none => (none,config.2+1)
  | some cfg =>
    let bank:=Mutable.Store.compile C E book prepared ci ei sources target cfg
    (bank.1.map (fun table=>⟨cfg,table⟩),config.2+bank.2+3)

/-- Invalid or retired leaders are cleared. A valid selected slot receives
the bank compiled from the current mutable source snapshot and catalog. -/
def write (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (partition : MaskedClusterLeaders.State h) (capacity first current : Nat)
    (anchors : Array (Option Nat)) (window : SourceWindow)
    (catalog : MaskedRunCatalog.Index) (classes : MaskedSuffixClass.Index n h')
    (target : Array Bool) (st : Mutable.Store.State C E) : Mutable.Store.State C E :=
  let out:=compile C E book prepared ci ei partition capacity first current anchors window catalog classes st.sources target
  {st with
    slots:=st.slots.setIfInBounds first out.1
    repairWork:=st.repairWork+out.2+5
    rebuilds:=st.rebuilds+1
    writes:=st.writes+1}

theorem write_selected (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (partition : MaskedClusterLeaders.State h) (capacity first current : Nat)
    (anchors : Array (Option Nat)) (window : SourceWindow)
    (catalog : MaskedRunCatalog.Index) (classes : MaskedSuffixClass.Index n h')
    (target : Array Bool) (st : Mutable.Store.State C E) (hb : first<st.slots.size) :
    (write C E book prepared ci ei partition capacity first current anchors window catalog classes target st).slots[first]?=
      some (compile C E book prepared ci ei partition capacity first current anchors window catalog classes st.sources target).1 :=
  Array.getElem?_setIfInBounds_self_of_lt hb

theorem write_other (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (partition : MaskedClusterLeaders.State h) (capacity first current other : Nat)
    (anchors : Array (Option Nat)) (window : SourceWindow)
    (catalog : MaskedRunCatalog.Index) (classes : MaskedSuffixClass.Index n h')
    (target : Array Bool) (st : Mutable.Store.State C E) (hne : first≠other) :
    (write C E book prepared ci ei partition capacity first current anchors window catalog classes target st).slots[other]?=
      st.slots[other]? := Array.getElem?_setIfInBounds_ne hne

theorem write_sources (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (partition : MaskedClusterLeaders.State h) (capacity first current : Nat)
    (anchors : Array (Option Nat)) (window : SourceWindow)
    (catalog : MaskedRunCatalog.Index) (classes : MaskedSuffixClass.Index n h')
    (target : Array Bool) (st : Mutable.Store.State C E) :
    (write C E book prepared ci ei partition capacity first current anchors window catalog classes target st).sources=st.sources := rfl

end REWB.MaskedTraversalBankReady
