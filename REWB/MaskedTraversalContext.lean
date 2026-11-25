import REWB.MaskedTraversalRepairCost

/-! Successor-only context refresh. Resetting a predecessor anchor can
change the next cluster's incoming cursor, while that next cluster keeps
its own H and stored run ID/immutable target counts. This pass never
recursively resets successor anchors.

The candidate keys are obtained by actual leader membership/successor
queries and sparse deduplication. The bank preparation checks that the
current descriptor equals the stored descriptor; structural changes
belong to the reset pass, and a failed check clears the slot explicitly.
It does not silently assert that dirty-set locality has already been proved.
-/
namespace REWB.MaskedTraversalContext
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedTraversalBankReady
variable {α : Type} {h : Nat}

def step (leaders : MaskedOrdered.Tree h) (capacity p : Nat)
    (out : MaskedTraversalDirty.Marked h) : MaskedTraversalDirty.Marked h :=
  let member:=MaskedOrdered.Tree.contains leaders capacity p
  if member.1 then
    let next:=MaskedOrdered.Tree.succ leaders capacity p
    match next.1 with
    | none => {out with work:=out.work+member.2+next.2+5}
    | some q =>
      let marked:=MaskedTraversalDirty.mark capacity q out
      {marked with work:=marked.work+member.2+next.2+7}
  else {out with work:=out.work+member.2+3}

def successors (leaders : MaskedOrdered.Tree h) (capacity : Nat) :
    List Nat→MaskedTraversalDirty.Marked h→MaskedTraversalDirty.Marked h
  | [],out => {out with work:=out.work+1}
  | p::ps,out => successors leaders capacity ps (step leaders capacity p out)

def config (partition : MaskedClusterLeaders.State h) (capacity first L : Nat)
    (anchors : Array (Option Nat)) (old : Mutable.Store.Config) : Mutable.Store.Config :=
  let entered:=incoming partition capacity first L anchors
  {old with
    length:=L,anchor:=readAnchor anchors first L,
    incoming:=entered.cursor,incomingEnabled:=entered.enabled}

def prepare (partition : MaskedClusterLeaders.State h) (capacity first L : Nat)
    (anchors : Array (Option Nat)) (old : Option (Mutable.Store.Entry C E)) :
    Option Mutable.Store.Config×Nat :=
  match old with
  | none => (none,2)
  | some entry =>
    let described:=MaskedClusterDescriptor.describeLeader partition capacity first
    match described.1 with
    | none => (none,described.2+4)
    | some d =>
      if d=entry.config.descriptor then
        let entered:=incoming partition capacity first L anchors
        (some (config partition capacity first L anchors entry.config),described.2+entered.work+26)
      else (none,described.2+20)

def compile (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (partition : MaskedClusterLeaders.State h) (capacity first L : Nat)
    (anchors : Array (Option Nat)) (target : Array Bool) (st : Mutable.Store.State C E) :
    Option (Mutable.Store.Entry C E)×Nat :=
  let cfg:=prepare partition capacity first L anchors (st.slots[first]?.join)
  match cfg.1 with
  | none => (none,cfg.2+3)
  | some cfg' =>
    let out:=Mutable.Store.compile C E book prepared ci ei st.sources target cfg'
    (out.1.map (fun bank=>⟨cfg',bank⟩),cfg.2+out.2+5)

def write (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (partition : MaskedClusterLeaders.State h) (capacity first L : Nat)
    (anchors : Array (Option Nat)) (target : Array Bool) (st : Mutable.Store.State C E) :
    Mutable.Store.State C E :=
  let out:=compile C E book prepared ci ei partition capacity first L anchors target st
  {st with
    slots:=st.slots.setIfInBounds first out.1
    repairWork:=st.repairWork+out.2+5
    rebuilds:=st.rebuilds+1
    writes:=st.writes+1}

def applyLoop (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (partition : MaskedClusterLeaders.State h) (capacity L : Nat)
    (anchors : Array (Option Nat)) (target : Array Bool) :
    List Nat→Mutable.Store.State C E→Mutable.Store.State C E
  | [],st => {st with repairWork:=st.repairWork+1}
  | p::ps,st =>
    let next:=write C E book prepared ci ei partition capacity p L anchors target st
    applyLoop C E book prepared ci ei partition capacity L anchors target ps
      {next with repairWork:=next.repairWork+3}

end REWB.MaskedTraversalContext
