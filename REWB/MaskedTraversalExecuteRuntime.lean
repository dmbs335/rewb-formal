import REWB.MaskedTraversalExecute

/-! Kernel-equal execution entry points with explicit ownership of the
collected transaction. Destructuring the returned band and answer state
prevents projection unfolding from emitting a second Reporting.run call.
The recursive wrappers ensure that a newly compiled public solve enters
this path even when the original Execute module already has compiled IR.
All values and recorded counters are equal to the original definitions.
-/
namespace REWB.MaskedTraversalExecute.Runtime
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedTraversalAggregate
variable {α : Type} {B C E : DFA α} {h n h' : Nat}

def band (env : Env B C E n h') (capacity : Nat) (b : MaskedTraversalEdge.Band h)
    (st : State C E h) : State C E h :=
  let oldStats:=st.global.stats
  let oldAnswerWork:=st.global.answers.work
  let repaired:=MaskedTraversalRepairCoherence.apply env.repair b.snapshot capacity b.hi
    st.global.anchors st.frame.dirty st.global.store st.frame.tree
  let base:=representative b
  let ⟨collected,answers⟩:=Collect.run B C E env.cut env.repair.shared repaired.store b.snapshot capacity
    repaired.tree base b.lo b.hi b.hi st.global.answers
  let ⟨reported,afterReport⟩:=collected
  let replayed:=replay C E env.repair.shared.cRanges env.repair.shared.eRanges base (b.lo-1) b.hi
  let shortened:=MaskedTraversalAggregate.shorten (bankAction replayed.maps) afterReport.tree
  let dirty:=MaskedTraversalDirty.crossing b.snapshot b.crossing capacity (MaskedTraversalDirty.empty h)
  let work:=oldStats.work+repaired.work+reported.queryWork+reported.copies+20*reported.calls+afterReport.work+
    (answers.work-oldAnswerWork)+replayed.work+shortened.2+dirty.work+24
  ⟨⟨repaired.anchors,afterReport.store,answers,
      ⟨work,oldStats.bands+1,oldStats.queryCalls+reported.calls,
        oldStats.reported+reported.count,oldStats.actionBuilds+1⟩⟩,
    ⟨shortened.1,dirty⟩⟩

@[csimp] theorem band_eq_runtime : @MaskedTraversalExecute.band=@band := by
  rfl

def bands (env : Env B C E n h') (capacity : Nat) :
    List (MaskedTraversalEdge.Band h)→State C E h→State C E h
  | [],st=>⟨{st.global with stats:={st.global.stats with work:=st.global.stats.work+1}},st.frame⟩
  | b::bs,st=>bands env capacity bs (band env capacity b st)

theorem bands_value (env : Env B C E n h') (capacity : Nat)
    (bs : List (MaskedTraversalEdge.Band h)) (st : State C E h) :
    bands env capacity bs st=MaskedTraversalExecute.bands env capacity bs st := by
  induction bs generalizing st with
  | nil=>rfl
  | cons b bs ih=>
    rw [bands,MaskedTraversalExecute.bands,ih]
    rfl

@[csimp] theorem bands_eq_runtime : @MaskedTraversalExecute.bands=@bands := by
  funext α B C E n h' h env capacity bs st
  exact (bands_value env capacity bs st).symm

def edge (env : Env B C E n h') (capacity : Nat) (step : MaskedTraversalDriver.Step h)
    (st : State C E h) : State C E h :=
  bands env capacity step.lowered.edge.path.bands (initial capacity step st)

theorem edge_value (env : Env B C E n h') (capacity : Nat) (step : MaskedTraversalDriver.Step h)
    (st : State C E h) : edge env capacity step st=MaskedTraversalExecute.edge env capacity step st :=
  bands_value env capacity _ _

@[csimp] theorem edge_eq_runtime : @MaskedTraversalExecute.edge=@edge := by
  funext α B C E n h' h env capacity step st
  exact (edge_value env capacity step st).symm

def plan (env : Env B C E n h') (capacity : Nat) (template : Template C E h) :
    MaskedTraversalDriver.Plan h→Global C E→State C E h
  | .empty step,global=>edge env capacity step (fresh template global)
  | .leaf p inserted step,global=>edge env capacity step (leaf capacity p inserted (fresh template global))
  | .node left right merged step,global=>
    let ⟨afterLeft,leftFrame⟩:=plan env capacity template left global
    let ⟨afterRight,rightFrame⟩:=plan env capacity template right afterLeft
    edge env capacity step (merge capacity merged leftFrame rightFrame afterRight)

theorem plan_value (env : Env B C E n h') (capacity : Nat) (template : Template C E h)
    (p : MaskedTraversalDriver.Plan h) (global : Global C E) :
    plan env capacity template p global=MaskedTraversalExecute.plan env capacity template p global := by
  induction p generalizing global with
  | empty step=>exact edge_value _ _ _ _
  | leaf p inserted step=>exact edge_value _ _ _ _
  | node left right merged step ihl ihr=>
    simp only [plan,MaskedTraversalExecute.plan,ihl,ihr,edge_value]

@[csimp] theorem plan_eq_runtime : @MaskedTraversalExecute.plan=@plan := by
  funext α B C E n h' h env capacity template p global
  exact (plan_value env capacity template p global).symm

end REWB.MaskedTraversalExecute.Runtime
