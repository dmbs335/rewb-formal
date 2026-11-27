import REWB.MaskedTraversalRepairTransportShortenRegression
import REWB.MaskedTraversalAggregateCollect
import REWB.MaskedTraversalDriverCoverage

/-! The actual bank/source executor for a retained geometric Driver plan.

The plan supplies actual insertions, selected heavy merges and queue
crossings. A positive band first repairs its accumulated primary keys and
their current successor contexts, then calls the concrete shared-cut
reporter, erases exactly its outputs, and only then applies the common
word replay and collects the lower crossing. Equal-depth refinements and
the final parent floor perform no bank reset or query.

One identity aggregate is prepared and shared. The two child executions
consume the same global store in sequence; only their persistent tree and
pending keys are saved. No old whole-store/anchor snapshot is retained by
this executable. The proof-only entry lists are absent from these types.

The local scalar/table/range counters are accumulated below. Source
fanout remains in store.sources.updateWork. Actual fixed-pattern action
construction is separately counted by actionBuilds, just as the compiler
keeps its finite formula construction separate. No global asymptotic
bank-repair bound is asserted in this module.
-/
namespace REWB.MaskedTraversalExecute
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedTraversalAggregate
variable {α : Type} {B C E : DFA α} {h n h' : Nat}

structure Env (B C E : DFA α) (n h' : Nat) where
  repair : MaskedTraversalRepairCoherence.Env C E n h'
  cut : Cut.Shared B C E

structure Stats where
  work : Nat := 0
  bands : Nat := 0
  queryCalls : Nat := 0
  reported : Nat := 0
  actionBuilds : Nat := 0
  deriving Repr

structure Global (C E : DFA α) where
  anchors : Array (Option Nat)
  store : Mutable.Store.State C E
  answers : MaskedTraversalAnswers.State
  stats : Stats

structure Frame (C E : DFA α) (h : Nat) where
  tree : BankTree C E h
  dirty : MaskedTraversalDirty.Marked h

structure State (C E : DFA α) (h : Nat) where
  global : Global C E
  frame : Frame C E h

def representative (b : MaskedTraversalEdge.Band h) : Nat :=
  b.snapshot.occurrences.first.getD 0

def fresh (template : Template C E h) (global : Global C E) : State C E h :=
  ⟨{global with stats:={global.stats with work:=global.stats.work+2}},
    ⟨template.blank,MaskedTraversalDirty.empty h⟩⟩

/-- A born-due drain only accumulates actual changed neighborhoods. -/
def initial (capacity : Nat) (step : MaskedTraversalDriver.Step h) (st : State C E h) : State C E h :=
  match step.lowered.edge.initial with
  | none => ⟨{st.global with stats:={st.global.stats with work:=st.global.stats.work+1}},st.frame⟩
  | some crossed =>
    let prior:=st.frame.dirty.work
    let dirty:=MaskedTraversalDirty.crossing step.before.state crossed capacity st.frame.dirty
    ⟨{st.global with stats:={st.global.stats with work:=st.global.stats.work+(dirty.work-prior)+3}},
      ⟨st.frame.tree,dirty⟩⟩

def band (env : Env B C E n h') (capacity : Nat) (b : MaskedTraversalEdge.Band h)
    (st : State C E h) : State C E h :=
  let oldStats:=st.global.stats
  let oldAnswerWork:=st.global.answers.work
  let repaired:=MaskedTraversalRepairCoherence.apply env.repair b.snapshot capacity b.hi
    st.global.anchors st.frame.dirty st.global.store st.frame.tree
  let base:=representative b
  let collected:=Collect.run B C E env.cut env.repair.shared repaired.store b.snapshot capacity
    repaired.tree base b.lo b.hi b.hi st.global.answers
  let replayed:=replay C E env.repair.shared.cRanges env.repair.shared.eRanges base (b.lo-1) b.hi
  let shortened:=MaskedTraversalAggregate.shorten (bankAction replayed.maps) collected.band.repaired.tree
  let dirty:=MaskedTraversalDirty.crossing b.snapshot b.crossing capacity (MaskedTraversalDirty.empty h)
  let work:=oldStats.work+repaired.work+collected.band.reported.queryWork+
    collected.band.reported.copies+20*collected.band.reported.calls+collected.band.repaired.work+
    (collected.answers.work-oldAnswerWork)+replayed.work+shortened.2+dirty.work+24
  ⟨⟨repaired.anchors,collected.band.repaired.store,collected.answers,
      ⟨work,oldStats.bands+1,oldStats.queryCalls+collected.band.reported.calls,
        oldStats.reported+collected.band.reported.count,oldStats.actionBuilds+1⟩⟩,
    ⟨shortened.1,dirty⟩⟩

/-- Tail recursion consumes each retained band exactly once. -/
def bands (env : Env B C E n h') (capacity : Nat) :
    List (MaskedTraversalEdge.Band h) → State C E h → State C E h
  | [],st => ⟨{st.global with stats:={st.global.stats with work:=st.global.stats.work+1}},st.frame⟩
  | b::bs,st => bands env capacity bs (band env capacity b st)

def edge (env : Env B C E n h') (capacity : Nat) (step : MaskedTraversalDriver.Step h)
    (st : State C E h) : State C E h :=
  bands env capacity step.lowered.edge.path.bands (initial capacity step st)

def leaf (capacity p : Nat) (inserted : MaskedTraversalFrontier.Inserted h)
    (st : State C E h) : State C E h :=
  let prior:=st.frame.dirty.work
  let dirty:=MaskedTraversalDirty.markChange (MaskedClusterLeaders.empty h).leaders
    inserted.frontier.state.leaders capacity p st.frame.dirty
  ⟨{st.global with stats:={st.global.stats with work:=st.global.stats.work+(dirty.work-prior)+3}},
    ⟨st.frame.tree,dirty⟩⟩

/-- The light bank tree is discarded. Every imported light position is
already in the actual merge patch log, so its needed cells enter the
selected heavy tree through the subsequent sparse repair. -/
def merge (capacity : Nat) (merged : MaskedTraversalFrontier.Merged h)
    (left right : Frame C E h) (global : Global C E) : State C E h :=
  let kept:=if merged.keptLeft then left else right
  let prior:=kept.dirty.work
  let dirty:=MaskedTraversalDirty.patches capacity merged.revPatches kept.dirty
  ⟨{global with stats:={global.stats with work:=global.stats.work+(dirty.work-prior)+3}},
    ⟨kept.tree,dirty⟩⟩

/-- Destructuring child results before continuing avoids retaining an
old complete global store merely to recover its saved tree later. -/
def plan (env : Env B C E n h') (capacity : Nat) (template : Template C E h) :
    MaskedTraversalDriver.Plan h → Global C E → State C E h
  | .empty step,global => edge env capacity step (fresh template global)
  | .leaf p inserted step,global => edge env capacity step (leaf capacity p inserted (fresh template global))
  | .node left right merged step,global =>
    let ⟨afterLeft,leftFrame⟩:=plan env capacity template left global
    let ⟨afterRight,rightFrame⟩:=plan env capacity template right afterLeft
    edge env capacity step (merge capacity merged leftFrame rightFrame afterRight)

theorem band_count (env : Env B C E n h') (capacity : Nat) (b : MaskedTraversalEdge.Band h)
    (st : State C E h) : (band env capacity b st).global.stats.bands=st.global.stats.bands+1 := rfl

theorem band_actions (env : Env B C E n h') (capacity : Nat) (b : MaskedTraversalEdge.Band h)
    (st : State C E h) : (band env capacity b st).global.stats.actionBuilds=st.global.stats.actionBuilds+1 := rfl

theorem bands_count (env : Env B C E n h') (capacity : Nat) (bs : List (MaskedTraversalEdge.Band h))
    (st : State C E h) : (bands env capacity bs st).global.stats.bands=st.global.stats.bands+bs.length := by
  induction bs generalizing st with
  | nil => simp only [bands,List.length_nil,Nat.add_zero]
  | cons b bs ih =>
    rw [bands,ih,band_count,List.length_cons]
    omega

theorem bands_actions (env : Env B C E n h') (capacity : Nat) (bs : List (MaskedTraversalEdge.Band h))
    (st : State C E h) : (bands env capacity bs st).global.stats.actionBuilds=st.global.stats.actionBuilds+bs.length := by
  induction bs generalizing st with
  | nil => simp only [bands,List.length_nil,Nat.add_zero]
  | cons b bs ih =>
    rw [bands,ih,band_actions,List.length_cons]
    omega

theorem edge_equal (env : Env B C E n h') (capacity length : Nat)
    (before : MaskedTraversalFrontier.Frontier h) (st : State C E h) :
    let step : MaskedTraversalDriver.Step h:=⟨length,length,before,MaskedTraversalFrontier.lower capacity length length before⟩
    (edge env capacity step st).frame=st.frame ∧
      (edge env capacity step st).global.anchors=st.global.anchors ∧
      (edge env capacity step st).global.store=st.global.store ∧
      (edge env capacity step st).global.answers=st.global.answers ∧
      (edge env capacity step st).global.stats.bands=st.global.stats.bands := by
  simp only [edge,initial,MaskedTraversalFrontier.lower,MaskedTraversalEdge.run_equal,bands]
  trivial

end REWB.MaskedTraversalExecute
