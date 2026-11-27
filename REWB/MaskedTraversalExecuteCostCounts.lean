import REWB.MaskedTraversalExecuteCostEvents

/-! Exact execution counts. Every scheduled band makes one common
finite-action construction, and the reported counter counts precisely
the new answer-list entries. These identities hold for the actual
executor without a semantic cost contract. -/
namespace REWB.MaskedTraversalExecute.Cost
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedTraversalAggregate
variable {α : Type} {B C E : DFA α} {h n h' : Nat}

structure Accounting (before after : Global C E) (count : Nat) : Prop where
  bands : after.stats.bands=before.stats.bands+count
  actions : after.stats.actionBuilds=before.stats.actionBuilds+count
  outputs : after.answers.count+before.stats.reported=before.answers.count+after.stats.reported

theorem Accounting.trans {a b c : Global C E} {i j : Nat}
    (left : Accounting a b i) (right : Accounting b c j) : Accounting a c (i+j) := by
  rcases left with ⟨hlb,hla,hlo⟩
  rcases right with ⟨hrb,hra,hro⟩
  constructor <;> omega

theorem fresh_accounting (template : Template C E h) (global : Global C E) :
    Accounting global (fresh template global).global 0 := ⟨rfl,rfl,rfl⟩

theorem initial_accounting (capacity : Nat) (step : MaskedTraversalDriver.Step h) (st : State C E h) :
    Accounting st.global (initial capacity step st).global 0 := by
  cases he : step.lowered.edge.initial <;> simp only [initial,he] <;> exact ⟨rfl,rfl,rfl⟩

theorem leaf_accounting (capacity p : Nat) (inserted : MaskedTraversalFrontier.Inserted h) (st : State C E h) :
    Accounting st.global (leaf capacity p inserted st).global 0 := ⟨rfl,rfl,rfl⟩

theorem merge_accounting (capacity : Nat) (merged : MaskedTraversalFrontier.Merged h)
    (left right : Frame C E h) (global : Global C E) :
    Accounting global (merge capacity merged left right global).global 0 := ⟨rfl,rfl,rfl⟩

theorem band_accounting (env : Env B C E n h') (capacity : Nat) (b : MaskedTraversalEdge.Band h) (st : State C E h) :
    Accounting st.global (band env capacity b st).global 1 := by
  let repaired:=MaskedTraversalRepairCoherence.apply env.repair b.snapshot capacity b.hi st.global.anchors st.frame.dirty st.global.store st.frame.tree
  let collected:=Collect.run B C E env.cut env.repair.shared repaired.store b.snapshot capacity repaired.tree
    (representative b) b.lo b.hi b.hi st.global.answers
  have counted : collected.band.reported.count=collected.band.reported.starts.length := MaskedReporting.report_count _ h 0
  have answers : collected.answers.count=st.global.answers.count+collected.band.reported.starts.length :=
    MaskedTraversalAnswers.push_count _ _
  refine ⟨rfl,rfl,?_⟩
  change collected.answers.count+st.global.stats.reported=
    st.global.answers.count+(st.global.stats.reported+collected.band.reported.count)
  omega

theorem bands_accounting (env : Env B C E n h') (capacity : Nat) (bs : List (MaskedTraversalEdge.Band h))
    (st : State C E h) : Accounting st.global (bands env capacity bs st).global bs.length := by
  induction bs generalizing st with
  | nil=>exact ⟨rfl,rfl,rfl⟩
  | cons b bs ih=>
    have ht:=(band_accounting env capacity b st).trans (ih (band env capacity b st))
    simpa only [bands,List.length_cons,Nat.add_comm 1] using ht

theorem edge_accounting (env : Env B C E n h') (capacity : Nat) (step : MaskedTraversalDriver.Step h)
    (st : State C E h) :
    Accounting st.global (edge env capacity step st).global step.lowered.edge.path.bands.length := by
  have ht:=(initial_accounting capacity step st).trans
    (bands_accounting env capacity step.lowered.edge.path.bands (initial capacity step st))
  simpa only [edge,Nat.zero_add] using ht

theorem plan_accounting (env : Env B C E n h') (capacity : Nat) (template : Template C E h)
    (p : MaskedTraversalDriver.Plan h) (global : Global C E) :
    Accounting global (plan env capacity template p global).global (scheduledBands p) := by
  induction p generalizing global with
  | empty step=>
    have ht:=(fresh_accounting template global).trans (edge_accounting env capacity step (fresh template global))
    simpa only [plan,scheduledBands,Nat.zero_add] using ht
  | leaf p inserted step=>
    have ht:=(fresh_accounting template global).trans
      ((leaf_accounting capacity p inserted (fresh template global)).trans
        (edge_accounting env capacity step (leaf capacity p inserted (fresh template global))))
    simpa only [plan,scheduledBands,Nat.zero_add] using ht
  | node left right merged step il ir=>
    cases hl : plan env capacity template left global with
    | mk leftGlobal leftFrame=>
      cases hr : plan env capacity template right leftGlobal with
      | mk rightGlobal rightFrame=>
        have leftCount:=il global
        rw [hl] at leftCount
        have rightCount:=ir leftGlobal
        rw [hr] at rightCount
        have ht:=leftCount.trans (rightCount.trans
          ((merge_accounting capacity merged leftFrame rightFrame rightGlobal).trans
            (edge_accounting env capacity step (merge capacity merged leftFrame rightFrame rightGlobal))))
        simpa only [plan,hl,hr,scheduledBands,Nat.zero_add,Nat.add_assoc] using ht

theorem plan_actions (env : Env B C E n h') (capacity : Nat) (template : Template C E h)
    (p : MaskedTraversalDriver.Plan h) (global : Global C E) :
    (plan env capacity template p global).global.stats.actionBuilds=global.stats.actionBuilds+scheduledBands p :=
  (plan_accounting env capacity template p global).actions

theorem plan_reported (env : Env B C E n h') (capacity : Nat) (template : Template C E h)
    (p : MaskedTraversalDriver.Plan h) (global : Global C E) :
    (plan env capacity template p global).global.stats.reported+global.answers.count=
      global.stats.reported+(plan env capacity template p global).global.answers.count := by
  have hh:=(plan_accounting env capacity template p global).outputs
  omega

end REWB.MaskedTraversalExecute.Cost
