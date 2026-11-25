import REWB.MaskedAllStartFullCostExecuteBand

/-! Whole-plan cost-bearing execution. The unchanged geometric dirty-key
operations use their actual returned work increments. The band loop is
tail recursive with an owned state and scalar cost accumulator. Sequential
child execution retains only the two persistent frames. Every local full
construction charge telescopes against the existing actual executor work.
-/
namespace REWB.MaskedAllStart.FullCost.Execution
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedTraversalAggregate
open REWB.MaskedTraversalExecute
variable {α : Type} {B C E : DFA α} {h n h' : Nat}

theorem delta_credit (coefficient before after : Nat) (hc : 1≤coefficient) (hm : before≤after) :
    after-before+coefficient*before≤coefficient*after := by
  have hs:=Nat.mul_le_mul_right (after-before) hc
  have he:=congrArg (fun x=>coefficient*x) (Nat.sub_add_cancel hm)
  simp only [Nat.mul_add,Nat.one_mul] at hs he
  omega

def fresh (template : Template C E h) (global : Global C E) : Bank.Result (MaskedTraversalExecute.State C E h) :=
  (MaskedTraversalExecute.fresh template global,2)

theorem fresh_value (template : Template C E h) (global : Global C E) :
    (fresh template global).1=MaskedTraversalExecute.fresh template global := rfl

theorem fresh_credit (template : Template C E h) (global : Global C E) (F : Nat) (hf : 1≤F) :
    (fresh template global).2+F*global.stats.work≤F*(fresh template global).1.global.stats.work := by
  have hh:=Nat.mul_le_mul_right 2 hf
  simp only [fresh,MaskedTraversalExecute.fresh,Nat.mul_add]
  omega

def initial (capacity : Nat) (step : MaskedTraversalDriver.Step h) (st : MaskedTraversalExecute.State C E h) :
    Bank.Result (MaskedTraversalExecute.State C E h) :=
  let before:=st.global.stats.work
  let ⟨global,frame⟩:=MaskedTraversalExecute.initial capacity step st
  (⟨global,frame⟩,global.stats.work-before)

theorem initial_value (capacity : Nat) (step : MaskedTraversalDriver.Step h) (st : MaskedTraversalExecute.State C E h) :
    (initial capacity step st).1=MaskedTraversalExecute.initial capacity step st := rfl

theorem initial_credit (capacity : Nat) (step : MaskedTraversalDriver.Step h) (st : MaskedTraversalExecute.State C E h)
    (F : Nat) (hf : 1≤F) :
    (initial capacity step st).2+F*st.global.stats.work≤F*(initial capacity step st).1.global.stats.work := by
  apply delta_credit F _ _ hf
  unfold MaskedTraversalExecute.initial
  split <;> simp only <;> omega

def leaf (capacity p : Nat) (inserted : MaskedTraversalFrontier.Inserted h) (st : MaskedTraversalExecute.State C E h) :
    Bank.Result (MaskedTraversalExecute.State C E h) :=
  let before:=st.global.stats.work
  let ⟨global,frame⟩:=MaskedTraversalExecute.leaf capacity p inserted st
  (⟨global,frame⟩,global.stats.work-before)

theorem leaf_value (capacity p : Nat) (inserted : MaskedTraversalFrontier.Inserted h) (st : MaskedTraversalExecute.State C E h) :
    (leaf capacity p inserted st).1=MaskedTraversalExecute.leaf capacity p inserted st := rfl

theorem leaf_credit (capacity p : Nat) (inserted : MaskedTraversalFrontier.Inserted h) (st : MaskedTraversalExecute.State C E h)
    (F : Nat) (hf : 1≤F) :
    (leaf capacity p inserted st).2+F*st.global.stats.work≤F*(leaf capacity p inserted st).1.global.stats.work := by
  apply delta_credit F _ _ hf
  simp only [MaskedTraversalExecute.leaf]
  omega

def merge (capacity : Nat) (merged : MaskedTraversalFrontier.Merged h)
    (left right : Frame C E h) (global : Global C E) : Bank.Result (MaskedTraversalExecute.State C E h) :=
  let before:=global.stats.work
  let ⟨next,frame⟩:=MaskedTraversalExecute.merge capacity merged left right global
  (⟨next,frame⟩,next.stats.work-before)

theorem merge_value (capacity : Nat) (merged : MaskedTraversalFrontier.Merged h)
    (left right : Frame C E h) (global : Global C E) :
    (merge capacity merged left right global).1=MaskedTraversalExecute.merge capacity merged left right global := rfl

theorem merge_credit (capacity : Nat) (merged : MaskedTraversalFrontier.Merged h)
    (left right : Frame C E h) (global : Global C E) (F : Nat) (hf : 1≤F) :
    (merge capacity merged left right global).2+F*global.stats.work≤
      F*(merge capacity merged left right global).1.global.stats.work := by
  apply delta_credit F _ _ hf
  simp only [MaskedTraversalExecute.merge]
  omega

def bandsLoop (env : Env B C E n h') (capacity : Nat) :
    List (MaskedTraversalEdge.Band h)→MaskedTraversalExecute.State C E h→Nat→Bank.Result (MaskedTraversalExecute.State C E h)
  | [],st,total=>
    (⟨{st.global with stats:={st.global.stats with work:=st.global.stats.work+1}},st.frame⟩,total+1)
  | b::bs,st,total=>
    let ⟨next,work⟩:=band env capacity b st
    bandsLoop env capacity bs next (total+work)

theorem bandsLoop_value (env : Env B C E n h') (capacity : Nat) (bs : List (MaskedTraversalEdge.Band h))
    (st : MaskedTraversalExecute.State C E h) (total : Nat) :
    (bandsLoop env capacity bs st total).1=MaskedTraversalExecute.bands env capacity bs st := by
  induction bs generalizing st total with
  | nil=>rfl
  | cons b bs ih=>simp only [bandsLoop,MaskedTraversalExecute.bands,ih,band_value]

theorem bandsLoop_credit (env : Env B C E n h') (capacity : Nat) (bs : List (MaskedTraversalEdge.Band h))
    (st : MaskedTraversalExecute.State C E h) (total : Nat) (ht : PeriodicConstruction.Cut.Tiny env.cut.tree) :
    (bandsLoop env capacity bs st total).2+coefficient B C E env.repair.shared.prepared.K*st.global.stats.work≤
      total+coefficient B C E env.repair.shared.prepared.K*(bandsLoop env capacity bs st total).1.global.stats.work := by
  induction bs generalizing st total with
  | nil=>
    have hh:=coefficient_pos B C E env.repair.shared.prepared.K
    simp only [bandsLoop,Nat.mul_add,Nat.mul_one]
    omega
  | cons b bs ih=>
    have hb:=band_credit env capacity b st ht
    have hh:=ih (band env capacity b st).1 (total+(band env capacity b st).2)
    simp only [bandsLoop]
    omega

def bands (env : Env B C E n h') (capacity : Nat) (bs : List (MaskedTraversalEdge.Band h))
    (st : MaskedTraversalExecute.State C E h) : Bank.Result (MaskedTraversalExecute.State C E h) :=
  bandsLoop env capacity bs st 0

theorem bands_value (env : Env B C E n h') (capacity : Nat) (bs : List (MaskedTraversalEdge.Band h))
    (st : MaskedTraversalExecute.State C E h) :
    (bands env capacity bs st).1=MaskedTraversalExecute.bands env capacity bs st := bandsLoop_value _ _ _ _ _

theorem bands_credit (env : Env B C E n h') (capacity : Nat) (bs : List (MaskedTraversalEdge.Band h))
    (st : MaskedTraversalExecute.State C E h) (ht : PeriodicConstruction.Cut.Tiny env.cut.tree) :
    (bands env capacity bs st).2+coefficient B C E env.repair.shared.prepared.K*st.global.stats.work≤
      coefficient B C E env.repair.shared.prepared.K*(bands env capacity bs st).1.global.stats.work :=
  bandsLoop_credit _ _ _ _ 0 ht

def edge (env : Env B C E n h') (capacity : Nat) (step : MaskedTraversalDriver.Step h)
    (st : MaskedTraversalExecute.State C E h) : Bank.Result (MaskedTraversalExecute.State C E h) :=
  let ⟨started,startWork⟩:=initial capacity step st
  let ⟨done,bandWork⟩:=bands env capacity step.lowered.edge.path.bands started
  (done,startWork+bandWork)

theorem edge_value (env : Env B C E n h') (capacity : Nat) (step : MaskedTraversalDriver.Step h)
    (st : MaskedTraversalExecute.State C E h) :
    (edge env capacity step st).1=MaskedTraversalExecute.edge env capacity step st := by
  simp only [edge,MaskedTraversalExecute.edge,bands_value,initial_value]

theorem edge_credit (env : Env B C E n h') (capacity : Nat) (step : MaskedTraversalDriver.Step h)
    (st : MaskedTraversalExecute.State C E h) (ht : PeriodicConstruction.Cut.Tiny env.cut.tree) :
    (edge env capacity step st).2+coefficient B C E env.repair.shared.prepared.K*st.global.stats.work≤
      coefficient B C E env.repair.shared.prepared.K*(edge env capacity step st).1.global.stats.work := by
  have hi:=initial_credit capacity step st (coefficient B C E env.repair.shared.prepared.K)
    (coefficient_pos B C E env.repair.shared.prepared.K)
  have hb:=bands_credit env capacity step.lowered.edge.path.bands (initial capacity step st).1 ht
  simp only [edge]
  omega

def plan (env : Env B C E n h') (capacity : Nat) (template : Template C E h) :
    MaskedTraversalDriver.Plan h→Global C E→Bank.Result (MaskedTraversalExecute.State C E h)
  | .empty step,global=>
    let ⟨started,startWork⟩:=fresh template global
    let ⟨done,edgeWork⟩:=edge env capacity step started
    (done,startWork+edgeWork)
  | .leaf p inserted step,global=>
    let ⟨started,startWork⟩:=fresh template global
    let ⟨seeded,leafWork⟩:=leaf capacity p inserted started
    let ⟨done,edgeWork⟩:=edge env capacity step seeded
    (done,startWork+leafWork+edgeWork)
  | .node left right merged step,global=>
    let ⟨⟨afterLeft,leftFrame⟩,leftWork⟩:=plan env capacity template left global
    let ⟨⟨afterRight,rightFrame⟩,rightWork⟩:=plan env capacity template right afterLeft
    let ⟨combined,mergeWork⟩:=merge capacity merged leftFrame rightFrame afterRight
    let ⟨done,edgeWork⟩:=edge env capacity step combined
    (done,leftWork+rightWork+mergeWork+edgeWork)

theorem plan_value (env : Env B C E n h') (capacity : Nat) (template : Template C E h)
    (p : MaskedTraversalDriver.Plan h) (global : Global C E) :
    (plan env capacity template p global).1=MaskedTraversalExecute.plan env capacity template p global := by
  induction p generalizing global with
  | empty step=>simp only [plan,MaskedTraversalExecute.plan,edge_value,fresh_value]
  | leaf p inserted step=>simp only [plan,MaskedTraversalExecute.plan,edge_value,leaf_value,fresh_value]
  | node left right merged step ihl ihr=>simp only [plan,MaskedTraversalExecute.plan,edge_value,merge_value,ihl,ihr]

theorem plan_credit (env : Env B C E n h') (capacity : Nat) (template : Template C E h)
    (p : MaskedTraversalDriver.Plan h) (global : Global C E) (ht : PeriodicConstruction.Cut.Tiny env.cut.tree) :
    (plan env capacity template p global).2+coefficient B C E env.repair.shared.prepared.K*global.stats.work≤
      coefficient B C E env.repair.shared.prepared.K*(plan env capacity template p global).1.global.stats.work := by
  let F:=coefficient B C E env.repair.shared.prepared.K
  have hf : 1≤F:=coefficient_pos B C E env.repair.shared.prepared.K
  induction p generalizing global with
  | empty step=>
    have hstart:=fresh_credit template global F hf
    have hedge:=edge_credit env capacity step (fresh template global).1 ht
    change (fresh template global).2+(edge env capacity step (fresh template global).1).2+F*global.stats.work≤
      F*(edge env capacity step (fresh template global).1).1.global.stats.work
    change _+F*(fresh template global).1.global.stats.work≤F*_ at hedge
    omega
  | leaf p inserted step=>
    let started:=fresh template global
    let seeded:=leaf capacity p inserted started.1
    have hstart:=fresh_credit template global F hf
    have hseed:=leaf_credit capacity p inserted started.1 F hf
    have hedge:=edge_credit env capacity step seeded.1 ht
    change started.2+seeded.2+(edge env capacity step seeded.1).2+F*global.stats.work≤
      F*(edge env capacity step seeded.1).1.global.stats.work
    change started.2+F*global.stats.work≤F*started.1.global.stats.work at hstart
    change _+F*seeded.1.global.stats.work≤F*_ at hedge
    omega
  | node left right merged step ihl ihr=>
    let leftRun:=plan env capacity template left global
    let rightRun:=plan env capacity template right leftRun.1.global
    let combined:=merge capacity merged leftRun.1.frame rightRun.1.frame rightRun.1.global
    have hl:=ihl global
    have hr:=ihr leftRun.1.global
    have hm:=merge_credit capacity merged leftRun.1.frame rightRun.1.frame rightRun.1.global F hf
    have he:=edge_credit env capacity step combined.1 ht
    change leftRun.2+rightRun.2+combined.2+(edge env capacity step combined.1).2+F*global.stats.work≤
      F*(edge env capacity step combined.1).1.global.stats.work
    change leftRun.2+F*global.stats.work≤F*leftRun.1.global.stats.work at hl
    change rightRun.2+F*leftRun.1.global.stats.work≤F*rightRun.1.global.stats.work at hr
    change combined.2+F*rightRun.1.global.stats.work≤F*combined.1.global.stats.work at hm
    change _+F*combined.1.global.stats.work≤F*_ at he
    omega

theorem plan_work (env : Env B C E n h') (capacity : Nat) (template : Template C E h)
    (p : MaskedTraversalDriver.Plan h) (global : Global C E) (ht : PeriodicConstruction.Cut.Tiny env.cut.tree) :
    (plan env capacity template p global).2≤coefficient B C E env.repair.shared.prepared.K*
      (MaskedTraversalExecute.plan env capacity template p global).global.stats.work := by
  have hh:=plan_credit env capacity template p global ht
  rw [plan_value] at hh
  omega

end REWB.MaskedAllStart.FullCost.Execution
