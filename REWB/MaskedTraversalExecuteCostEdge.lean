import REWB.MaskedTraversalExecuteCostBand
import REWB.MaskedTraversalExecuteEdge

/-! Telescoping the real band loop and the born-due initial drain. All
intermediate validity is obtained from the proved actual band operation;
no cost callback or preassigned per-step budget is assumed. -/
namespace REWB.MaskedTraversalExecute.Cost
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedTraversalAggregate
variable {σ h : Nat} {B C E : DFA (Fin σ)}

theorem fresh_charged (template : Template C E h) (global : Global C E) (D R U : Nat) :
    actualWork (fresh template global).global+credit R U global+held D (fresh template global).frame=
      actualWork global+credit R U (fresh template global).global+2 := by
  simp only [actualWork,credit,held,fresh,MaskedTraversalDirty.empty,MaskedOrdered.State.empty,List.length_nil,Nat.mul_zero,Nat.add_zero]
  omega

theorem initial_charged (capacity : Nat) (step : MaskedTraversalDriver.Step h) (st : State C E h) (D R U : Nat) :
    actualWork (initial capacity step st).global+credit R U st.global+held D (initial capacity step st).frame≤
      actualWork st.global+credit R U (initial capacity step st).global+held D st.frame+
        markBudget h D*initialEvents step+4 := by
  cases he : step.lowered.edge.initial with
  | none=>
    simp only [initial,he,initialEvents,actualWork,credit,held,Nat.mul_zero,Nat.add_zero]
    omega
  | some crossed=>
    have hh:=crossing_charged step.before.state crossed capacity D st.frame.dirty
    simp only [initial,he,initialEvents,actualWork,credit,held]
    omega

theorem leaf_charged (capacity p : Nat) (inserted : MaskedTraversalFrontier.Inserted h) (st : State C E h) (D R U : Nat) :
    actualWork (leaf capacity p inserted st).global+credit R U st.global+held D (leaf capacity p inserted st).frame≤
      actualWork st.global+credit R U (leaf capacity p inserted st).global+held D st.frame+markBudget h D := by
  have hh:=change_charged (MaskedClusterLeaders.empty h).leaders inserted.frontier.state.leaders capacity p D st.frame.dirty
  simp only [leaf,actualWork,credit,held]
  unfold markBudget at hh ⊢
  omega

theorem merge_charged (capacity : Nat) (merged : MaskedTraversalFrontier.Merged h)
    (left right : Frame C E h) (global : Global C E) (D R U : Nat) :
    actualWork (merge capacity merged left right global).global+credit R U global+
      held D (merge capacity merged left right global).frame≤
    actualWork global+credit R U (merge capacity merged left right global).global+
      held D left+held D right+markBudget h D*merged.revPatches.length+4 := by
  cases hk : merged.keptLeft
  · have hh:=patches_charged capacity D merged.revPatches right.dirty
    simp only [merge,hk,Bool.false_eq_true,if_false,actualWork,credit,held]
    omega
  · have hh:=patches_charged capacity D merged.revPatches left.dirty
    simp only [merge,hk,if_true,actualWork,credit,held]
    omega

theorem walk_charged (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool)
    (env : Env B C E text.size (MaskedSuffixClass.height text.size)) (hs : Static text fallback source env)
    (capacity floor high : Nat) (hc : capacity=2^h) (s : MaskedClusterLeaders.State h) (st : State C E h)
    (hv : st.Valid text fallback source env s capacity high)
    (metadata : ∀b,b∈(MaskedTraversalEdge.walk capacity floor high s).bands→
      MaskedTraversalPositiveCoverage.Metadata text fallback capacity b) :
    let bs:=(MaskedTraversalEdge.walk capacity floor high s).bands
    let out:=bands env capacity bs st
    let D:=MaskedTraversalRepairCoherence.repairBudget C E env.repair.shared.prepared.K text.size h
    let R:=MaskedMutableProgression.Batch.rowBudget text.size
    let U:=outputBudget B C E env.repair.shared.prepared.K h text.size
    actualWork out.global+credit R U st.global+held D out.frame≤
      actualWork st.global+credit R U out.global+held D st.frame+
        markBudget h D*bandEvents bs+bandBudget B C E env.repair.shared.prepared.K h text.size*bs.length+1 := by
  induction high using Nat.strongRecOn generalizing s st with
  | ind high ih=>
    by_cases strict : floor<high
    · let boundary:=MaskedTraversalEdge.next floor high s
      let crossed:=MaskedClusterLeaders.shorten capacity boundary.length s
      let b : MaskedTraversalEdge.Band h:=⟨boundary.length+1,high,s,crossed⟩
      have below : boundary.length<high:=MaskedTraversalEdge.next_lt floor high s strict
      have walkEq : MaskedTraversalEdge.walk capacity floor high s=
          ⟨(MaskedTraversalEdge.walk capacity floor boundary.length crossed.state).state,
            b::(MaskedTraversalEdge.walk capacity floor boundary.length crossed.state).bands,
            crossed.popped+(MaskedTraversalEdge.walk capacity floor boundary.length crossed.state).popped,
            boundary.work+crossed.work+(MaskedTraversalEdge.walk capacity floor boundary.length crossed.state).work+8⟩ := by
        rw [MaskedTraversalEdge.walk,dif_pos strict]
      have thisMeta:=metadata b (by rw [walkEq]; exact List.mem_cons_self)
      have thisValid:=band_valid text fallback source env hs capacity hc b st hv thisMeta
      have thisCost:=band_charged text fallback source env hs capacity hc b st hv thisMeta
      have tail:=ih boundary.length below crossed.state (band env capacity b st)
        (by simpa only [b,Nat.add_sub_cancel] using thisValid)
        (fun a ha=>metadata a (by rw [walkEq]; exact List.mem_cons_of_mem b ha))
      dsimp only at thisCost tail ⊢
      rw [walkEq]
      simp only [bands,bandEvents,List.length_cons,Nat.mul_add,Nat.mul_one]
      omega
    · rw [MaskedTraversalEdge.walk,dif_neg strict]
      simp only [bands,bandEvents,List.length_nil,Nat.mul_zero,Nat.add_zero,actualWork,credit,held]
      omega

theorem edge_charged (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool)
    (env : Env B C E text.size (MaskedSuffixClass.height text.size)) (hs : Static text fallback source env)
    (capacity floor high : Nat) (hc : capacity=2^h) (before : MaskedTraversalFrontier.Frontier h) (st : State C E h)
    (hbefore : before.Valid high) (hv : st.Valid text fallback source env before.state capacity high)
    (metadata : ∀b,b∈(MaskedTraversalFrontier.lower capacity floor high before).edge.path.bands→
      MaskedTraversalPositiveCoverage.Metadata text fallback capacity b) :
    let step : MaskedTraversalDriver.Step h:=⟨floor,high,before,MaskedTraversalFrontier.lower capacity floor high before⟩
    let out:=edge env capacity step st
    let D:=MaskedTraversalRepairCoherence.repairBudget C E env.repair.shared.prepared.K text.size h
    let R:=MaskedMutableProgression.Batch.rowBudget text.size
    let U:=outputBudget B C E env.repair.shared.prepared.K h text.size
    actualWork out.global+credit R U st.global+held D out.frame≤
      actualWork st.global+credit R U out.global+held D st.frame+markBudget h D*stepEvents step+
        bandBudget B C E env.repair.shared.prepared.K h text.size*step.lowered.edge.path.bands.length+5 := by
  let step : MaskedTraversalDriver.Step h:=⟨floor,high,before,MaskedTraversalFrontier.lower capacity floor high before⟩
  let D:=MaskedTraversalRepairCoherence.repairBudget C E env.repair.shared.prepared.K text.size h
  let R:=MaskedMutableProgression.Batch.rowBudget text.size
  let U:=outputBudget B C E env.repair.shared.prepared.K h text.size
  have start:=initial_charged capacity step st D R U
  by_cases strict : floor<high
  · let first:=MaskedClusterLeaders.shorten capacity high before.state
    have initEq : step.lowered.edge.initial=some first := by
      simp only [step,MaskedTraversalFrontier.lower,MaskedTraversalEdge.run,if_pos strict]
      rfl
    have initValid:=initial_crossing_valid text fallback source env capacity hc step st hbefore initEq hv
    have tail:=walk_charged text fallback source env hs capacity floor high hc first.state (initial capacity step st) initValid (by
      intro b hb
      apply metadata b
      simpa only [MaskedTraversalFrontier.lower,MaskedTraversalEdge.run,if_pos strict] using hb)
    have outputEq : edge env capacity step st=bands env capacity (MaskedTraversalEdge.walk capacity floor high first.state).bands (initial capacity step st) := by
      simp only [edge,step,MaskedTraversalFrontier.lower,MaskedTraversalEdge.run,if_pos strict]
      rfl
    have bandsEq : step.lowered.edge.path.bands=(MaskedTraversalEdge.walk capacity floor high first.state).bands := by
      simp only [step,MaskedTraversalFrontier.lower,MaskedTraversalEdge.run,if_pos strict]
      rfl
    change actualWork (edge env capacity step st).global+credit R U st.global+held D (edge env capacity step st).frame≤_
    rw [outputEq]
    change _≤actualWork st.global+credit R U _+held D st.frame+
      markBudget h D*stepEvents step+bandBudget B C E env.repair.shared.prepared.K h text.size*step.lowered.edge.path.bands.length+5
    rw [stepEvents,bandsEq,Nat.mul_add]
    dsimp only at tail
    dsimp only [D,R,U] at start ⊢
    omega
  · simp only [step,edge,initial,MaskedTraversalFrontier.lower,MaskedTraversalEdge.run,if_neg strict,bands,
      stepEvents,initialEvents,bandEvents,List.length_nil,Nat.mul_zero,Nat.add_zero,actualWork,credit,held]
    omega

end REWB.MaskedTraversalExecute.Cost
