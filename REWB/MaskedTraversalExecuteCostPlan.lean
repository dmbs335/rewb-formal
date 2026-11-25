import REWB.MaskedTraversalExecuteCostEdge
import REWB.MaskedTraversalExecuteCostCounts
import REWB.MaskedTraversalExecuteSuffix

/-! Global cost of the actual sequential child/child/heavy-merge/edge
execution. A light child's pending-key potential may be discarded, while
every retained key is paid by a preceding real neighborhood event. All
bank validity needed by the local bound is derived from the actual
executor preservation theorems. -/
namespace REWB.MaskedTraversalExecute.Cost
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedTraversalAggregate
open REWB.BoundaryTrie
open REWB.MaskedRunDiscovery (positions prepareSuffixes suffixKeys)
variable {σ h : Nat} {B C E : DFA (Fin σ)}

theorem build_charged (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool)
    (env : Env B C E text.size (MaskedSuffixClass.height text.size)) (hs : Static text fallback source env)
    (capacity floor : Nat) (hc : capacity=2^h) (hn : text.size<2^h)
    (t : BoundaryTrie.Tree text.size Nat) (hg : t.Good (ArrayText.read text fallback))
    (hf : floor≤t.depth) (distinct : (positions t).Nodup)
    (metadata : ∀b,(MaskedTraversalDriver.build (h:=h) capacity floor t).plan.HasBand b→
      MaskedTraversalPositiveCoverage.Metadata text fallback capacity b)
    (global : Global C E) (valid : global.Valid text fallback source env) :
    let geometry:=MaskedTraversalDriver.build (h:=h) capacity floor t
    let out:=plan env capacity (MaskedTraversalAggregate.prepare C E h) geometry.plan global
    let D:=MaskedTraversalRepairCoherence.repairBudget C E env.repair.shared.prepared.K text.size h
    let R:=MaskedMutableProgression.Batch.rowBudget text.size
    let U:=outputBudget B C E env.repair.shared.prepared.K h text.size
    actualWork out.global+credit R U global+held D out.frame≤
      actualWork global+credit R U out.global+markBudget h D*marks geometry.plan+
        bandBudget B C E env.repair.shared.prepared.K h text.size*scheduledBands geometry.plan+9*nodes geometry.plan := by
  let D:=MaskedTraversalRepairCoherence.repairBudget C E env.repair.shared.prepared.K text.size h
  let R:=MaskedMutableProgression.Batch.rowBudget text.size
  let U:=outputBudget B C E env.repair.shared.prepared.K h text.size
  let M:=markBudget h D
  let F:=bandBudget B C E env.repair.shared.prepared.K h text.size
  induction t generalizing floor global with
  | empty=>
    let blank:=fresh (MaskedTraversalAggregate.prepare C E h) global
    have blankValid:=fresh_valid text fallback source env capacity 0 hc global valid
    have edgeCost:=edge_charged text fallback source env hs capacity floor 0 hc (MaskedTraversalFrontier.empty h) blank
      (MaskedTraversalFrontier.empty_valid h 0) blankValid metadata
    have freshCost:=fresh_charged (MaskedTraversalAggregate.prepare C E h) global D R U
    change actualWork (edge env capacity ⟨floor,0,MaskedTraversalFrontier.empty h,
        MaskedTraversalFrontier.lower capacity floor 0 (MaskedTraversalFrontier.empty h)⟩ blank).global+
      credit R U global+held D (edge env capacity ⟨floor,0,MaskedTraversalFrontier.empty h,
        MaskedTraversalFrontier.lower capacity floor 0 (MaskedTraversalFrontier.empty h)⟩ blank).frame≤_
    change _≤actualWork global+credit R U (edge env capacity ⟨floor,0,MaskedTraversalFrontier.empty h,
      MaskedTraversalFrontier.lower capacity floor 0 (MaskedTraversalFrontier.empty h)⟩ blank).global+
      M*stepEvents ⟨floor,0,MaskedTraversalFrontier.empty h,
      MaskedTraversalFrontier.lower capacity floor 0 (MaskedTraversalFrontier.empty h)⟩+
      F*(MaskedTraversalFrontier.lower capacity floor 0 (MaskedTraversalFrontier.empty h)).edge.path.bands.length+9
    dsimp only at edgeCost
    dsimp only [D,R,U,M,F,blank] at freshCost ⊢
    dsimp only [blank] at edgeCost
    omega
  | leaf a=>
    have bound : a.start<capacity:=by have hh:=a.bounded; omega
    let blank:=fresh (MaskedTraversalAggregate.prepare C E h) global
    let inserted:=MaskedTraversalFrontier.insert capacity a.length a.start (MaskedTraversalFrontier.empty h)
    let started:=leaf capacity a.start inserted blank
    let step : MaskedTraversalDriver.Step h:=⟨floor,a.length,inserted.frontier,MaskedTraversalFrontier.lower capacity floor a.length inserted.frontier⟩
    have blankValid:=fresh_valid text fallback source env capacity a.length hc global valid
    have startValid:=leaf_valid text fallback source env capacity a.length a.start hc bound blank blankValid
    have geoValid:=MaskedTraversalFrontier.insert_valid capacity a.length a.start (MaskedTraversalFrontier.empty h)
      (MaskedTraversalFrontier.empty_valid h a.length) hc bound
    have edgeCost:=edge_charged text fallback source env hs capacity floor a.length hc inserted.frontier started geoValid startValid metadata
    have freshCost:=fresh_charged (MaskedTraversalAggregate.prepare C E h) global D R U
    have leafCost:=leaf_charged capacity a.start inserted blank D R U
    change actualWork (edge env capacity step started).global+credit R U global+held D (edge env capacity step started).frame≤
      actualWork global+credit R U (edge env capacity step started).global+M*(1+stepEvents step)+
        F*step.lowered.edge.path.bands.length+9
    dsimp only at edgeCost
    simp only [Nat.mul_add,Nat.mul_one]
    dsimp only [D,R,U,M,F,blank,started,step] at freshCost leafCost ⊢
    dsimp only [blank,started] at edgeCost
    omega
  | node stem depth left right il ir=>
    let leftGeometry:=MaskedTraversalDriver.build (h:=h) capacity depth left
    let rightGeometry:=MaskedTraversalDriver.build (h:=h) capacity depth right
    let leftRun:=plan env capacity (MaskedTraversalAggregate.prepare C E h) leftGeometry.plan global
    let rightRun:=plan env capacity (MaskedTraversalAggregate.prepare C E h) rightGeometry.plan leftRun.global
    let merged:=MaskedTraversalFrontier.merge capacity depth leftGeometry.frontier rightGeometry.frontier
    let combined:=merge capacity merged leftRun.frame rightRun.frame rightRun.global
    let step : MaskedTraversalDriver.Step h:=⟨floor,depth,merged.frontier,MaskedTraversalFrontier.lower capacity floor depth merged.frontier⟩
    have depths:=Tree.edge_depths (ArrayText.read text fallback) stem depth left right hg
    have distinct' : (positions left++positions right).Nodup:=by
      simpa only [positions,BoundaryTrie.Tree.leaves,List.map_append] using distinct
    have parts:=List.pairwise_append.mp distinct'
    have leftValid:=MaskedTraversalDriver.build_valid capacity depth (ArrayText.read text fallback) left hg.1 hc hn depths.1
    have rightValid:=MaskedTraversalDriver.build_valid capacity depth (ArrayText.read text fallback) right hg.2.1 hc hn depths.2
    have leftDone:=build_preserves text fallback source env hs capacity depth hc hn left hg.1 depths.1 parts.1
      (fun b hb=>metadata b (Or.inr (Or.inl hb))) global valid
    have rightDone:=build_preserves text fallback source env hs capacity depth hc hn right hg.2.1 depths.2 parts.2.1
      (fun b hb=>metadata b (Or.inr (Or.inr hb))) leftRun.global leftDone.1.global
    have disjoint : ∀p,p∈leftGeometry.frontier.state.occurrences.entries→p∉positions right := by
      intro p hp hright
      have hleft:=(MaskedTraversalDriver.build_mem capacity depth (ArrayText.read text fallback) left hg.1 hc hn depths.1 p).mp hp
      exact parts.2.2 p hleft p hright rfl
    have saved:=Effect.saved text fallback source env leftGeometry.frontier.state capacity depth leftRun rightRun.global
      leftDone.1 rightDone.1.global leftValid.invariant hc (positions right) rightDone.2.1 disjoint
    have selected : State.Valid text fallback source env
        (if merged.keptLeft then leftGeometry.frontier.state else rightGeometry.frontier.state) capacity depth
        ⟨rightRun.global,if merged.keptLeft then leftRun.frame else rightRun.frame⟩ := by
      cases hk : merged.keptLeft
      · simpa only [hk,Bool.false_eq_true,if_false] using rightDone.1
      · simpa only [hk,if_true] using saved
    have mergedValid:=merge_valid text fallback source env capacity depth hc leftGeometry.frontier rightGeometry.frontier
      leftValid rightValid leftRun.frame rightRun.frame rightRun.global selected
    have mergedGeo:=MaskedTraversalFrontier.merge_valid capacity depth leftGeometry.frontier rightGeometry.frontier leftValid rightValid hc
    have leftCost:=il depth hg.1 depths.1 parts.1 (fun b hb=>metadata b (Or.inr (Or.inl hb))) global valid
    have rightCost:=ir depth hg.2.1 depths.2 parts.2.1 (fun b hb=>metadata b (Or.inr (Or.inr hb))) leftRun.global leftDone.1.global
    have mergeCost:=merge_charged capacity merged leftRun.frame rightRun.frame rightRun.global D R U
    have edgeCost:=edge_charged text fallback source env hs capacity floor depth hc merged.frontier combined mergedGeo mergedValid
      (fun b hb=>metadata b (Or.inl hb))
    change actualWork (edge env capacity step combined).global+credit R U global+held D (edge env capacity step combined).frame≤
      actualWork global+credit R U (edge env capacity step combined).global+
        M*(marks leftGeometry.plan+marks rightGeometry.plan+merged.revPatches.length+stepEvents step)+
        F*(scheduledBands leftGeometry.plan+scheduledBands rightGeometry.plan+step.lowered.edge.path.bands.length)+
        9*(nodes leftGeometry.plan+nodes rightGeometry.plan+1)
    dsimp only at leftCost rightCost edgeCost
    simp only [Nat.mul_add,Nat.mul_one]
    dsimp only [D,R,U,M,F,leftRun,rightRun,combined,step,leftGeometry,rightGeometry] at mergeCost ⊢
    dsimp only [leftRun,rightRun,combined,leftGeometry,rightGeometry] at rightCost edgeCost
    omega

theorem suffix_charged (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool)
    (env : Env B C E text.size (MaskedSuffixClass.height text.size)) (hs : Static text fallback source env)
    (capacity : Nat) (hc : capacity=2^h) (hn : text.size<2^h)
    (global : Global C E) (valid : global.Valid text fallback source env) :
    let geometry:=MaskedTraversalDriver.run h (prepareSuffixes text fallback).trie.tree
    let out:=plan env capacity (MaskedTraversalAggregate.prepare C E h) geometry.plan global
    let D:=MaskedTraversalRepairCoherence.repairBudget C E env.repair.shared.prepared.K text.size h
    let R:=MaskedMutableProgression.Batch.rowBudget text.size
    let U:=outputBudget B C E env.repair.shared.prepared.K h text.size
    let volume:=(text.size+1)*(text.size+1).log2+(text.size+1)
    actualWork out.global+credit R U global≤actualWork global+credit R U out.global+
      markBudget h D*(5*volume)+bandBudget B C E env.repair.shared.prepared.K h text.size*(4*volume+2*(text.size+1))+
        18*(text.size+1) := by
  have capEq : (MaskedOrdered.capacity h).1=capacity:=(MaskedOrdered.capacity_value h).trans hc.symm
  have good : (prepareSuffixes text fallback).trie.tree.Good (ArrayText.read text fallback):=
    (BoundaryTrie.Build.run_correct text fallback (suffixKeys text.size)).2.1
  have metadata : ∀b,(MaskedTraversalDriver.build (h:=h) capacity 0 (prepareSuffixes text fallback).trie.tree).plan.HasBand b→
      MaskedTraversalPositiveCoverage.Metadata text fallback capacity b := by
    intro b hb
    apply MaskedTraversalPositiveCoverage.actual_band_metadata text fallback h capacity hc hn b
    simpa only [MaskedTraversalDriver.run,capEq] using hb
  have cost:=build_charged text fallback source env hs capacity 0 hc hn (prepareSuffixes text fallback).trie.tree
    good (Nat.zero_le _) (MaskedRunTrieBridge.suffix_positions_nodup text fallback) metadata global valid
  have volume:=suffix_volume text fallback h hn
  simp only [MaskedTraversalDriver.run,capEq] at volume ⊢
  dsimp only at cost volume ⊢
  have hm:=Nat.mul_le_mul_left
    (markBudget h (MaskedTraversalRepairCoherence.repairBudget C E env.repair.shared.prepared.K text.size h)) volume.1
  have hb:=Nat.mul_le_mul_left (bandBudget B C E env.repair.shared.prepared.K h text.size) volume.2.1
  have hs:=Nat.mul_le_mul_left 9 volume.2.2
  simp only [Nat.mul_assoc] at hs
  omega

end REWB.MaskedTraversalExecute.Cost
