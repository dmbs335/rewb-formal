import REWB.MaskedTraversalExecuteEdge

/-! Actual child/child/merge/edge execution on the constructed plan.
The right child consumes the global state returned by the left. Its
proved write/erasure footprint preserves the suspended left frame, even
when that frame is pending at an incomplete parent depth. The actual
cached-count heavy selection then chooses one of these valid frames.
-/
namespace REWB.MaskedTraversalExecute
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedTraversalAggregate
open REWB.BoundaryTrie
open REWB.MaskedRunDiscovery (positions)
open REWB.MaskedTraversalPositiveCoverage (BandExhausted Exhausted)
variable {σ h : Nat} {B C E : DFA (Fin σ)}

theorem build_preserves (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool)
    (env : Env B C E text.size (MaskedSuffixClass.height text.size)) (hs : Static text fallback source env)
    (capacity floor : Nat) (hc : capacity=2^h) (hn : text.size<2^h)
    (t : BoundaryTrie.Tree text.size Nat) (hg : t.Good (ArrayText.read text fallback))
    (hf : floor≤t.depth) (distinct : (positions t).Nodup)
    (metadata : ∀b,(MaskedTraversalDriver.build (h:=h) capacity floor t).plan.HasBand b→
      MaskedTraversalPositiveCoverage.Metadata text fallback capacity b)
    (global : Global C E) (valid : global.Valid text fallback source env) :
    let geometry:=MaskedTraversalDriver.build (h:=h) capacity floor t
    let out:=plan env capacity (MaskedTraversalAggregate.prepare C E h) geometry.plan global
    out.Valid text fallback source env geometry.frontier.state capacity floor ∧
      Effect (positions t) global out.global ∧
      Exhausted B C E text.toList source env.repair.shared.target capacity out.global.answers.history geometry.plan := by
  induction t generalizing floor global with
  | empty=>
    let blank:=fresh (MaskedTraversalAggregate.prepare C E h) global
    have blankValid:=fresh_valid text fallback source env capacity 0 hc global valid
    have done:=edge_preserves text fallback source env hs capacity floor 0 hc (MaskedTraversalFrontier.empty h) blank hf
      (MaskedTraversalFrontier.empty_valid h 0) blankValid metadata
    exact ⟨done.1,(fresh_effect _ global []).trans done.2.1,done.2.2⟩
  | leaf a=>
    have bound : a.start<capacity:=by have hh:=a.bounded; omega
    let blank:=fresh (MaskedTraversalAggregate.prepare C E h) global
    let inserted:=MaskedTraversalFrontier.insert capacity a.length a.start (MaskedTraversalFrontier.empty h)
    let started:=leaf capacity a.start inserted blank
    have blankValid:=fresh_valid text fallback source env capacity a.length hc global valid
    have startValid:=leaf_valid text fallback source env capacity a.length a.start hc bound blank blankValid
    have geoValid:=MaskedTraversalFrontier.insert_valid capacity a.length a.start (MaskedTraversalFrontier.empty h)
      (MaskedTraversalFrontier.empty_valid h a.length) hc bound
    have done:=edge_preserves text fallback source env hs capacity floor a.length hc inserted.frontier started hf geoValid startValid metadata
    have support : ∀p,p∈inserted.frontier.state.occurrences.entries→p∈positions (.leaf a) := by
      intro p hp
      have hm:=(MaskedTraversalFrontier.insert_mem capacity a.length a.start p (MaskedTraversalFrontier.empty h)
        (MaskedTraversalFrontier.empty_valid h a.length) hc bound).mp hp
      rcases hm with he|hm
      · simpa only [positions,BoundaryTrie.Tree.leaves,List.map_cons,List.map_nil,List.mem_singleton] using he
      · cases hm
    exact ⟨done.1,((fresh_effect _ global (positions (.leaf a))).trans
      (leaf_effect capacity a.start inserted blank (positions (.leaf a)))).trans (done.2.1.mono support),done.2.2⟩
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
    have leftDone:=il depth hg.1 depths.1 parts.1
      (fun b hb=>metadata b (Or.inr (Or.inl hb))) global valid
    have rightDone:=ir depth hg.2.1 depths.2 parts.2.1
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
    have edgeDone:=edge_preserves text fallback source env hs capacity floor depth hc merged.frontier combined hf mergedGeo mergedValid
      (fun b hb=>metadata b (Or.inl hb))
    have leftSupport : ∀p,p∈positions left→p∈positions (.node stem depth left right) := by
      intro p hp
      simp only [positions,BoundaryTrie.Tree.leaves,List.map_append,List.mem_append]
      exact Or.inl hp
    have rightSupport : ∀p,p∈positions right→p∈positions (.node stem depth left right) := by
      intro p hp
      simp only [positions,BoundaryTrie.Tree.leaves,List.map_append,List.mem_append]
      exact Or.inr hp
    have mergedSupport : ∀p,p∈merged.frontier.state.occurrences.entries→p∈positions (.node stem depth left right) := by
      intro p hp
      rcases (MaskedTraversalFrontier.merge_mem capacity depth leftGeometry.frontier rightGeometry.frontier leftValid rightValid hc p).mp hp with hp|hp
      · exact leftSupport p ((MaskedTraversalDriver.build_mem capacity depth (ArrayText.read text fallback) left hg.1 hc hn depths.1 p).mp hp)
      · exact rightSupport p ((MaskedTraversalDriver.build_mem capacity depth (ArrayText.read text fallback) right hg.2.1 hc hn depths.2 p).mp hp)
    have leftEffect:=leftDone.2.1.mono leftSupport
    have rightEffect:=rightDone.2.1.mono rightSupport
    have mergeEffect:=merge_effect capacity merged leftRun.frame rightRun.frame rightRun.global (positions (.node stem depth left right))
    have edgeEffect:=edgeDone.2.1.mono mergedSupport
    have allEffect:=((leftEffect.trans rightEffect).trans mergeEffect).trans edgeEffect
    have leftHistory:=(rightEffect.trans mergeEffect).trans edgeEffect
    have rightHistory:=mergeEffect.trans edgeEffect
    have done:=MaskedTraversalPositiveCoverage.exhausted_node B C E text.toList source env.repair.shared.target capacity
      (edge env capacity step combined).global.answers.history leftGeometry.plan rightGeometry.plan merged step
      (leftDone.2.2.mono leftHistory.history) (rightDone.2.2.mono rightHistory.history) edgeDone.2.2
    exact ⟨edgeDone.1,allEffect,done⟩

end REWB.MaskedTraversalExecute
