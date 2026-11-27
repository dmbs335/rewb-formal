import REWB.MaskedTraversalExecuteTransitions
import REWB.MaskedTraversalPositiveCoverageExhaustion

/-! Structural induction over the actual queue-driven compressed edge.
Every emitted band is executed once before its lower crossing. The final
parent-depth state is pending, and all earlier reported bands remain
exhausted under the monotonically increasing physical deletion history.
-/
namespace REWB.MaskedTraversalExecute
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedTraversalAggregate
open REWB.MaskedTraversalPositiveCoverage (BandExhausted)
variable {σ h : Nat} {B C E : DFA (Fin σ)}

theorem band_exhausted (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool)
    (env : Env B C E text.size (MaskedSuffixClass.height text.size)) (hs : Static text fallback source env)
    (capacity : Nat) (hc : capacity=2^h) (b : MaskedTraversalEdge.Band h) (st : State C E h)
    (hv : st.Valid text fallback source env b.snapshot capacity b.hi)
    (hm : MaskedTraversalPositiveCoverage.Metadata text fallback capacity b) :
    BandExhausted B C E text.toList source env.repair.shared.target capacity (band env capacity b st).global.answers.history b := by
  let repaired:=MaskedTraversalRepairCoherence.apply env.repair b.snapshot capacity b.hi st.global.anchors st.frame.dirty st.global.store st.frame.tree
  have ready:=band_prepared text fallback source env hs capacity hc b st hv hm
  change BandExhausted B C E text.toList source env.repair.shared.target capacity
    (Collect.run B C E env.cut env.repair.shared repaired.store b.snapshot capacity repaired.tree
      (representative b) b.lo b.hi b.hi st.global.answers).answers.history b
  rw [hs.cut]
  exact MaskedTraversalPositiveCoverage.collect_exhausts B C E env.repair.shared repaired.store b capacity (representative b) b.hi
    repaired.anchors source repaired.tree st.global.answers text.toList fallback ready.2.2
    (by simpa only [Array.length_toList] using ready.1) hs.cRanges hs.eRanges hm.valid.bounds

theorem walk_preserves (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool)
    (env : Env B C E text.size (MaskedSuffixClass.height text.size)) (hs : Static text fallback source env)
    (capacity floor high : Nat) (hc : capacity=2^h) (s : MaskedClusterLeaders.State h) (st : State C E h)
    (hle : floor≤high) (hi : MaskedClusterLeaders.Invariant high s) (hf : MaskedClusterLeaders.Future high s)
    (hclean : MaskedTraversalEdge.Clean high s) (hv : st.Valid text fallback source env s capacity high)
    (metadata : ∀b,b∈(MaskedTraversalEdge.walk capacity floor high s).bands→
      MaskedTraversalPositiveCoverage.Metadata text fallback capacity b) :
    let path:=MaskedTraversalEdge.walk capacity floor high s
    let out:=bands env capacity path.bands st
    out.Valid text fallback source env path.state capacity floor ∧
      Effect s.occurrences.entries st.global out.global ∧
      ∀b,b∈path.bands→BandExhausted B C E text.toList source env.repair.shared.target capacity out.global.answers.history b := by
  induction high using Nat.strongRecOn generalizing s st with
  | ind high ih=>
    by_cases strict : floor<high
    · let boundary:=MaskedTraversalEdge.next floor high s
      let crossed:=MaskedClusterLeaders.shorten capacity boundary.length s
      let b : MaskedTraversalEdge.Band h:=⟨boundary.length+1,high,s,crossed⟩
      have below : boundary.length<high:=MaskedTraversalEdge.next_lt floor high s strict
      have above : floor≤boundary.length:=MaskedTraversalEdge.next_ge floor high s strict
      have walkEq : MaskedTraversalEdge.walk capacity floor high s=
          ⟨(MaskedTraversalEdge.walk capacity floor boundary.length crossed.state).state,
            b::(MaskedTraversalEdge.walk capacity floor boundary.length crossed.state).bands,
            crossed.popped+(MaskedTraversalEdge.walk capacity floor boundary.length crossed.state).popped,
            boundary.work+crossed.work+(MaskedTraversalEdge.walk capacity floor boundary.length crossed.state).work+8⟩ := by
        rw [MaskedTraversalEdge.walk,dif_pos strict]
      have thisMeta:=metadata b (by rw [walkEq]; exact List.mem_cons_self)
      have thisValid:=band_valid text fallback source env hs capacity hc b st hv thisMeta
      have thisEffect:=band_effect text fallback source env hs capacity hc b st hv thisMeta
      have thisDone:=band_exhausted text fallback source env hs capacity hc b st hv thisMeta
      have nextInv:=MaskedClusterLeaders.shorten_invariant capacity high boundary.length s hi hf hc (by omega)
      have nextFuture:=MaskedClusterLeaders.shorten_future capacity high boundary.length s hi hf (by omega)
      have nextClean:=MaskedTraversalEdge.shorten_clean capacity high boundary.length s hi
      have tail:=ih boundary.length below crossed.state (band env capacity b st) above nextInv nextFuture nextClean
        (by simpa only [b,Nat.add_sub_cancel] using thisValid)
        (fun a ha=>metadata a (by rw [walkEq]; exact List.mem_cons_of_mem b ha))
      dsimp only at tail ⊢
      rw [walkEq]
      change State.Valid text fallback source env (MaskedTraversalEdge.walk capacity floor boundary.length crossed.state).state capacity floor
        (bands env capacity (MaskedTraversalEdge.walk capacity floor boundary.length crossed.state).bands (band env capacity b st)) ∧ _
      refine ⟨tail.1,thisEffect.trans tail.2.1,?_⟩
      intro a ha
      rcases List.mem_cons.mp ha with heq|ha
      · subst a
        exact thisDone.mono tail.2.1.history
      · exact tail.2.2 a ha
    · have same : high=floor:=by omega
      subst high
      rw [MaskedTraversalEdge.walk,dif_neg (Nat.lt_irrefl floor)]
      refine ⟨?_,?_,?_⟩
      · exact hv.with_stats text fallback source env s capacity floor st _
      · exact ⟨by intros; rfl,by intros; rfl,[],rfl,rfl,by intro p hp; cases hp⟩
      · intro b hb; cases hb

theorem edge_preserves (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool)
    (env : Env B C E text.size (MaskedSuffixClass.height text.size)) (hs : Static text fallback source env)
    (capacity floor high : Nat) (hc : capacity=2^h) (before : MaskedTraversalFrontier.Frontier h) (st : State C E h)
    (hle : floor≤high) (hbefore : before.Valid high) (hv : st.Valid text fallback source env before.state capacity high)
    (metadata : ∀b,b∈(MaskedTraversalFrontier.lower capacity floor high before).edge.path.bands→
      MaskedTraversalPositiveCoverage.Metadata text fallback capacity b) :
    let step : MaskedTraversalDriver.Step h:=⟨floor,high,before,MaskedTraversalFrontier.lower capacity floor high before⟩
    let out:=edge env capacity step st
    out.Valid text fallback source env step.lowered.frontier.state capacity floor ∧
      Effect before.state.occurrences.entries st.global out.global ∧
      ∀b,b∈step.lowered.edge.path.bands→BandExhausted B C E text.toList source env.repair.shared.target capacity out.global.answers.history b := by
  let step : MaskedTraversalDriver.Step h:=⟨floor,high,before,MaskedTraversalFrontier.lower capacity floor high before⟩
  by_cases strict : floor<high
  · let first:=MaskedClusterLeaders.shorten capacity high before.state
    have initEq : step.lowered.edge.initial=some first := by
      simp only [step,MaskedTraversalFrontier.lower,MaskedTraversalEdge.run,if_pos strict]
      rfl
    have initValid:=initial_crossing_valid text fallback source env capacity hc step st hbefore initEq hv
    have firstInv:=MaskedClusterLeaders.shorten_invariant capacity high high before.state hbefore.invariant hbefore.future hc (Nat.le_refl _)
    have firstFuture:=MaskedClusterLeaders.shorten_future capacity high high before.state hbefore.invariant hbefore.future (Nat.le_refl _)
    have firstClean:=MaskedTraversalEdge.shorten_clean capacity high high before.state hbefore.invariant
    have tail:=walk_preserves text fallback source env hs capacity floor high hc first.state (initial capacity step st)
      hle firstInv firstFuture firstClean initValid (by
        intro b hb
        apply metadata b
        simpa only [MaskedTraversalFrontier.lower,MaskedTraversalEdge.run,if_pos strict] using hb)
    have outputEq : edge env capacity step st=bands env capacity (MaskedTraversalEdge.walk capacity floor high first.state).bands (initial capacity step st) := by
      simp only [edge,step,MaskedTraversalFrontier.lower,MaskedTraversalEdge.run,if_pos strict]
      rfl
    have frontEq : step.lowered.frontier.state=(MaskedTraversalEdge.walk capacity floor high first.state).state := by
      simp only [step,MaskedTraversalFrontier.lower,MaskedTraversalEdge.run,if_pos strict]
      rfl
    have bandsEq : step.lowered.edge.path.bands=(MaskedTraversalEdge.walk capacity floor high first.state).bands := by
      simp only [step,MaskedTraversalFrontier.lower,MaskedTraversalEdge.run,if_pos strict]
      rfl
    change State.Valid text fallback source env step.lowered.frontier.state capacity floor (edge env capacity step st) ∧ _
    rw [outputEq,frontEq,bandsEq]
    exact ⟨tail.1,(initial_effect capacity step st before.state.occurrences.entries).trans tail.2.1,tail.2.2⟩
  · have same : high=floor:=by omega
    subst high
    simp only [edge,initial,MaskedTraversalFrontier.lower,MaskedTraversalEdge.run_equal,bands]
    refine ⟨?_,?_,?_⟩
    · exact hv.with_stats text fallback source env before.state capacity floor st _
    · exact ⟨by intros; rfl,by intros; rfl,[],rfl,rfl,by intro p hp; cases hp⟩
    · intro b hb; cases hb

end REWB.MaskedTraversalExecute
