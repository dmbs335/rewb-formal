import REWB.MaskedTraversalExecuteEffect
import REWB.MaskedTraversalExecuteMergeSupport

/-! Exact suspended-frame transitions of the bank executor. Partial
imports and born-due drains only grow the actual pending set; all source,
raw-bank and anchor arrays remain untouched until a positive complete
band. The selected heavy tree is retained at a genuine merge.
-/
namespace REWB.MaskedTraversalExecute
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedTraversalAggregate
open REWB.MaskedTraversalRepairCoherence REWB.MaskedClusterDescriptor
variable {σ h : Nat} {B C E : DFA (Fin σ)}

theorem fresh_valid (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool)
    (env : Env B C E text.size (MaskedSuffixClass.height text.size))
    (capacity L : Nat) (hc : capacity=2^h) (global : Global C E)
    (hg : global.Valid text fallback source env) :
    (fresh (MaskedTraversalAggregate.prepare C E h) global).Valid text fallback source env (MaskedClusterLeaders.empty h) capacity L := by
  let entries : List (Option (Mutable.Store.Entry C E)):=List.replicate (2^h) none
  have absent : ∀(first : Nat) (entry : Mutable.Store.Entry C E),entries[first]?≠some (some entry) := by
    intro first entry he
    simp only [entries,List.getElem?_replicate] at he
    split at he <;> cases he
  have noDesc : ∀first d,(describeLeader (MaskedClusterLeaders.empty h) capacity first).1≠some d := by
    intro first d hd
    have hh:=describeLeader_sound (MaskedClusterLeaders.empty h) capacity L first
      (MaskedClusterLeaders.empty_invariant h L) hc d hd
    cases hh.2.firstMember
  refine ⟨⟨hg.sources,hg.size,hg.modulus,hg.runs,hg.slots,hg.anchors,hg.answers⟩,
    MaskedOrdered.State.empty_valid h,dirty_empty _,prepare_good C E h,?_,entries,Cells.prepare_represents C E h,?_,?_,?_⟩
  · intro first _ d hd
    exact False.elim (noDesc first d hd)
  · refine ⟨?_,?_,?_,?_⟩
    · intro first hm; cases hm
    · intro first _ entry he; exact False.elim (absent first entry he)
    · intro first hm; cases hm
    · intro first _ _ entry he; exact False.elim (absent first entry he)
  · intro first entry he; exact False.elim (absent first entry he)
  · intro first entry he; exact False.elim (absent first entry he)

theorem leaf_valid (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool)
    (env : Env B C E text.size (MaskedSuffixClass.height text.size))
    (capacity L p : Nat) (hc : capacity=2^h) (hp : p<capacity) (st : State C E h)
    (hv : st.Valid text fallback source env (MaskedClusterLeaders.empty h) capacity L) :
    (leaf capacity p (MaskedTraversalFrontier.insert capacity L p (MaskedTraversalFrontier.empty h)) st).Valid
      text fallback source env (MaskedClusterLeaders.add capacity L p (MaskedClusterLeaders.empty h)).state capacity L := by
  let before:=MaskedClusterLeaders.empty h
  have hi:=MaskedClusterLeaders.empty_invariant h L
  have after:=MaskedClusterLeaders.add_invariant capacity L p before hi hc hp
  have ds:=MaskedTraversalDirty.markChange_spec before.leaders (MaskedClusterLeaders.add capacity L p before).state.leaders
    capacity p st.frame.dirty hv.dirty hi.leadGood hi.leadFits after.leadGood after.leadFits hc (by omega)
  obtain ⟨entries,hr,hpending,hu,hs⟩:=hv.entries
  refine ⟨⟨hv.global.sources,hv.global.size,hv.global.modulus,hv.global.runs,hv.global.slots,hv.global.anchors,hv.global.answers⟩,
    ds.1,add_supported before capacity L p st.frame.dirty hv.dirty hi hc hp hv.dirtySupport,hv.tree,
    MaskedTraversalRetained.add_away before capacity text.size L p (ArrayText.read text fallback) st.global.anchors st.frame.dirty
      hv.dirty hi hc hp hv.own,entries,hr,
    MaskedTraversalRepairTransport.add_pending env.repair before capacity L p st.global.anchors st.frame.dirty st.global.store entries
      hv.dirty hi hc hp hpending,hu,?_⟩
  apply supported_mono before.occurrences.entries _ entries hs
  intro q hq
  exact (MaskedOrdered.insert_mem before.occurrences capacity p q hi.occFits hc (by omega)).mpr (Or.inr hq)

theorem initial_none_valid (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool)
    (env : Env B C E text.size (MaskedSuffixClass.height text.size))
    (capacity L : Nat) (partition : MaskedClusterLeaders.State h) (step : MaskedTraversalDriver.Step h) (st : State C E h)
    (hn : step.lowered.edge.initial=none) (hv : st.Valid text fallback source env partition capacity L) :
    (initial capacity step st).Valid text fallback source env partition capacity L := by
  rw [initial,hn]
  exact hv.with_stats text fallback source env partition capacity L st _

theorem initial_crossing_valid (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool)
    (env : Env B C E text.size (MaskedSuffixClass.height text.size))
    (capacity : Nat) (hc : capacity=2^h) (step : MaskedTraversalDriver.Step h) (st : State C E h)
    (hbefore : step.before.Valid step.high)
    (hinitial : step.lowered.edge.initial=some (MaskedClusterLeaders.shorten capacity step.high step.before.state))
    (hv : st.Valid text fallback source env step.before.state capacity step.high) :
    (initial capacity step st).Valid text fallback source env
      (MaskedClusterLeaders.shorten capacity step.high step.before.state).state capacity step.high := by
  obtain ⟨entries,hr,hpending,hu,hs⟩:=hv.entries
  have hi:=hbefore.invariant
  have hf:=hbefore.future
  have ds:=MaskedTraversalDirty.crossing_spec capacity step.high step.high step.before.state _ rfl st.frame.dirty hv.dirty hi hf hc (Nat.le_refl _)
  rw [initial,hinitial]
  refine ⟨⟨hv.global.sources,hv.global.size,hv.global.modulus,hv.global.runs,hv.global.slots,hv.global.anchors,hv.global.answers⟩,
    ds.1,crossing_supported capacity step.high step.high step.before.state st.frame.dirty hv.dirty hi hf hc (Nat.le_refl _) hv.dirtySupport,
    hv.tree,MaskedTraversalRetained.crossing_away capacity text.size step.high step.high step.before.state
      (ArrayText.read text fallback) st.global.anchors st.frame.dirty hv.dirty hi hf hc (Nat.le_refl _) hv.own,
    entries,hr,MaskedTraversalRepairTransport.crossing_same_pending env.repair capacity step.high step.before.state
      st.global.anchors st.frame.dirty st.global.store entries hv.dirty hi hf hc hpending,hu,hs⟩

theorem merge_valid (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool)
    (env : Env B C E text.size (MaskedSuffixClass.height text.size))
    (capacity L : Nat) (hc : capacity=2^h) (left right : MaskedTraversalFrontier.Frontier h)
    (hl : left.Valid L) (hr : right.Valid L) (leftFrame rightFrame : Frame C E h) (global : Global C E)
    (hv : State.Valid text fallback source env
      (if (MaskedTraversalFrontier.merge capacity L left right).keptLeft then left.state else right.state)
      capacity L ⟨global,if (MaskedTraversalFrontier.merge capacity L left right).keptLeft then leftFrame else rightFrame⟩) :
    (merge capacity (MaskedTraversalFrontier.merge capacity L left right) leftFrame rightFrame global).Valid
      text fallback source env (MaskedTraversalFrontier.merge capacity L left right).frontier.state capacity L := by
  let merged:=MaskedTraversalFrontier.merge capacity L left right
  let kept:=if merged.keptLeft then leftFrame else rightFrame
  have patches:=MaskedTraversalDirty.merge_patches capacity L left right hl hr hc
  have ds:=MaskedTraversalDirty.patches_spec capacity L merged.revPatches kept.dirty hv.dirty hc patches
  obtain ⟨entries,hrep,hpending,hu,hs⟩:=hv.entries
  have hds : DirtySupported (if merged.keptLeft then left.state.occurrences.entries else right.state.occurrences.entries) kept.dirty := by
    have hh:=hv.dirtySupport
    change DirtySupported (if merged.keptLeft then left.state else right.state).occurrences.entries kept.dirty at hh
    cases hb : merged.keptLeft <;> simpa only [hb,Bool.false_eq_true,if_false,if_true] using hh
  refine ⟨⟨hv.global.sources,hv.global.size,hv.global.modulus,hv.global.runs,hv.global.slots,hv.global.anchors,hv.global.answers⟩,
    ds.1,merge_dirty_supported capacity L left right kept.dirty hv.dirty hl hr hc hds,hv.tree,
    MaskedTraversalRetained.merge_away capacity text.size L left right (ArrayText.read text fallback) global.anchors kept.dirty
      hv.dirty hl hr hc hv.own,entries,hrep,
    MaskedTraversalRepairTransport.merge_pending env.repair capacity L left right global.anchors kept.dirty global.store entries
      hv.dirty hl hr hc hpending,hu,?_⟩
  apply supported_mono _ _ entries hs
  intro p hp
  apply (MaskedTraversalFrontier.merge_mem capacity L left right hl hr hc p).mpr
  split at hp
  · exact Or.inl hp
  · exact Or.inr hp

theorem initial_effect (capacity : Nat) (step : MaskedTraversalDriver.Step h) (st : State C E h) (positions : List Nat) :
    Effect positions st.global (initial capacity step st).global := by
  unfold initial
  split <;> exact ⟨by intros; rfl,by intros; rfl,[],rfl,rfl,by intro p hp; cases hp⟩

theorem fresh_effect (template : Template C E h) (global : Global C E) (positions : List Nat) :
    Effect positions global (fresh template global).global :=
  ⟨by intros; rfl,by intros; rfl,[],rfl,rfl,by intro p hp; cases hp⟩

theorem leaf_effect (capacity p : Nat) (inserted : MaskedTraversalFrontier.Inserted h) (st : State C E h) (positions : List Nat) :
    Effect positions st.global (leaf capacity p inserted st).global :=
  ⟨by intros; rfl,by intros; rfl,[],rfl,rfl,by intro p hp; cases hp⟩

theorem merge_effect (capacity : Nat) (merged : MaskedTraversalFrontier.Merged h)
    (left right : Frame C E h) (global : Global C E) (positions : List Nat) :
    Effect positions global (merge capacity merged left right global).global :=
  ⟨by intros; rfl,by intros; rfl,[],rfl,rfl,by intro p hp; cases hp⟩

end REWB.MaskedTraversalExecute
