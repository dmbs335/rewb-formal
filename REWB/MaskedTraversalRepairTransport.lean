import REWB.MaskedTraversalRepairCoherenceCorrect

/-! Transport the actual scoped bank invariant through geometric updates.
The current successor closure need not monotonically grow as leaders
change. Instead actual predecessor preservation proves that a currently
unmarked leader was outside the earlier successor closure as well.
This prevents a hidden stale-incoming premise across partial merges.
-/
namespace REWB.MaskedTraversalRepairTransport
open REWB.MaskedOrdered REWB.MaskedClusterDescriptor REWB.MaskedTraversalBankReady
open REWB.MaskedTraversalContext REWB.MaskedTraversalNeighbor REWB.MaskedTraversalIncoming
open REWB.MaskedCluster REWB.MaskedTraversalAggregate REWB.MaskedTraversalRepairCoherence
variable {α : Type} {C E : DFA α} {h n h' : Nat}

theorem successor_predecessor (leaders : MaskedOrdered.Tree h) (capacity p first : Nat)
    (hg : leaders.Good) (hf : leaders.Fits 0) (hc : capacity=2^h)
    (hm : p∈leaders.entries) (hn : (MaskedOrdered.Tree.succ leaders capacity p).1=some first) :
    (MaskedOrdered.Tree.pred leaders capacity first).1=some p := by
  have hs:=MaskedOrdered.Tree.succ_correct leaders capacity p hg hf hc
  rw [hn] at hs
  apply pred_unique leaders.entries first _ (some p) (MaskedOrdered.Tree.pred_correct leaders capacity first hg hf hc)
  refine ⟨hm,hs.2.1,?_⟩
  intro q hq hqf
  by_cases hqp : q≤p
  · exact hqp
  · have hh:=hs.2.2 q hq (by omega)
    omega

theorem old_context_unmarked (before after : MaskedClusterLeaders.State h)
    (capacity old fresh first : Nat) (oldKeys newKeys : List Nat)
    (hb : MaskedClusterLeaders.Invariant old before) (ha : MaskedClusterLeaders.Invariant fresh after)
    (hc : capacity=2^h)
    (hocc : ∀p,p∈before.occurrences.entries→p∈after.occurrences.entries)
    (hdesc : ∀p,p∉newKeys→(describeLeader after capacity p).1=(describeLeader before capacity p).1)
    (hgrow : ∀p,p∈oldKeys→p∈newKeys) (hm : first∈after.leaders.entries)
    (hn : first∉(successors after.leaders capacity newKeys (MaskedTraversalDirty.empty h)).keys.tree.entries) :
    first∉(successors before.leaders capacity oldKeys (MaskedTraversalDirty.empty h)).keys.tree.entries := by
  have hprev:=predecessor_preserved before after capacity old fresh first newKeys hb ha hc hocc hdesc hm hn
  have hs:=successors_spec before.leaders capacity oldKeys (MaskedTraversalDirty.empty h)
    hb.leadGood hb.leadFits hc (MaskedOrdered.State.empty_valid h)
  intro hmarked
  rcases (hs.2.1 first).mp hmarked with ⟨p,hp,hleader,hsucc⟩|hbad
  · have hpOld:=successor_predecessor before.leaders capacity p first hb.leadGood hb.leadFits hc hleader hsucc
    have hpNew:=hprev.trans hpOld
    exact (previous_unmarked after capacity fresh first p newKeys ha hc hm hpNew hn) (hgrow p hp)
  · have hbad':=(MaskedOrdered.State.empty_valid h).2.2.mem_iff.mpr hbad
    cases hbad'

/-- No bank operation occurs during these geometric updates. The old
and new partition use the same length; the genuine shortening/reindex
transition is handled separately. -/
theorem repartition (env : Env C E n h') (before after : MaskedClusterLeaders.State h)
    (capacity L : Nat) (anchors : Array (Option Nat))
    (oldDirty newDirty : MaskedTraversalDirty.Marked h) (st : Mutable.Store.State C E)
    (entries : List (Option (Mutable.Store.Entry C E)))
    (hb : MaskedClusterLeaders.Invariant L before) (ha : MaskedClusterLeaders.Invariant L after)
    (hc : capacity=2^h)
    (hocc : ∀p,p∈before.occurrences.entries→p∈after.occurrences.entries)
    (hdesc : ∀p,p∉newDirty.keys.positions→(describeLeader after capacity p).1=(describeLeader before capacity p).1)
    (hgrow : ∀p,p∈oldDirty.keys.positions→p∈newDirty.keys.positions)
    (hp : Pending env before capacity L anchors oldDirty st entries) :
    Pending env after capacity L anchors newDirty st entries := by
  have hnotOld : ∀p,p∉newDirty.keys.positions→p∉oldDirty.keys.positions :=
    fun p hn hm=>hn (hgrow p hm)
  have hleader : ∀p,p∈after.leaders.entries→p∉newDirty.keys.positions→p∈before.leaders.entries := by
    intro p hm hn
    obtain ⟨d,hd,_,_⟩:=describeLeader_exists after capacity L p ha hc hm
    have hs:=describeLeader_sound before capacity L p hb hc d ((hdesc p hn).symm.trans hd)
    simpa only [hs.1] using hs.2.firstLeader
  refine ⟨?_,?_,?_,?_⟩
  · intro first hm hn
    obtain ⟨entry,he⟩:=hp.raw first (hleader first hm hn) (hnotOld first hn)
    exact ⟨entry,he.slot,(hdesc first hn).trans he.descriptor,he.anchor,he.run⟩
  · intro first hn entry he
    have hold:=hp.coherent first (hnotOld first hn) entry he
    exact ⟨(hdesc first hn).trans hold.descriptor,hold.current,hold.compiled,hold.raw⟩
  · intro first hm hn
    exact hp.complete first (hleader first hm hn) (hnotOld first hn)
  · intro first hn hctx entry he
    have hold:=hp.coherent first (hnotOld first hn) entry he
    have hd:=describeLeader_sound after capacity L first ha hc entry.config.descriptor ((hdesc first hn).trans hold.descriptor)
    have hm : first∈after.leaders.entries := by simpa only [hd.1] using hd.2.firstLeader
    have hvNew:=contextKeys_valid after capacity L newDirty ha hc
    have hnNew : first∉(successors after.leaders capacity newDirty.keys.positions (MaskedTraversalDirty.empty h)).keys.tree.entries :=
      fun hh=>hctx (hvNew.2.2.mem_iff.mpr hh)
    have hnOld:=old_context_unmarked before after capacity L L first oldDirty.keys.positions newDirty.keys.positions
      hb ha hc hocc hdesc hgrow hm hnNew
    have hvOld:=contextKeys_valid before capacity L oldDirty hb hc
    have hnOld' : first∉(contextKeys before capacity oldDirty).keys.positions :=
      fun hh=>hnOld (hvOld.2.2.mem_iff.mp hh)
    have linked:=hp.linked first (hnotOld first hn) hnOld' entry he
    have hin:=incoming_transport before after capacity L L first anchors newDirty.keys.positions hb ha hc hocc hdesc
      (by intro; intros; rfl) hm hnNew
    exact ⟨linked.anchor,linked.incoming.trans hin.1.symm,linked.enabled.trans hin.2.symm,linked.run⟩

theorem add_pending (env : Env C E n h') (before : MaskedClusterLeaders.State h)
    (capacity L p : Nat) (anchors : Array (Option Nat)) (dirty : MaskedTraversalDirty.Marked h)
    (st : Mutable.Store.State C E) (entries : List (Option (Mutable.Store.Entry C E)))
    (hv : dirty.keys.Valid) (hi : MaskedClusterLeaders.Invariant L before) (hc : capacity=2^h) (hb : p<capacity)
    (hp : Pending env before capacity L anchors dirty st entries) :
    Pending env (MaskedClusterLeaders.add capacity L p before).state capacity L anchors
      (MaskedTraversalDirty.markChange before.leaders (MaskedClusterLeaders.add capacity L p before).state.leaders
        capacity p dirty) st entries := by
  have ha:=MaskedClusterLeaders.add_invariant capacity L p before hi hc hb
  have hs:=MaskedTraversalDirty.markChange_spec before.leaders (MaskedClusterLeaders.add capacity L p before).state.leaders
    capacity p dirty hv hi.leadGood hi.leadFits ha.leadGood ha.leadFits hc (by omega)
  apply repartition env before (MaskedClusterLeaders.add capacity L p before).state capacity L anchors dirty _ st entries hi ha hc _ _ _ hp
  · intro x hx
    change x∈(MaskedOrdered.insert before.occurrences capacity p).tree.entries
    exact (MaskedOrdered.insert_mem before.occurrences capacity p x hi.occFits hc (by omega)).mpr (Or.inr hx)
  · intro x hn
    apply add_describe_away before capacity L p x hi hc hb
    intro hh
    exact hn (hs.1.2.2.mem_iff.mpr ((hs.2.1 x).mpr (Or.inl hh)))
  · intro x hx
    exact hs.1.2.2.mem_iff.mpr ((hs.2.1 x).mpr (Or.inr (hv.2.2.mem_iff.mp hx)))

theorem merge_pending (env : Env C E n h') (capacity L : Nat)
    (left right : MaskedTraversalFrontier.Frontier h) (anchors : Array (Option Nat))
    (dirty : MaskedTraversalDirty.Marked h) (st : Mutable.Store.State C E)
    (entries : List (Option (Mutable.Store.Entry C E))) (hv : dirty.keys.Valid)
    (hl : left.Valid L) (hr : right.Valid L) (hc : capacity=2^h)
    (hp : Pending env
      (if (MaskedTraversalFrontier.merge capacity L left right).keptLeft then left.state else right.state)
      capacity L anchors dirty st entries) :
    Pending env (MaskedTraversalFrontier.merge capacity L left right).frontier.state capacity L anchors
      (MaskedTraversalDirty.patches capacity (MaskedTraversalFrontier.merge capacity L left right).revPatches dirty) st entries := by
  have ha:=(MaskedTraversalFrontier.merge_valid capacity L left right hl hr hc).invariant
  have hb : MaskedClusterLeaders.Invariant L
      (if (MaskedTraversalFrontier.merge capacity L left right).keptLeft then left.state else right.state) := by
    split <;> first | exact hl.invariant | exact hr.invariant
  have hs:=MaskedTraversalDirty.patches_spec capacity L (MaskedTraversalFrontier.merge capacity L left right).revPatches dirty hv hc
    (MaskedTraversalDirty.merge_patches capacity L left right hl hr hc)
  apply repartition env _ _ capacity L anchors dirty _ st entries hb ha hc _ _ _ hp
  · intro x hx
    apply (MaskedTraversalFrontier.merge_mem capacity L left right hl hr hc x).mpr
    split at hx
    · exact Or.inl hx
    · exact Or.inr hx
  · intro x hn
    apply merge_describe_unmarked capacity L x left right dirty hv hl hr hc
    intro hh
    exact hn (hs.1.2.2.mem_iff.mpr hh)
  · intro x hx
    exact hs.1.2.2.mem_iff.mpr ((hs.2.1 x).mpr (Or.inr (hv.2.2.mem_iff.mp hx)))

end REWB.MaskedTraversalRepairTransport
