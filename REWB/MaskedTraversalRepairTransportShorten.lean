import REWB.MaskedTraversalRepairSnapshotRegression

/-! Actual bank-model transport over threshold crossings. A completed
band supplies coherent current banks and retained anchors. One common
word action reindexes its aggregate; the actual drained live records
create the pending reset set at the lower length. The final parent-depth
state is allowed to remain pending, with no incomplete-class reset.
-/
namespace REWB.MaskedTraversalRepairTransport
open REWB.MaskedOrdered REWB.MaskedClusterDescriptor REWB.MaskedTraversalBankReady
open REWB.MaskedTraversalContext REWB.MaskedTraversalNeighbor REWB.MaskedTraversalIncoming
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedTraversalAggregate REWB.MaskedTraversalRepairCoherence
variable {α : Type} {C E : DFA α} {h n h' : Nat}

def entryAt (z : ReplayMaps.Value C.stateCount E.stateCount) (fresh : Nat) (entry : Mutable.Store.Entry C E) :
    Mutable.Store.Entry C E :=
  ⟨withLength entry.config fresh,(Counted.reindex (bankAction z) entry.bank).1⟩

theorem reindexed_get (z : ReplayMaps.Value C.stateCount E.stateCount) (fresh first : Nat)
    (entries : List (Option (Mutable.Store.Entry C E))) (entry : Mutable.Store.Entry C E)
    (he : (entries.map (Cells.reindexedEntry z fresh))[first]?=some (some entry)) :
    ∃old,entries[first]?=some (some old) ∧ entry=entryAt z fresh old := by
  cases hs : entries[first]? with
  | none => simp only [List.getElem?_map,hs,Option.map] at he; cases he
  | some value =>
    cases value with
    | none => simp only [List.getElem?_map,hs,Option.map,Cells.reindexedEntry,Option.some.injEq] at he; cases he
    | some old =>
      simp only [List.getElem?_map,hs,Option.map,Cells.reindexedEntry,Option.some.injEq] at he
      exact ⟨old,rfl,he.symm⟩

theorem shortened_entry (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity base old fresh first : Nat)
    (anchors : Array (Option Nat)) (entry : Mutable.Store.Entry C E)
    (w : Word α) (fallback : α)
    (hi : MaskedClusterLeaders.Invariant old partition) (hc : capacity=2^h)
    (hfull : MaskedRunDiscovery.Complete (ArrayText.read w.toArray fallback) w.length base old partition.occurrences.entries)
    (ha : MaskedTraversalRetained.Away partition capacity (ArrayText.read w.toArray fallback) w.length old anchors [])
    (hcoh : Cells.EntryState env st partition capacity old first entry)
    (hlink : Cells.Linked env st partition capacity old first anchors entry.config)
    (hC : env.cRanges=BoundaryApplication.Range.build C w) (hE : env.eRanges=BoundaryApplication.Range.build E w)
    (hle : fresh≤old) (hrep : base+old≤w.length) :
    Cells.EntryState env st partition capacity fresh first
      (entryAt (ReplayMaps.word C E (Spec.slice w (base+fresh) (base+old))) fresh entry) := by
  obtain ⟨H,hH,cert⟩:=ha first (by simp) entry.config.descriptor hcoh.descriptor
  have hanchor : entry.config.anchor=H := by
    simpa only [readAnchor,hH,Option.getD_some] using hlink.anchor
  have hd:=describeLeader_sound partition capacity old first hi hc entry.config.descriptor hcoh.descriptor
  have hcand:=(hfull entry.config.descriptor.first).mp hd.2.firstMember
  have hcopy : Spec.slice w base (base+old)=
      Spec.slice w entry.config.descriptor.first (entry.config.descriptor.first+old) := by
    have hh:=hcand.2.symm
    rw [ArrayText.segment_word w fallback base old hrep,
      ArrayText.segment_word w fallback entry.config.descriptor.first old hcand.1] at hh
    simpa only [Spec.slice,Nat.add_sub_cancel_left] using hh
  apply Cells.EntryState.shortened env st partition capacity old first entry hcoh w base fresh hC hE hle
  · rw [hanchor]
    exact cert.current
  · exact hrep
  · rw [hanchor]
    have hlast:=cert.lastBound
    have hfirst:=hd.2.first_le_last
    omega
  · exact hcopy

/-- Born-due records are drained at the node's unchanged current length,
before the first positive-width band is emitted. Existing pending keys
survive; no anchored-word replay or class reset is needed at this point. -/
theorem crossing_same_pending (env : Env C E n h') (capacity L : Nat) (s : MaskedClusterLeaders.State h)
    (anchors : Array (Option Nat)) (dirty : MaskedTraversalDirty.Marked h) (st : Mutable.Store.State C E)
    (entries : List (Option (Mutable.Store.Entry C E))) (hv : dirty.keys.Valid)
    (hi : MaskedClusterLeaders.Invariant L s) (hf : MaskedClusterLeaders.Future L s) (hc : capacity=2^h)
    (hp : Pending env s capacity L anchors dirty st entries) :
    Pending env (MaskedClusterLeaders.shorten capacity L s).state capacity L anchors
      (MaskedTraversalDirty.crossing s (MaskedClusterLeaders.shorten capacity L s) capacity dirty) st entries := by
  have ha:=MaskedClusterLeaders.shorten_invariant capacity L L s hi hf hc (Nat.le_refl _)
  have hbound:=MaskedClusterLeaders.live_bound capacity L L s hi hc
  have hs:=MaskedTraversalDirty.live_spec s.leaders (MaskedClusterLeaders.shorten capacity L s).state.leaders capacity
    (MaskedClusterLeaders.shorten capacity L s).live dirty hv hi.leadGood hi.leadFits ha.leadGood ha.leadFits hc
    (fun e he=>by have hh:=hbound e he; omega)
  apply repartition env s (MaskedClusterLeaders.shorten capacity L s).state capacity L anchors dirty _ st entries hi ha hc
    (by intro p hp; exact hp) _ _ hp
  · intro p hn
    apply crossing_describe_unmarked capacity L L p s dirty hv hi hf hc (Nat.le_refl _)
    intro hh
    exact hn (hs.1.2.2.mem_iff.mpr hh)
  · intro p hp
    exact hs.1.2.2.mem_iff.mpr ((hs.2.1 p).mpr (Or.inr (hv.2.2.mem_iff.mp hp)))

theorem crossing_pending (env : Env C E n h') (capacity base old fresh : Nat) (s : MaskedClusterLeaders.State h)
    (anchors : Array (Option Nat)) (st : Mutable.Store.State C E) (entries : List (Option (Mutable.Store.Entry C E)))
    (w : Word α) (fallback : α)
    (hi : MaskedClusterLeaders.Invariant old s) (hf : MaskedClusterLeaders.Future old s) (hc : capacity=2^h)
    (hfull : MaskedRunDiscovery.Complete (ArrayText.read w.toArray fallback) w.length base old s.occurrences.entries)
    (ha : MaskedTraversalRetained.Away s capacity (ArrayText.read w.toArray fallback) w.length old anchors [])
    (hcoh : Cells.Coherent env.shared st s capacity old entries) (hcomplete : Cells.CompleteModel s entries)
    (hlink : Cells.LinkedEntries env.shared st s capacity old anchors entries)
    (hC : env.shared.cRanges=BoundaryApplication.Range.build C w) (hE : env.shared.eRanges=BoundaryApplication.Range.build E w)
    (hle : fresh≤old) (hrep : base+old≤w.length) :
    Pending env (MaskedClusterLeaders.shorten capacity fresh s).state capacity fresh anchors
      (MaskedTraversalDirty.crossing s (MaskedClusterLeaders.shorten capacity fresh s) capacity (MaskedTraversalDirty.empty h)) st
      (entries.map (Cells.reindexedEntry (ReplayMaps.word C E (Spec.slice w (base+fresh) (base+old))) fresh)) := by
  let after:=(MaskedClusterLeaders.shorten capacity fresh s).state
  let dirty:=MaskedTraversalDirty.crossing s (MaskedClusterLeaders.shorten capacity fresh s) capacity (MaskedTraversalDirty.empty h)
  let z:=ReplayMaps.word C E (Spec.slice w (base+fresh) (base+old))
  have hv:=MaskedOrdered.State.empty_valid h
  have hnew:=MaskedClusterLeaders.shorten_invariant capacity old fresh s hi hf hc hle
  have hbound:=MaskedClusterLeaders.live_bound capacity old fresh s hi hc
  have hs:=MaskedTraversalDirty.live_spec s.leaders after.leaders capacity
    (MaskedClusterLeaders.shorten capacity fresh s).live (MaskedTraversalDirty.empty h) hv
    hi.leadGood hi.leadFits hnew.leadGood hnew.leadFits hc (fun e he=>by have hh:=hbound e he; omega)
  have hdesc : ∀p,p∉dirty.keys.positions→(describeLeader after capacity p).1=(describeLeader s capacity p).1 := by
    intro p hn
    apply crossing_describe_unmarked capacity old fresh p s (MaskedTraversalDirty.empty h) hv hi hf hc hle
    intro hh
    exact hn (hs.1.2.2.mem_iff.mpr hh)
  have hown:=MaskedTraversalRetained.crossing_away capacity w.length old fresh s (ArrayText.read w.toArray fallback)
    anchors (MaskedTraversalDirty.empty h) hv hi hf hc hle ha
  have hleader : ∀p,p∈after.leaders.entries→p∉dirty.keys.positions→p∈s.leaders.entries := by
    intro p hm hn
    obtain ⟨d,hd,_,_⟩:=describeLeader_exists after capacity fresh p hnew hc hm
    have hh:=describeLeader_sound s capacity old p hi hc d ((hdesc p hn).symm.trans hd)
    simpa only [hh.1] using hh.2.firstLeader
  change Pending env after capacity fresh anchors dirty st (entries.map (Cells.reindexedEntry z fresh))
  refine ⟨?_,?_,?_,?_⟩
  · intro first hm hn
    obtain ⟨entry,he⟩:=hcomplete first (hleader first hm hn)
    have cc:=hcoh first entry he
    have ll:=hlink first entry he
    obtain ⟨raw,hraw⟩:=coherent_raw env.shared st s capacity old first anchors entry cc ll.anchor ll.run
    obtain ⟨H,hH,_⟩:=ha first (by simp) entry.config.descriptor cc.descriptor
    have hread : readAnchor anchors first fresh=readAnchor anchors first old := by simp only [readAnchor,hH,Option.getD_some]
    exact ⟨raw,hraw.slot,(hdesc first hn).trans hraw.descriptor,hraw.anchor.trans hread.symm,hraw.run⟩
  · intro first hn entry he
    obtain ⟨before,hbefore,rfl⟩:=reindexed_get z fresh first entries entry he
    have cc:=shortened_entry env.shared st s capacity base old fresh first anchors before w fallback hi hc hfull ha
      (hcoh first before hbefore) (hlink first before hbefore) hC hE hle hrep
    exact ⟨(hdesc first hn).trans cc.descriptor,cc.current,cc.compiled,cc.raw⟩
  · intro first hm hn
    obtain ⟨entry,he⟩:=hcomplete first (hleader first hm hn)
    refine ⟨entryAt z fresh entry,?_⟩
    simp only [List.getElem?_map,he,Option.map,Cells.reindexedEntry]
    rfl
  · intro first hn hctx entry he
    obtain ⟨before,hbefore,rfl⟩:=reindexed_get z fresh first entries entry he
    have cc:=hcoh first before hbefore
    have ll:=hlink first before hbefore
    have hd:=describeLeader_sound after capacity fresh first hnew hc before.config.descriptor ((hdesc first hn).trans cc.descriptor)
    have hm : first∈after.leaders.entries := by simpa only [hd.1] using hd.2.firstLeader
    have hctxGood:=contextKeys_valid after capacity fresh dirty hnew hc
    have hctxTree : first∉(successors after.leaders capacity dirty.keys.positions (MaskedTraversalDirty.empty h)).keys.tree.entries :=
      fun hh=>hctx (hctxGood.2.2.mem_iff.mpr hh)
    have hin:=retained_transport s after capacity w.length old fresh first (ArrayText.read w.toArray fallback) anchors dirty.keys.positions
      hi hnew hc (by intro p hp; exact hp) hdesc hown hm hctxTree
    obtain ⟨H,hH,_⟩:=ha first (by simp) before.config.descriptor cc.descriptor
    have hread : readAnchor anchors first fresh=readAnchor anchors first old := by simp only [readAnchor,hH,Option.getD_some]
    exact ⟨ll.anchor.trans hread.symm,ll.incoming.trans hin.1.symm,ll.enabled.trans hin.2.symm,ll.run⟩

theorem reindexed_unclipped (z : ReplayMaps.Value C.stateCount E.stateCount) (fresh n : Nat)
    (entries : List (Option (Mutable.Store.Entry C E))) (hu : Cells.Unclipped n entries) :
    Cells.Unclipped n (entries.map (Cells.reindexedEntry z fresh)) := by
  intro first entry he
  obtain ⟨before,hbefore,rfl⟩:=reindexed_get z fresh first entries entry he
  exact hu first before hbefore

end REWB.MaskedTraversalRepairTransport
