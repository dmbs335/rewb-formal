import REWB.MaskedTraversalIncoming

/-! No structural incoming oracle: instantiate the exact predecessor
transport with the real sparse dirty collectors and real occurrence
updates, including heavy-side selection and a batch of live thresholds.
Only the actual current successors of dirty leaders require a context
refresh beyond the primary reset set.
-/
namespace REWB.MaskedTraversalIncoming
open REWB.MaskedOrdered REWB.MaskedClusterDescriptor REWB.MaskedTraversalBankReady
open REWB.MaskedTraversalContext REWB.MaskedTraversalNeighbor REWB.MaskedTraversalFrontier
variable {α : Type} {h : Nat}

theorem add_incoming_away (before : MaskedClusterLeaders.State h) (capacity L p first : Nat)
    (anchors : Array (Option Nat)) (dirty : MaskedTraversalDirty.Marked h)
    (hv : dirty.keys.Valid) (hi : MaskedClusterLeaders.Invariant L before)
    (hc : capacity=2^h) (hp : p<capacity)
    (hm : first∈(MaskedClusterLeaders.add capacity L p before).state.leaders.entries)
    (hn : first∉(successors (MaskedClusterLeaders.add capacity L p before).state.leaders capacity
      (MaskedTraversalDirty.markChange before.leaders (MaskedClusterLeaders.add capacity L p before).state.leaders
        capacity p dirty).keys.positions (MaskedTraversalDirty.empty h)).keys.tree.entries) :
    (incoming (MaskedClusterLeaders.add capacity L p before).state capacity first L anchors).cursor=
      (incoming before capacity first L anchors).cursor ∧
    (incoming (MaskedClusterLeaders.add capacity L p before).state capacity first L anchors).enabled=
      (incoming before capacity first L anchors).enabled := by
  have ha:=MaskedClusterLeaders.add_invariant capacity L p before hi hc hp
  have hs:=MaskedTraversalDirty.markChange_spec before.leaders
    (MaskedClusterLeaders.add capacity L p before).state.leaders capacity p dirty hv
    hi.leadGood hi.leadFits ha.leadGood ha.leadFits hc (by omega)
  apply incoming_transport before (MaskedClusterLeaders.add capacity L p before).state capacity L L first anchors
    _ hi ha hc _ _ (by intro; intros; rfl) hm hn
  · intro x hx
    change x∈(MaskedOrdered.insert before.occurrences capacity p).tree.entries
    exact (MaskedOrdered.insert_mem before.occurrences capacity p x hi.occFits hc (by omega)).mpr (Or.inr hx)
  · intro x hx
    apply add_describe_away before capacity L p x hi hc hp
    intro hh
    apply hx
    apply hs.1.2.2.mem_iff.mpr
    exact (hs.2.1 x).mpr (Or.inl hh)

theorem merge_incoming_away (capacity L first : Nat) (left right : Frontier h)
    (anchors : Array (Option Nat)) (dirty : MaskedTraversalDirty.Marked h)
    (hv : dirty.keys.Valid) (hl : left.Valid L) (hr : right.Valid L) (hc : capacity=2^h)
    (hm : first∈(MaskedTraversalFrontier.merge capacity L left right).frontier.state.leaders.entries)
    (hn : first∉(successors (MaskedTraversalFrontier.merge capacity L left right).frontier.state.leaders capacity
      (MaskedTraversalDirty.patches capacity (MaskedTraversalFrontier.merge capacity L left right).revPatches dirty).keys.positions
      (MaskedTraversalDirty.empty h)).keys.tree.entries) :
    (incoming (MaskedTraversalFrontier.merge capacity L left right).frontier.state capacity first L anchors).cursor=
      (incoming (if (MaskedTraversalFrontier.merge capacity L left right).keptLeft then left.state else right.state)
        capacity first L anchors).cursor ∧
    (incoming (MaskedTraversalFrontier.merge capacity L left right).frontier.state capacity first L anchors).enabled=
      (incoming (if (MaskedTraversalFrontier.merge capacity L left right).keptLeft then left.state else right.state)
        capacity first L anchors).enabled := by
  have ha:=(merge_valid capacity L left right hl hr hc).invariant
  have hb : MaskedClusterLeaders.Invariant L
      (if (MaskedTraversalFrontier.merge capacity L left right).keptLeft then left.state else right.state) := by
    split <;> first | exact hl.invariant | exact hr.invariant
  have hp:=MaskedTraversalDirty.merge_patches capacity L left right hl hr hc
  have hs:=MaskedTraversalDirty.patches_spec capacity L
    (MaskedTraversalFrontier.merge capacity L left right).revPatches dirty hv hc hp
  apply incoming_transport _ _ capacity L L first anchors _ hb ha hc _ _ (by intro; intros; rfl) hm hn
  · intro x hx
    apply (merge_mem capacity L left right hl hr hc x).mpr
    split at hx
    · exact Or.inl hx
    · exact Or.inr hx
  · intro x hx
    apply merge_describe_unmarked capacity L x left right dirty hv hl hr hc
    intro hh
    exact hx (hs.1.2.2.mem_iff.mpr hh)

theorem crossing_incoming_away (capacity n old fresh first : Nat) (s : MaskedClusterLeaders.State h)
    (f : Nat→α) (anchors : Array (Option Nat)) (dirty : MaskedTraversalDirty.Marked h)
    (hv : dirty.keys.Valid) (hi : MaskedClusterLeaders.Invariant old s)
    (hf : MaskedClusterLeaders.Future old s) (hc : capacity=2^h) (hle : fresh≤old)
    (hb : MaskedTraversalRetained.Away s capacity f n old anchors dirty.keys.positions)
    (hm : first∈(MaskedClusterLeaders.shorten capacity fresh s).state.leaders.entries)
    (hn : first∉(successors (MaskedClusterLeaders.shorten capacity fresh s).state.leaders capacity
      (MaskedTraversalDirty.crossing s (MaskedClusterLeaders.shorten capacity fresh s) capacity dirty).keys.positions
      (MaskedTraversalDirty.empty h)).keys.tree.entries) :
    (incoming (MaskedClusterLeaders.shorten capacity fresh s).state capacity first fresh anchors).cursor=
      (incoming s capacity first old anchors).cursor ∧
    (incoming (MaskedClusterLeaders.shorten capacity fresh s).state capacity first fresh anchors).enabled=
      (incoming s capacity first old anchors).enabled := by
  have ha:=MaskedClusterLeaders.shorten_invariant capacity old fresh s hi hf hc hle
  have hbound:=MaskedClusterLeaders.live_bound capacity old fresh s hi hc
  have hs:=MaskedTraversalDirty.live_spec s.leaders (MaskedClusterLeaders.shorten capacity fresh s).state.leaders capacity
    (MaskedClusterLeaders.shorten capacity fresh s).live dirty hv hi.leadGood hi.leadFits ha.leadGood ha.leadFits hc
    (fun e he=>by have hh:=hbound e he; omega)
  apply retained_transport s (MaskedClusterLeaders.shorten capacity fresh s).state capacity n old fresh first f anchors
    _ hi ha hc (by intro p hp; exact hp) _
    (MaskedTraversalRetained.crossing_away capacity n old fresh s f anchors dirty hv hi hf hc hle hb) hm hn
  intro x hx
  apply crossing_describe_unmarked capacity old fresh x s dirty hv hi hf hc hle
  intro hh
  exact hx (hs.1.2.2.mem_iff.mpr hh)

/-- Once structural transport is known, the actual two-pass reset keeps
the same incoming data outside its computed current successor set. -/
theorem reset_preserves_transport (before after : MaskedClusterLeaders.State h)
    (capacity old fresh first : Nat) (anchors : Array (Option Nat)) (keys : List Nat)
    (ha : MaskedClusterLeaders.Invariant fresh after) (hc : capacity=2^h)
    (hm : first∈after.leaders.entries)
    (hn : first∉(successors after.leaders capacity keys (MaskedTraversalDirty.empty h)).keys.tree.entries)
    (he : (incoming after capacity first fresh anchors).cursor=(incoming before capacity first old anchors).cursor ∧
      (incoming after capacity first fresh anchors).enabled=(incoming before capacity first old anchors).enabled) :
    (incoming after capacity first fresh (MaskedTraversalRepair.anchorsLoop fresh keys anchors 0).1).cursor=
      (incoming before capacity first old anchors).cursor ∧
    (incoming after capacity first fresh (MaskedTraversalRepair.anchorsLoop fresh keys anchors 0).1).enabled=
      (incoming before capacity first old anchors).enabled := by
  rw [incoming_unchanged after capacity fresh first anchors keys ha hc hm hn]
  exact he

end REWB.MaskedTraversalIncoming
