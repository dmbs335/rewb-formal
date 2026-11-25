import REWB.MaskedTraversalNeighborThreshold

/-! Accumulation over the actual recorded import sequence. Descriptor
preservation is proved for the executed import loop and its real dirty
set, then for the heavy side selected by the cached-count merge. Equal
depth refinements are included; no completed-class assumption is used.
-/
namespace REWB.MaskedTraversalNeighbor
open REWB.MaskedClusterDescriptor REWB.MaskedTraversalFrontier
variable {h : Nat}

theorem old_patch_mem (capacity L : Nat) (ps : List Nat) (out : Imported h) (patch : Patch h)
    (hp : patch∈out.revPatches) : patch∈(importLoop capacity L ps out).revPatches := by
  induction ps generalizing out with
  | nil => exact hp
  | cons p ps ih =>
    rw [importLoop]
    apply ih (push capacity L p out)
    exact List.mem_cons_of_mem _ hp

theorem importLoop_describe_away (capacity L x : Nat) (ps : List Nat) (out : Imported h)
    (hv : out.frontier.Valid L) (hc : capacity=2^h) (hb : ∀p,p∈ps→p<capacity)
    (hn : ∀patch,patch∈(importLoop capacity L ps out).revPatches→
      x∉(MaskedTraversalDirty.prepareChange patch.before.state.leaders patch.update.frontier.state.leaders
        capacity patch.position).keys) :
    (describeLeader (importLoop capacity L ps out).frontier.state capacity x).1=
      (describeLeader out.frontier.state capacity x).1 := by
  induction ps generalizing out with
  | nil => rfl
  | cons p ps ih =>
    have hp:=hb p List.mem_cons_self
    have hnext:=insert_valid capacity L p out.frontier hv hc hp
    have ht:=ih (push capacity L p out) hnext (fun q hq=>hb q (List.mem_cons_of_mem p hq)) hn
    have hpatch : (⟨p,out.frontier,insert capacity L p out.frontier⟩ : Patch h)∈
        (importLoop capacity L (p::ps) out).revPatches :=
      old_patch_mem capacity L ps (push capacity L p out) _ List.mem_cons_self
    have hnone:=hn _ hpatch
    have hs:=add_describe_away out.frontier.state capacity L p x hv.invariant hc hp hnone
    exact ht.trans hs

theorem importLoop_describe_unmarked (capacity L x : Nat) (ps : List Nat) (out : Imported h)
    (dirty : MaskedTraversalDirty.Marked h) (hd : dirty.keys.Valid)
    (hv : out.frontier.Valid L) (hc : capacity=2^h) (hb : ∀p,p∈ps→p<capacity)
    (hp : ∀p,p∈out.revPatches→MaskedTraversalDirty.PatchValid capacity L p)
    (hn : x∉(MaskedTraversalDirty.patches capacity (importLoop capacity L ps out).revPatches dirty).keys.tree.entries) :
    (describeLeader (importLoop capacity L ps out).frontier.state capacity x).1=
      (describeLeader out.frontier.state capacity x).1 := by
  have hp':=MaskedTraversalDirty.importLoop_patches capacity L ps out hv hc hb hp
  have hs:=MaskedTraversalDirty.patches_spec capacity L (importLoop capacity L ps out).revPatches dirty hd hc hp'
  apply importLoop_describe_away capacity L x ps out hv hc hb
  intro patch hpatch hx
  apply hn
  apply (hs.2.1 x).mpr
  exact Or.inl ⟨patch,hpatch,hx⟩

theorem merge_describe_unmarked (capacity L x : Nat) (left right : Frontier h)
    (dirty : MaskedTraversalDirty.Marked h) (hd : dirty.keys.Valid)
    (hl : left.Valid L) (hr : right.Valid L) (hc : capacity=2^h)
    (hn : x∉(MaskedTraversalDirty.patches capacity
      (MaskedTraversalFrontier.merge capacity L left right).revPatches dirty).keys.tree.entries) :
    (describeLeader (MaskedTraversalFrontier.merge capacity L left right).frontier.state capacity x).1=
      (describeLeader
        (if (MaskedTraversalFrontier.merge capacity L left right).keptLeft then left.state else right.state) capacity x).1 := by
  by_cases hsize : left.state.occurrences.count≤right.state.occurrences.count
  · simp only [MaskedTraversalFrontier.merge,hsize,if_true,Bool.false_eq_true,if_false] at hn ⊢
    exact importLoop_describe_unmarked capacity L x left.positions (initial right) dirty hd hr hc
      (fun p hp=>by have hb:=hl.bounded p hp; omega) (by intro p hp; cases hp) hn
  · simp only [MaskedTraversalFrontier.merge,hsize,if_false,if_true] at hn ⊢
    exact importLoop_describe_unmarked capacity L x right.positions (initial left) dirty hd hl hc
      (fun p hp=>by have hb:=hr.bounded p hp; omega) (by intro p hp; cases hp) hn

end REWB.MaskedTraversalNeighbor
