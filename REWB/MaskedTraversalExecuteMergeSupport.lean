import REWB.MaskedTraversalExecuteSupport

/-! Every actual light-import patch has physical support in the merged
frontier. This proves sparse repair writes cannot escape that subtree;
neither the old nor the new signed neighbor list is assumed to be an
externally supplied affected-key set.
-/
namespace REWB.MaskedTraversalExecute
open REWB.MaskedTraversalFrontier REWB.MaskedTraversalDirty
variable {h : Nat}

def PatchSupported (P : Nat→Prop) (patch : Patch h) : Prop :=
  P patch.position ∧ (∀p,p∈patch.before.state.occurrences.entries→P p) ∧
    ∀p,p∈patch.update.frontier.state.occurrences.entries→P p

theorem import_support (capacity L : Nat) (ps : List Nat) (out : Imported h)
    (hv : out.frontier.Valid L) (hc : capacity=2^h) (hb : ∀p,p∈ps→p<capacity)
    (P : Nat→Prop) (hps : ∀p,p∈ps→P p)
    (hocc : ∀p,p∈out.frontier.state.occurrences.entries→P p)
    (hpatch : ∀patch,patch∈out.revPatches→PatchSupported P patch) :
    (∀p,p∈(importLoop capacity L ps out).frontier.state.occurrences.entries→P p) ∧
    ∀patch,patch∈(importLoop capacity L ps out).revPatches→PatchSupported P patch := by
  induction ps generalizing out with
  | nil=>exact ⟨hocc,hpatch⟩
  | cons p ps ih=>
    have bound:=hb p List.mem_cons_self
    have next:=insert_valid capacity L p out.frontier hv hc bound
    have inserted : ∀q,q∈(insert capacity L p out.frontier).frontier.state.occurrences.entries→P q := by
      intro q hq
      rcases (insert_mem capacity L p q out.frontier hv hc bound).mp hq with heq|hq
      · rw [heq]
        exact hps p List.mem_cons_self
      · exact hocc q hq
    apply ih (push capacity L p out) next (fun q hq=>hb q (List.mem_cons_of_mem p hq))
      (fun q hq=>hps q (List.mem_cons_of_mem p hq)) inserted
    intro patch hp
    change patch∈⟨p,out.frontier,insert capacity L p out.frontier⟩::out.revPatches at hp
    rcases List.mem_cons.mp hp with rfl|hp
    · exact ⟨hps p List.mem_cons_self,hocc,inserted⟩
    · exact hpatch patch hp

theorem merge_patches_supported (capacity L : Nat) (left right : Frontier h)
    (hl : left.Valid L) (hr : right.Valid L) (hc : capacity=2^h)
    (P : Nat→Prop) (hleft : ∀p,p∈left.state.occurrences.entries→P p)
    (hright : ∀p,p∈right.state.occurrences.entries→P p) :
    ∀patch,patch∈(MaskedTraversalFrontier.merge capacity L left right).revPatches→PatchSupported P patch := by
  unfold MaskedTraversalFrontier.merge
  split
  · exact (import_support capacity L left.positions (MaskedTraversalFrontier.initial right) hr hc
      (fun p hp=>by have hh:=hl.bounded p hp; omega) P
      (fun p hp=>hleft p (hl.positions.mem_iff.mp hp)) hright (by intro patch hp; cases hp)).2
  · exact (import_support capacity L right.positions (MaskedTraversalFrontier.initial left) hl hc
      (fun p hp=>by have hh:=hr.bounded p hp; omega) P
      (fun p hp=>hright p (hr.positions.mem_iff.mp hp)) hleft (by intro patch hp; cases hp)).2

theorem merge_dirty_supported (capacity L : Nat) (left right : Frontier h)
    (dirty : MaskedTraversalDirty.Marked h) (hv : dirty.keys.Valid)
    (hl : left.Valid L) (hr : right.Valid L) (hc : capacity=2^h)
    (hd : DirtySupported
      (if (MaskedTraversalFrontier.merge capacity L left right).keptLeft then left.state.occurrences.entries else right.state.occurrences.entries) dirty) :
    DirtySupported (MaskedTraversalFrontier.merge capacity L left right).frontier.state.occurrences.entries
      (patches capacity (MaskedTraversalFrontier.merge capacity L left right).revPatches dirty) := by
  have valid:=MaskedTraversalDirty.merge_patches capacity L left right hl hr hc
  have spec:=patches_spec capacity L (MaskedTraversalFrontier.merge capacity L left right).revPatches dirty hv hc valid
  have supported:=merge_patches_supported capacity L left right hl hr hc
    (fun p=>p∈(MaskedTraversalFrontier.merge capacity L left right).frontier.state.occurrences.entries)
    (fun p hp=>(merge_mem capacity L left right hl hr hc p).mpr (Or.inl hp))
    (fun p hp=>(merge_mem capacity L left right hl hr hc p).mpr (Or.inr hp))
  intro p hp
  rcases (spec.2.1 p).mp (spec.1.2.2.mem_iff.mp hp) with ⟨patch,hm,hp⟩|hp
  · obtain ⟨before,bound,eq⟩:=valid patch hm
    have after : patch.update.frontier.Valid L := by rw [eq]; exact insert_valid capacity L patch.position patch.before before hc bound
    have support:=supported patch hm
    exact change_supported patch.before.state.leaders patch.update.frontier.state.leaders capacity patch.position _
      before.invariant.leadGood before.invariant.leadFits after.invariant.leadGood after.invariant.leadFits hc
      (fun q hq=>support.2.1 q ((before.invariant.represented q).mp hq).1)
      (fun q hq=>support.2.2 q ((after.invariant.represented q).mp hq).1) support.1 p hp
  · have hold:=hd p (hv.2.2.mem_iff.mpr hp)
    apply (merge_mem capacity L left right hl hr hc p).mpr
    split at hold
    · exact Or.inl hold
    · exact Or.inr hold

end REWB.MaskedTraversalExecute
