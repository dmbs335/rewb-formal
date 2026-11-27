import REWB.BoundaryApplicationRTable

/-! Pointwise semantics of the two operations used on fixed-end heavy
paths: inject D colors through a node's materialized acceptance rows,
and pull A subsets backwards through a materialized edge transition. -/
namespace REWB.BoundaryApplication.Subset
open REWB.BoundaryIndex
open REWB.BoundaryIndex.Merge
variable {σ m h : Nat}

abbrev count (A : DFA (Fin σ)) := (Colors.colorSpace A).enumeration.elems.length

def Selected (A : DFA (Fin σ)) (tree : BoundaryIndex.Tree (count A) m h)
    (i : Position h) (alpha : Fin A.stateCount) (q : Fin m) : Prop :=
  ∃c,Colors.select A alpha c=true ∧ (point tree i).active c q=true

theorem imported_selected (A D : DFA (Fin σ)) (g : Vector (Colors.Color A) D.stateCount)
    (source : BoundaryIndex.Tree D.stateCount m h) (is : List (Position h))
    (dest : Merge.State (count A) m h) (i : Position h) (alpha : Fin A.stateCount) (q : Fin m) :
    Selected A (Lift.importMany g source is dest).1.tree i alpha q ↔
      Selected A dest.tree i alpha q ∨
        (i∈is ∧ ∃delta,Colors.select A alpha (g.get delta)=true ∧ (point source i).active delta q=true) := by
  unfold Selected
  constructor
  · rintro ⟨c,hc,ha⟩
    rcases (Lift.loop_active g source is dest 0 i c q).mp ha with hd | ⟨hi,old,he,ho⟩
    · exact Or.inl ⟨c,hc,hd⟩
    · exact Or.inr ⟨hi,old,by rw [he]; exact hc,ho⟩
  · rintro (⟨c,hc,ha⟩ | ⟨hi,old,hc,ha⟩)
    · exact ⟨c,hc,(Lift.loop_active g source is dest 0 i c q).mpr (Or.inl ha)⟩
    · exact ⟨g.get old,hc,(Lift.loop_active g source is dest 0 i _ q).mpr (Or.inr ⟨hi,old,rfl,ha⟩)⟩

theorem recolored_selected (A : DFA (Fin σ)) (tr : Range.Map A.stateCount)
    (dest : Merge.State (count A) m h) (i : Position h) (alpha : Fin A.stateCount) (q : Fin m) :
    Selected A (Merge.recolor (Colors.preimageMap A tr) dest).1.tree i alpha q ↔
      Selected A dest.tree i (tr.get alpha) q := by
  unfold Selected
  change (∃c,Colors.select A alpha c=true ∧
    (point (Tree.recolor (Colors.preimageMap A tr) dest.tree).1 i).active c q=true) ↔ _
  simp only [point_recolor,View.rename_active]
  constructor
  · rintro ⟨c,hc,old,he,ho⟩
    refine ⟨old,?_,ho⟩
    rw [← Colors.selected_preimage A tr old alpha,he]
    exact hc
  · rintro ⟨old,hc,ho⟩
    exact ⟨(Colors.preimageMap A tr).get old,by rw [Colors.selected_preimage]; exact hc,old,rfl,ho⟩

theorem node_import_selected (A B D : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (t : TrieFor w) (hg : t.Good (reverseText w fallback)) (hn : t.leaves≠[])
    (source : BoundaryIndex.Tree D.stateCount m h) (is : List (Position h))
    (dest : Merge.State (count A) m h) (i : Position h) (alpha : Fin A.stateCount) (q : Fin m) :
    Selected A (Lift.importMany (RTable.node A B D w (RTable.prepare A B D w) t).map source is dest).1.tree i alpha q ↔
      Selected A dest.tree i alpha q ∨
        (i∈is ∧ ∃delta,BoundaryIndex.FixedEnd.Predicate A B D w
          (w.length-(representative w t).start) t.depth 0 t.depth alpha delta ∧
          (point source i).active delta q=true) := by
  rw [imported_selected]
  simp only [RTable.node_correct A B D w fallback t hg hn]

end REWB.BoundaryApplication.Subset
