import REWB.BoundaryApplicationQuery

/-! Import listed endpoints while changing the finite color space.
This is used for D-state colors becoming A-subset colors. Conversion
materializes the finite table at each imported position, then unions it
with the retained path index. It never traverses retained endpoints. -/
namespace REWB.BoundaryApplication.Lift
open REWB.BoundaryIndex
open REWB.BoundaryIndex.Merge
open REWB.FiniteRelation
variable {k₁ k₂ m h : Nat}

def renameView (g : Fin k₁→Fin k₂) (a : View k₁ m) : View k₂ m :=
  ⟨a.trans,fun c q=>any (finEnum k₁) (fun old=>decide (g old=c) && a.active old q)⟩

theorem renameView_active (g : Fin k₁→Fin k₂) (a : View k₁ m) (c : Fin k₂) (q : Fin m) :
    (renameView g a).active c q=true ↔ ∃old,g old=c ∧ a.active old q=true := by
  simp only [renameView,any_true,Bool.and_eq_true,decide_eq_true_eq]

def rename (g : Vector (Fin k₂) k₁) (a : Table k₁ m) : Table k₂ m×Nat :=
  let cells:=Vector.ofFn fun c : Fin k₂=>Vector.ofFn fun q : Fin m=>
    Counted.scan (fun old : Fin k₁=>decide (g.get old=c) && a.view.active old q) (List.ofFn id)
  let bits:=Vector.ofFn fun c=>Vector.ofFn fun q=>(cells.get c |>.get q).1
  (⟨a.trans,bits⟩,(List.ofFn fun c=>Counted.rowWork (cells.get c)).sum)

theorem rename_view (g : Vector (Fin k₂) k₁) (a : Table k₁ m) :
    (rename g a).1.view=renameView g.get a.view := by
  apply View.ext
  · rfl
  · funext c q
    simp only [rename,Table.view,Table.get_ofFn,renameView,Counted.scan_value,any,finEnum]

theorem rename_steps (g : Vector (Fin k₂) k₁) (a : Table k₁ m) :
    (rename g a).2=k₂*(m*(k₁+1)) := by
  unfold rename
  simp only [Table.get_ofFn]
  have hh (c : Fin k₂) : Counted.rowWork (Vector.ofFn fun q : Fin m=>
      Counted.scan (fun old : Fin k₁=>decide (g.get old=c) && a.view.active old q)
        (List.ofFn id))=m*(k₁+1) := by
    apply Counted.rowWork_uniform
    intro q
    simp only [Table.get_ofFn,Counted.scan_steps,List.length_ofFn]
  simp only [hh]
  exact Counted.sum_ofFn_const k₂ (m*(k₁+1))

def Active (g : Vector (Fin k₂) k₁) (source : BoundaryIndex.Tree k₁ m h)
    (i : Position h) (c : Fin k₂) (q : Fin m) : Prop :=
  ∃old,g.get old=c ∧ (point source i).active old q=true

def importOne (g : Vector (Fin k₂) k₁) (source : BoundaryIndex.Tree k₁ m h)
    (dest : BoundaryIndex.Tree k₂ m h) (i : Position h) : BoundaryIndex.Tree k₂ m h×Nat :=
  let src:=Tree.get source i.val
  let dst:=Tree.get dest i.val
  let converted:=rename g src.1
  let cell:=unionCell dst.1 converted.1
  let out:=Tree.replace dest i.val cell.1
  (out.1,src.2+dst.2+converted.2+cell.2+out.2+1)

theorem importOne_good (g : Vector (Fin k₂) k₁) (source : BoundaryIndex.Tree k₁ m h)
    (dest : BoundaryIndex.Tree k₂ m h) (hd : Tree.Good dest) (i : Position h) :
    Tree.Good (importOne g source dest i).1 := Tree.replace_good _ hd _ _

theorem importOne_point (g : Vector (Fin k₂) k₁) (source : BoundaryIndex.Tree k₁ m h)
    (dest : BoundaryIndex.Tree k₂ m h) (i j : Position h) :
    point (importOne g source dest i).1 j=
      if i=j then unionView (point dest i) (renameView g.get (point source i)) else point dest j := by
  simp only [importOne,point_replace,unionCell_view,rename_view]
  rfl

theorem importOne_trans (g : Vector (Fin k₂) k₁) (source : BoundaryIndex.Tree k₁ m h)
    (dest : BoundaryIndex.Tree k₂ m h) (i j : Position h) :
    (point (importOne g source dest i).1 j).trans=(point dest j).trans := by
  rw [importOne_point]
  split
  next he => subst j; rfl
  next he => rfl

theorem importOne_active (g : Vector (Fin k₂) k₁) (source : BoundaryIndex.Tree k₁ m h)
    (dest : BoundaryIndex.Tree k₂ m h) (i j : Position h) (c : Fin k₂) (q : Fin m) :
    (point (importOne g source dest i).1 j).active c q=true ↔
      (point dest j).active c q=true ∨ (j=i ∧ Active g source j c q) := by
  rw [importOne_point]
  by_cases he : i=j
  · subst j
    simp only [if_pos rfl,if_true,unionView,Bool.or_eq_true,renameView_active,true_and,Active]
  · simp only [if_neg he,Ne.symm he,false_and,or_false]

def budget (k₁ k₂ m h : Nat) : Nat :=
  (h+1)*(Tree.getBudget k₁ m+Tree.getBudget k₂ m+Tree.replaceBudget k₂ m)+k₂*(m*(k₁+1))+k₂*m+3

theorem importOne_steps (g : Vector (Fin k₂) k₁) (source : BoundaryIndex.Tree k₁ m h)
    (dest : BoundaryIndex.Tree k₂ m h) (i : Position h) :
    (importOne g source dest i).2+2≤budget k₁ k₂ m h := by
  have hs:=Tree.get_steps source i.val
  have hd:=Tree.get_steps dest i.val
  have hr:=Tree.replace_steps dest i.val
    (unionCell (Tree.get dest i.val).1 (rename g (Tree.get source i.val).1).1).1
  simp only [importOne,rename_steps]
  change (Tree.get source i.val).2+(Tree.get dest i.val).2+k₂*(m*(k₁+1))+k₂*m+
    (Tree.replace dest i.val (unionCell (Tree.get dest i.val).1 (rename g (Tree.get source i.val).1).1).1).2+1+2≤_
  unfold budget
  simp only [Nat.mul_add]
  omega

def loop (g : Vector (Fin k₂) k₁) (source : BoundaryIndex.Tree k₁ m h) :
    List (Position h)→Merge.State k₂ m h→Nat→Merge.State k₂ m h×Nat
  | [],dest,work => (dest,work)
  | i::is,dest,work =>
    let out:=importOne g source dest.tree i
    let next : Merge.State k₂ m h:=⟨out.1,i::dest.positions,dest.cachedSize+1⟩
    loop g source is next (work+out.2+2)

def importMany (g : Vector (Fin k₂) k₁) (source : BoundaryIndex.Tree k₁ m h)
    (is : List (Position h)) (dest : Merge.State k₂ m h) : Merge.State k₂ m h×Nat :=
  loop g source is dest 0

theorem loop_positions (g : Vector (Fin k₂) k₁) (source : BoundaryIndex.Tree k₁ m h)
    (is : List (Position h)) (dest : Merge.State k₂ m h) (work : Nat) :
    (loop g source is dest work).1.positions=is.reverse++dest.positions := by
  induction is generalizing dest work with
  | nil => rfl
  | cons i is ih => simp only [loop,ih,List.reverse_cons,List.append_assoc,List.singleton_append]

theorem loop_size (g : Vector (Fin k₂) k₁) (source : BoundaryIndex.Tree k₁ m h)
    (is : List (Position h)) (dest : Merge.State k₂ m h) (work : Nat) :
    (loop g source is dest work).1.cachedSize=dest.cachedSize+is.length := by
  induction is generalizing dest work with
  | nil => simp [loop]
  | cons i is ih => simp only [loop,ih,List.length_cons]; omega

theorem loop_good (g : Vector (Fin k₂) k₁) (source : BoundaryIndex.Tree k₁ m h)
    (is : List (Position h)) (dest : Merge.State k₂ m h) (work : Nat) (hg : Tree.Good dest.tree) :
    Tree.Good (loop g source is dest work).1.tree := by
  induction is generalizing dest work with
  | nil => exact hg
  | cons i is ih => exact ih _ _ (importOne_good _ _ _ hg _)

theorem loop_trans (g : Vector (Fin k₂) k₁) (source : BoundaryIndex.Tree k₁ m h)
    (is : List (Position h)) (dest : Merge.State k₂ m h) (work : Nat) (j : Position h) :
    (point (loop g source is dest work).1.tree j).trans=(point dest.tree j).trans := by
  induction is generalizing dest work with
  | nil => rfl
  | cons i is ih => simp only [loop,ih,importOne_trans]

theorem loop_active (g : Vector (Fin k₂) k₁) (source : BoundaryIndex.Tree k₁ m h)
    (is : List (Position h)) (dest : Merge.State k₂ m h) (work : Nat)
    (j : Position h) (c : Fin k₂) (q : Fin m) :
    (point (loop g source is dest work).1.tree j).active c q=true ↔
      (point dest.tree j).active c q=true ∨ (j∈is ∧ Active g source j c q) := by
  induction is generalizing dest work with
  | nil => simp [loop]
  | cons i is ih =>
    simp only [loop,ih,importOne_active,List.mem_cons]
    constructor
    · rintro ((hd | ⟨he,hs⟩) | ⟨hm,hs⟩)
      · exact Or.inl hd
      · exact Or.inr ⟨Or.inl he,hs⟩
      · exact Or.inr ⟨Or.inr hm,hs⟩
    · rintro (hd | ⟨he|hm,hs⟩)
      · exact Or.inl (Or.inl hd)
      · exact Or.inl (Or.inr ⟨he,hs⟩)
      · exact Or.inr ⟨hm,hs⟩

theorem loop_steps (g : Vector (Fin k₂) k₁) (source : BoundaryIndex.Tree k₁ m h)
    (is : List (Position h)) (dest : Merge.State k₂ m h) (work : Nat) :
    (loop g source is dest work).2≤work+is.length*budget k₁ k₂ m h := by
  induction is generalizing dest work with
  | nil => simp [loop]
  | cons i is ih =>
    have hs:=importOne_steps g source dest.tree i
    have hr:=ih ⟨(importOne g source dest.tree i).1,i::dest.positions,dest.cachedSize+1⟩
      (work+(importOne g source dest.tree i).2+2)
    change (loop g source is _ _).2≤_
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem importMany_steps (g : Vector (Fin k₂) k₁) (source : BoundaryIndex.Tree k₁ m h)
    (is : List (Position h)) (dest : Merge.State k₂ m h) :
    (importMany g source is dest).2≤is.length*budget k₁ k₂ m h := by
  simpa only [Nat.zero_add] using loop_steps g source is dest 0

theorem importMany_positions (g : Vector (Fin k₂) k₁) (source : BoundaryIndex.Tree k₁ m h)
    (is : List (Position h)) (dest : Merge.State k₂ m h) :
    (importMany g source is dest).1.positions=is.reverse++dest.positions := loop_positions _ _ _ _ _

theorem importMany_size (g : Vector (Fin k₂) k₁) (source : BoundaryIndex.Tree k₁ m h)
    (is : List (Position h)) (dest : Merge.State k₂ m h) :
    (importMany g source is dest).1.cachedSize=dest.cachedSize+is.length := loop_size _ _ _ _ _

theorem importMany_trans (g : Vector (Fin k₂) k₁) (source : BoundaryIndex.Tree k₁ m h)
    (is : List (Position h)) (dest : Merge.State k₂ m h) (j : Position h) :
    (point (importMany g source is dest).1.tree j).trans=(point dest.tree j).trans := loop_trans _ _ _ _ _ _

/-- The source may be a full node version while `is` is only its light
child's maintained record list. Only those listed records are imported. -/
theorem importMany_valid_of_live (g : Vector (Fin k₂) k₁) (source : BoundaryIndex.Tree k₁ m h)
    (is : List (Position h)) (dest : Merge.State k₂ m h) (hd : Valid dest)
    (hlive : ∀i,i∈is→∃c q,(point source i).active c q=true) :
    Valid (importMany g source is dest).1 := by
  refine ⟨loop_good _ _ _ _ _ hd.1,?_,?_⟩
  · rw [importMany_size,importMany_positions,List.length_append,List.length_reverse,hd.2.1]
    omega
  · intro j
    rw [importMany_positions,List.mem_append,List.mem_reverse]
    constructor
    · rintro (hj | hj)
      · obtain ⟨c,q,hc⟩:=hlive j hj
        refine ⟨g.get c,q,?_⟩
        exact (loop_active g source is dest 0 j _ q).mpr (Or.inr ⟨hj,c,rfl,hc⟩)
      · obtain ⟨c,q,hc⟩:=(hd.2.2 j).mp hj
        exact ⟨c,q,(loop_active g source is dest 0 j c q).mpr (Or.inl hc)⟩
    · rintro ⟨c,q,hc⟩
      rcases (loop_active g source is dest 0 j c q).mp hc with hd' | ⟨hj,_⟩
      · exact Or.inr ((hd.2.2 j).mpr ⟨c,q,hd'⟩)
      · exact Or.inl hj

theorem importMany_active (g : Vector (Fin k₂) k₁) (source : Merge.State k₁ m h)
    (dest : Merge.State k₂ m h) (hs : Valid source) (j : Position h) (c : Fin k₂) (q : Fin m) :
    (point (importMany g source.tree source.positions dest).1.tree j).active c q=true ↔
      (point dest.tree j).active c q=true ∨ Active g source.tree j c q := by
  rw [importMany,loop_active]
  constructor
  · rintro (hd | ⟨_,hl⟩)
    · exact Or.inl hd
    · exact Or.inr hl
  · rintro (hd | ⟨old,he,ha⟩)
    · exact Or.inl hd
    · exact Or.inr ⟨(hs.2.2 j).mpr ⟨old,q,ha⟩,old,he,ha⟩

theorem importMany_valid (g : Vector (Fin k₂) k₁) (source : Merge.State k₁ m h)
    (dest : Merge.State k₂ m h) (hs : Valid source) (hd : Valid dest) :
    Valid (importMany g source.tree source.positions dest).1 := by
  refine ⟨loop_good _ _ _ _ _ hd.1,?_,?_⟩
  · simp only [importMany,loop_size,loop_positions,List.length_append,List.length_reverse,hd.2.1]
    omega
  · intro j
    have hp:=loop_positions g source.tree source.positions dest 0
    change (importMany g source.tree source.positions dest).1.positions=source.positions.reverse++dest.positions at hp
    rw [hp,List.mem_append,List.mem_reverse,hs.2.2 j,hd.2.2 j]
    constructor
    · rintro (⟨c,q,hc⟩ | ⟨c,q,hc⟩)
      · exact ⟨g.get c,q,(importMany_active g source dest hs j _ q).mpr (Or.inr ⟨c,rfl,hc⟩)⟩
      · exact ⟨c,q,(importMany_active g source dest hs j c q).mpr (Or.inl hc)⟩
    · rintro ⟨c,q,hc⟩
      rcases (importMany_active g source dest hs j c q).mp hc with hd | ⟨old,_,ha⟩
      · exact Or.inr ⟨c,q,hd⟩
      · exact Or.inl ⟨old,q,ha⟩

end REWB.BoundaryApplication.Lift
