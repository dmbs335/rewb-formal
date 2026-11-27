import REWB.BoundaryIndexTree

/-! Persistent union by importing only the listed light positions.

Every import reads one light and one heavy leaf, unions their materialized
active cells, preserves the heavy leaf's static letter transition, and
replaces only that leaf. The maintained position list is extended by cons;
neither the heavy list nor the heavy tree's leaves are scanned or copied.
A cached size supports a constant-time choice of retained child. -/
namespace REWB.BoundaryIndex.Merge
variable {k m h : Nat}

abbrev Position (h : Nat) := Fin (2^h)

def point (t : Tree k m h) (i : Position h) : View k m := (Tree.get t i.val).1.view

theorem point_replace (t : Tree k m h) (i j : Position h) (a : Table k m) :
    point (Tree.replace t i.val a).1 j=if i=j then a.view else point t j := by
  have hh := Tree.get_correct (Tree.replace t i.val a).1 j.val j.isLt
  rw [Tree.replace_leaves,List.getElem?_set] at hh
  by_cases he : i=j
  · subst j
    simp only [Tree.leaves_length,i.isLt,if_true,Option.some.injEq] at hh
    simp only [point,if_pos rfl]
    exact hh.symm
  · have hn : i.val≠j.val := fun hx=>he (Fin.ext hx)
    rw [if_neg hn,Tree.get_correct t j.val j.isLt] at hh
    simp only [if_neg he,point]
    exact (Option.some.inj hh).symm

theorem point_recolor (g : Vector (Fin k) k) (t : Tree k m h) (i : Position h) :
    point (Tree.recolor g t).1 i=View.rename g.get (point t i) := by
  have hh := Tree.get_correct (Tree.recolor g t).1 i.val i.isLt
  rw [Tree.recolor_leaves,List.getElem?_map,Tree.get_correct t i.val i.isLt] at hh
  exact (Option.some.inj hh).symm

/-- Both indexes describe the same static text. Only active cells are
united; copying a light transition would duplicate or replace text. -/
def unionCell (heavy light : Table k m) : Table k m×Nat :=
  (⟨heavy.trans,Vector.ofFn (fun c=>Vector.ofFn (fun q=>
    heavy.view.active c q || light.view.active c q))⟩,k*m)

def unionView (heavy light : View k m) : View k m :=
  ⟨heavy.trans,fun c q=>heavy.active c q || light.active c q⟩

theorem unionCell_view (heavy light : Table k m) :
    (unionCell heavy light).1.view=unionView heavy.view light.view := by
  apply View.ext
  · rfl
  · funext c q
    simp only [unionCell,unionView,Table.view,Table.get_ofFn]

def importOne (light heavy : Tree k m h) (i : Position h) : Tree k m h×Nat :=
  let src := Tree.get light i.val
  let dst := Tree.get heavy i.val
  let cell := unionCell dst.1 src.1
  let out := Tree.replace heavy i.val cell.1
  (out.1,src.2+dst.2+cell.2+out.2+1)

theorem importOne_good (light heavy : Tree k m h) (hh : Tree.Good heavy) (i : Position h) :
    Tree.Good (importOne light heavy i).1 := Tree.replace_good _ hh _ _

theorem importOne_point (light heavy : Tree k m h) (i j : Position h) :
    point (importOne light heavy i).1 j=
      if i=j then unionView (point heavy i) (point light i) else point heavy j := by
  simp only [importOne,point_replace,unionCell_view]
  rfl

theorem importOne_trans (light heavy : Tree k m h) (i j : Position h) :
    (point (importOne light heavy i).1 j).trans=(point heavy j).trans := by
  rw [importOne_point]
  split
  next he => subst j; rfl
  next he => rfl

theorem importOne_active (light heavy : Tree k m h) (i j : Position h)
    (c : Fin k) (q : Fin m) :
    (point (importOne light heavy i).1 j).active c q=true ↔
      (point heavy j).active c q=true ∨ (j=i ∧ (point light j).active c q=true) := by
  rw [importOne_point]
  by_cases he : i=j
  · subst j
    simp only [if_pos rfl,if_true,unionView,Bool.or_eq_true,true_and]
  · rw [if_neg he]
    simp only [Ne.symm he,false_and,or_false]

/-- The import-loop budget includes both leaf reads, one union, one
persistent replacement, a position-list cons and its cached-size update. -/
def importBudget (k m h : Nat) : Nat :=
  (h+1)*(2*Tree.getBudget k m+Tree.replaceBudget k m)+k*m+3

theorem importOne_steps (light heavy : Tree k m h) (i : Position h) :
    (importOne light heavy i).2+2≤importBudget k m h := by
  have hs := Tree.get_steps light i.val
  have hd := Tree.get_steps heavy i.val
  have hr := Tree.replace_steps heavy i.val (unionCell (Tree.get heavy i.val).1 (Tree.get light i.val).1).1
  change (Tree.get light i.val).2+(Tree.get heavy i.val).2+k*m+
    (Tree.replace heavy i.val (unionCell (Tree.get heavy i.val).1 (Tree.get light i.val).1).1).2+1+2≤_
  unfold importBudget
  simp only [Nat.mul_add,Nat.mul_left_comm (h+1) 2,Nat.two_mul]
  omega

structure State (k m h : Nat) where
  tree : Tree k m h
  positions : List (Position h)
  cachedSize : Nat

/-- A position is listed exactly when the leaf has at least one live
color/state pair. Duplicate input positions may be represented repeatedly;
distinct program leaves give a duplicate-free list. -/
def Valid (s : State k m h) : Prop :=
  Tree.Good s.tree ∧ s.cachedSize=s.positions.length ∧
    ∀ i, i∈s.positions ↔ ∃ c q, (point s.tree i).active c q=true

def importLoop (light : Tree k m h) : List (Position h)→State k m h→Nat→State k m h×Nat
  | [],heavy,work => (heavy,work)
  | i::is,heavy,work =>
    let out := importOne light heavy.tree i
    let next : State k m h := ⟨out.1,i::heavy.positions,heavy.cachedSize+1⟩
    importLoop light is next (work+out.2+2)

def importMany (light : Tree k m h) (positions : List (Position h)) (heavy : State k m h) :
    State k m h×Nat := importLoop light positions heavy 0

theorem importLoop_positions (light : Tree k m h) (is : List (Position h))
    (heavy : State k m h) (work : Nat) :
    (importLoop light is heavy work).1.positions=is.reverse++heavy.positions := by
  induction is generalizing heavy work with
  | nil => rfl
  | cons i is ih =>
    simp only [importLoop,ih,List.reverse_cons,List.append_assoc,List.singleton_append]

theorem importLoop_size (light : Tree k m h) (is : List (Position h))
    (heavy : State k m h) (work : Nat) :
    (importLoop light is heavy work).1.cachedSize=heavy.cachedSize+is.length := by
  induction is generalizing heavy work with
  | nil => simp [importLoop]
  | cons i is ih =>
    simp only [importLoop,ih,List.length_cons]
    omega

theorem importLoop_good (light : Tree k m h) (is : List (Position h))
    (heavy : State k m h) (work : Nat) (hg : Tree.Good heavy.tree) :
    Tree.Good (importLoop light is heavy work).1.tree := by
  induction is generalizing heavy work with
  | nil => exact hg
  | cons i is ih => exact ih _ _ (importOne_good _ _ hg _)

theorem importLoop_trans (light : Tree k m h) (is : List (Position h))
    (heavy : State k m h) (work : Nat) (j : Position h) :
    (point (importLoop light is heavy work).1.tree j).trans=(point heavy.tree j).trans := by
  induction is generalizing heavy work with
  | nil => rfl
  | cons i is ih =>
    simp only [importLoop,ih,importOne_trans]

theorem importLoop_active (light : Tree k m h) (is : List (Position h))
    (heavy : State k m h) (work : Nat) (j : Position h) (c : Fin k) (q : Fin m) :
    (point (importLoop light is heavy work).1.tree j).active c q=true ↔
      (point heavy.tree j).active c q=true ∨ (j∈is ∧ (point light j).active c q=true) := by
  induction is generalizing heavy work with
  | nil => simp [importLoop]
  | cons i is ih =>
    simp only [importLoop,ih,importOne_active,List.mem_cons]
    constructor
    · rintro ((hh | ⟨he,hl⟩) | ⟨hm,hl⟩)
      · exact Or.inl hh
      · exact Or.inr ⟨Or.inl he,hl⟩
      · exact Or.inr ⟨Or.inr hm,hl⟩
    · rintro (hh | ⟨he|hm,hl⟩)
      · exact Or.inl (Or.inl hh)
      · exact Or.inl (Or.inr ⟨he,hl⟩)
      · exact Or.inr ⟨hm,hl⟩

theorem importLoop_steps (light : Tree k m h) (is : List (Position h))
    (heavy : State k m h) (work : Nat) :
    (importLoop light is heavy work).2≤work+is.length*importBudget k m h := by
  induction is generalizing heavy work with
  | nil => simp [importLoop]
  | cons i is ih =>
    have hs := importOne_steps light heavy.tree i
    have hr := ih ⟨(importOne light heavy.tree i).1,i::heavy.positions,heavy.cachedSize+1⟩
      (work+(importOne light heavy.tree i).2+2)
    change (importLoop light is _ _).2≤_
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem importMany_positions (light : Tree k m h) (is : List (Position h)) (heavy : State k m h) :
    (importMany light is heavy).1.positions=is.reverse++heavy.positions := importLoop_positions _ _ _ _

theorem importMany_size (light : Tree k m h) (is : List (Position h)) (heavy : State k m h) :
    (importMany light is heavy).1.cachedSize=heavy.cachedSize+is.length := importLoop_size _ _ _ _

theorem importMany_trans (light : Tree k m h) (is : List (Position h))
    (heavy : State k m h) (j : Position h) :
    (point (importMany light is heavy).1.tree j).trans=(point heavy.tree j).trans :=
  importLoop_trans _ _ _ _ _

theorem importMany_steps (light : Tree k m h) (is : List (Position h)) (heavy : State k m h) :
    (importMany light is heavy).2≤is.length*importBudget k m h := by
  simpa only [Nat.zero_add] using importLoop_steps light is heavy 0

/-- If the actual maintained light list covers all its live positions,
importing it computes the exact union at every position. -/
theorem importMany_active (light heavy : State k m h) (hl : Valid light)
    (j : Position h) (c : Fin k) (q : Fin m) :
    (point (importMany light.tree light.positions heavy).1.tree j).active c q=true ↔
      (point heavy.tree j).active c q=true ∨ (point light.tree j).active c q=true := by
  rw [importMany,importLoop_active]
  constructor
  · rintro (hh | ⟨_,hl⟩)
    · exact Or.inl hh
    · exact Or.inr hl
  · rintro (hh | hj)
    · exact Or.inl hh
    · exact Or.inr ⟨(hl.2.2 j).mpr ⟨c,q,hj⟩,hj⟩

theorem importMany_valid (light heavy : State k m h) (hl : Valid light) (hh : Valid heavy) :
    Valid (importMany light.tree light.positions heavy).1 := by
  refine ⟨importLoop_good _ _ _ _ hh.1,?_,?_⟩
  · rw [importMany_size,importMany_positions,List.length_append,List.length_reverse,hh.2.1]
    omega
  · intro j
    rw [importMany_positions,List.mem_append,List.mem_reverse,hl.2.2 j,hh.2.2 j]
    constructor
    · rintro (⟨c,q,hc⟩ | ⟨c,q,hc⟩)
      · exact ⟨c,q,(importMany_active light heavy hl j c q).mpr (Or.inr hc)⟩
      · exact ⟨c,q,(importMany_active light heavy hl j c q).mpr (Or.inl hc)⟩
    · rintro ⟨c,q,hc⟩
      rcases (importMany_active light heavy hl j c q).mp hc with hh|hl
      · exact Or.inr ⟨c,q,hh⟩
      · exact Or.inl ⟨c,q,hl⟩

/-- Recoloring retains the maintained position list and cached size. -/
def recolor (g : Vector (Fin k) k) (s : State k m h) : State k m h×Nat :=
  let out := Tree.recolor g s.tree
  (⟨out.1,s.positions,s.cachedSize⟩,out.2+1)

theorem recolor_valid (g : Vector (Fin k) k) (s : State k m h) (hs : Valid s) :
    Valid (recolor g s).1 := by
  refine ⟨Tree.recolor_good _ _ hs.1,hs.2.1,?_⟩
  intro j
  change j∈s.positions ↔ ∃ c q,(point (Tree.recolor g s.tree).1 j).active c q=true
  rw [hs.2.2 j]
  simp only [point_recolor,View.rename_active]
  constructor
  · rintro ⟨c,q,hc⟩
    exact ⟨g.get c,q,c,rfl,hc⟩
  · rintro ⟨c,q,old,_,ho⟩
    exact ⟨old,q,ho⟩

theorem recolor_steps (g : Vector (Fin k) k) (s : State k m h) :
    (recolor g s).2≤Tree.recolorBudget k m+1 := by
  have hh := Tree.recolor_steps g s.tree
  change (Tree.recolor g s.tree).2+1≤_
  omega

end REWB.BoundaryIndex.Merge
