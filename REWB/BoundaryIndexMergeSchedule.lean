import REWB.BoundaryIndexMerge
import REWB.MaskedEventBudget

/-! A concrete persistent small-to-large schedule. Position lists and cached
sizes are built from leaves, rather than supplied by an external event-count
hypothesis. Node maps permit arbitrary color coalescence on both children.
The retained heavy child's list is shared; only light positions are imported.
The underlying binary schedule is exactly `MaskedEventBudget.MergeTree`. -/
namespace REWB.BoundaryIndex.MergeSchedule
open REWB.BoundaryIndex.Merge
variable {k m h : Nat}

/-- Compare cached sizes once, retain the heavy child, and import the actual
maintained light list. The extra unit charges the branch/record operation. -/
def merge (left right : Merge.State k m h) : Merge.State k m h×Nat :=
  let out := if left.cachedSize≤right.cachedSize then
    importMany left.tree left.positions right
    else importMany right.tree right.positions left
  (out.1,out.2+1)

theorem merge_valid (left right : Merge.State k m h) (hl : Valid left) (hr : Valid right) :
    Valid (merge left right).1 := by
  unfold merge
  split
  · exact importMany_valid _ _ hl hr
  · exact importMany_valid _ _ hr hl

theorem merge_size (left right : Merge.State k m h)
    (hl : left.cachedSize=left.positions.length) (hr : right.cachedSize=right.positions.length) :
    (merge left right).1.cachedSize=left.cachedSize+right.cachedSize := by
  unfold merge
  split <;> simp only [importMany_size,← hl,← hr]
  exact Nat.add_comm _ _

theorem merge_length (left right : Merge.State k m h) :
    (merge left right).1.positions.length=left.positions.length+right.positions.length := by
  unfold merge
  split <;> simp only [importMany_positions,List.length_append,List.length_reverse]
  exact Nat.add_comm _ _

theorem merge_perm (left right : Merge.State k m h) :
    (merge left right).1.positions.Perm (left.positions++right.positions) := by
  unfold merge
  split
  · rw [importMany_positions]
    exact (List.reverse_perm _).append (List.Perm.refl _)
  · rw [importMany_positions]
    exact ((List.reverse_perm _).append (List.Perm.refl _)).trans List.perm_append_comm

theorem merge_active (left right : Merge.State k m h) (hl : Valid left) (hr : Valid right)
    (i : Position h) (c : Fin k) (q : Fin m) :
    (point (merge left right).1.tree i).active c q=true ↔
      (point left.tree i).active c q=true ∨ (point right.tree i).active c q=true := by
  unfold merge
  split
  · rw [importMany_active _ _ hl]
    exact or_comm
  · exact importMany_active _ _ hr _ _ _

theorem merge_trans (left right : Merge.State k m h) (i : Position h)
    (he : (point left.tree i).trans=(point right.tree i).trans) :
    (point (merge left right).1.tree i).trans=(point left.tree i).trans := by
  unfold merge
  split
  · rw [importMany_trans,he]
  · exact importMany_trans _ _ _ _

theorem merge_steps (left right : Merge.State k m h)
    (hl : left.cachedSize=left.positions.length) (hr : right.cachedSize=right.positions.length) :
    (merge left right).2≤min left.cachedSize right.cachedSize*importBudget k m h+1 := by
  unfold merge
  split
  next he =>
    rw [Nat.min_eq_left he]
    have hh := importMany_steps left.tree left.positions right
    rw [← hl] at hh
    change (importMany left.tree left.positions right).2+1≤_
    omega
  next he =>
    rw [Nat.min_eq_right (by omega)]
    have hh := importMany_steps right.tree right.positions left
    rw [← hr] at hh
    change (importMany right.tree right.positions left).2+1≤_
    omega

inductive Program (k m h : Nat) where
  | leaf : Position h→Fin k→Fin m→Program k m h
  | node : Vector (Fin k) k→Vector (Fin k) k→Program k m h→Program k m h→Program k m h

def shape : Program k m h→MaskedEventBudget.MergeTree
  | .leaf p _ _ => .leaf p.val
  | .node _ _ a b => .node (shape a) (shape b)

def positions : Program k m h→List (Position h)
  | .leaf p _ _ => [p]
  | .node _ _ a b => positions a++positions b

def nodes : Program k m h→Nat
  | .leaf _ _ _ => 0
  | .node _ _ a b => nodes a+nodes b+1

theorem positions_length (p : Program k m h) :
    (positions p).length=MaskedEventBudget.size (shape p) := by
  induction p with
  | leaf _ _ _ => rfl
  | node _ _ a b ha hb => simp only [positions,List.length_append,ha,hb,shape,MaskedEventBudget.size]

theorem nodes_size (p : Program k m h) : nodes p+1=MaskedEventBudget.size (shape p) := by
  induction p with
  | leaf _ _ _ => rfl
  | node _ _ a b ha hb =>
    simp only [nodes,shape,MaskedEventBudget.size]
    omega

/-- Exact leaf-color semantics of a decorated merge program. -/
def Active : Program k m h→Position h→Fin k→Fin m→Prop
  | .leaf p c q,i,d,r => i=p ∧ d=c ∧ r=q
  | .node g f a b,i,c,q =>
      (∃ old,g.get old=c ∧ Active a i old q) ∨
      (∃ old,f.get old=c ∧ Active b i old q)

structure Result (k m h : Nat) where
  state : Merge.State k m h
  steps : Nat
  transfers : Nat

/-- The static base is shared by all leaf versions. Each leaf creates one
persistent point insertion; there is no full-text rebuild at a leaf. -/
def execute (base : Tree k m h) : Program k m h→Result k m h
  | .leaf p c q =>
    let out := Tree.insert base p.val c q
    ⟨⟨out.1,[p],1⟩,out.2+2,0⟩
  | .node g f a b =>
    let aa := execute base a
    let bb := execute base b
    let ll := recolor g aa.state
    let rr := recolor f bb.state
    let out := merge ll.1 rr.1
    ⟨out.1,aa.steps+bb.steps+ll.2+rr.2+out.2,
      aa.transfers+bb.transfers+min ll.1.cachedSize rr.1.cachedSize⟩

theorem execute_perm (base : Tree k m h) (p : Program k m h) :
    (execute base p).state.positions.Perm (positions p) := by
  induction p with
  | leaf _ _ _ => exact List.Perm.refl _
  | node g f a b ha hb =>
    change (merge (recolor g (execute base a).state).1 (recolor f (execute base b).state).1).1.positions.Perm _
    exact (merge_perm _ _).trans (ha.append hb)

theorem execute_length (base : Tree k m h) (p : Program k m h) :
    (execute base p).state.positions.length=MaskedEventBudget.size (shape p) := by
  rw [(execute_perm base p).length_eq,positions_length]

theorem execute_size (base : Tree k m h) (p : Program k m h) :
    (execute base p).state.cachedSize=MaskedEventBudget.size (shape p) := by
  induction p with
  | leaf _ _ _ => rfl
  | node g f a b ha hb =>
    change (merge (recolor g (execute base a).state).1 (recolor f (execute base b).state).1).1.cachedSize=_
    rw [merge_size _ _ (by simpa only [recolor,ha] using (execute_length base a).symm)
      (by simpa only [recolor,hb] using (execute_length base b).symm)]
    simp only [recolor,ha,hb,shape,MaskedEventBudget.size]

theorem execute_nodup (base : Tree k m h) (p : Program k m h) (hp : (positions p).Nodup) :
    (execute base p).state.positions.Nodup := (execute_perm base p).symm.nodup hp

def Blank (base : Tree k m h) : Prop := ∀ i c q,(point base i).active c q=false

theorem insert_active (base : Tree k m h) (hb : Blank base) (p i : Position h)
    (c d : Fin k) (q r : Fin m) :
    (point (Tree.insert base p.val c q).1 i).active d r=true ↔ i=p ∧ d=c ∧ r=q := by
  change (point (Tree.replace base p.val (Tree.seed (Tree.get base p.val).1 c q).1).1 i).active d r=true ↔ _
  rw [point_replace,Tree.seed_view]
  by_cases he : p=i
  · subst i
    simp only [if_pos rfl,if_true,Tree.seedView]
    change ((point base p).active d r || decide (d=c ∧ r=q))=true ↔ _
    rw [hb]
    simp only [Bool.false_or,decide_eq_true_eq,true_and]
  · rw [if_neg he]
    rw [hb]
    simp only [Bool.false_eq_true,Ne.symm he,false_and]

theorem execute_valid (base : Tree k m h) (hg : Tree.Good base) (hb : Blank base)
    (p : Program k m h) : Valid (execute base p).state := by
  induction p with
  | leaf p c q =>
    refine ⟨Tree.insert_good _ hg _ _ _,rfl,?_⟩
    intro i
    simp only [execute,List.mem_singleton,insert_active base hb]
    constructor
    · intro he
      exact ⟨c,q,he,rfl,rfl⟩
    · rintro ⟨d,r,he,_,_⟩
      exact he
  | node g f a b ha hb =>
    exact merge_valid _ _ (recolor_valid _ _ ha) (recolor_valid _ _ hb)

theorem execute_active (base : Tree k m h) (hg : Tree.Good base) (hb : Blank base)
    (p : Program k m h) (i : Position h) (c : Fin k) (q : Fin m) :
    (point (execute base p).state.tree i).active c q=true ↔ Active p i c q := by
  induction p generalizing c with
  | leaf pos color state => exact insert_active base hb _ _ _ _ _ _
  | node g f a b ha hc =>
    rw [show (execute base (.node g f a b)).state=
      (merge (recolor g (execute base a).state).1 (recolor f (execute base b).state).1).1 from rfl,
      merge_active _ _ (recolor_valid _ _ (execute_valid base hg hb a))
        (recolor_valid _ _ (execute_valid base hg hb b))]
    change (point (Tree.recolor g (execute base a).state.tree).1 i).active c q=true ∨
      (point (Tree.recolor f (execute base b).state.tree).1 i).active c q=true ↔ _
    simp only [point_recolor,View.rename_active,ha,hc,Active]

theorem execute_trans (base : Tree k m h) (p : Program k m h) (i : Position h) :
    (point (execute base p).state.tree i).trans=(point base i).trans := by
  induction p with
  | leaf pos c q =>
    change (point (Tree.replace base pos.val (Tree.seed (Tree.get base pos.val).1 c q).1).1 i).trans=_
    rw [point_replace,Tree.seed_view]
    split
    next he => subst i; rfl
    next he => rfl
  | node g f a b ha hb =>
    change (point (merge (recolor g (execute base a).state).1
      (recolor f (execute base b).state).1).1.tree i).trans=_
    have hla : (point (recolor g (execute base a).state).1.tree i).trans=(point base i).trans := by
      change (point (Tree.recolor g (execute base a).state.tree).1 i).trans=_
      rw [point_recolor]
      exact ha
    have hlb : (point (recolor f (execute base b).state).1.tree i).trans=(point base i).trans := by
      change (point (Tree.recolor f (execute base b).state.tree).1 i).trans=_
      rw [point_recolor]
      exact hb
    rw [merge_trans _ _ i (hla.trans hlb.symm),hla]

theorem execute_transfers (base : Tree k m h) (p : Program k m h) :
    (execute base p).transfers=MaskedEventBudget.lightVolume (shape p) := by
  induction p with
  | leaf _ _ _ => rfl
  | node g f a b ha hb =>
    simp only [execute,recolor,ha,hb,execute_size,shape,MaskedEventBudget.lightVolume]

/-- Number of pattern-dependent operations for one seeded leaf version. -/
def seedBudget (k m h : Nat) : Nat :=
  (h+1)*(Tree.getBudget k m+Tree.replaceBudget k m)+k*m+2

/-- Root color maps, state records and the retained-child choice. -/
def nodeBudget (k m : Nat) : Nat := 2*(Tree.recolorBudget k m+1)+1

theorem execute_steps (base : Tree k m h) (p : Program k m h) :
    (execute base p).steps≤
      MaskedEventBudget.size (shape p)*seedBudget k m h+
      nodes p*nodeBudget k m+MaskedEventBudget.lightVolume (shape p)*importBudget k m h := by
  induction p with
  | leaf pos c q =>
    have hh := Tree.insert_steps base pos.val c q
    simpa only [execute,shape,MaskedEventBudget.size,MaskedEventBudget.lightVolume,
      nodes,Nat.one_mul,Nat.zero_mul,Nat.add_zero,seedBudget] using Nat.add_le_add_right hh 2
  | node g f a b ha hb =>
    have hl := recolor_steps g (execute base a).state
    have hr := recolor_steps f (execute base b).state
    have hm := merge_steps (recolor g (execute base a).state).1 (recolor f (execute base b).state).1
      (by change (execute base a).state.cachedSize=(execute base a).state.positions.length
          rw [execute_size,execute_length])
      (by change (execute base b).state.cachedSize=(execute base b).state.positions.length
          rw [execute_size,execute_length])
    change (merge (recolor g (execute base a).state).1 (recolor f (execute base b).state).1).2≤
      min (execute base a).state.cachedSize (execute base b).state.cachedSize*importBudget k m h+1 at hm
    rw [execute_size,execute_size] at hm
    have hn : (recolor g (execute base a).state).2+(recolor f (execute base b).state).2+1≤nodeBudget k m := by
      unfold nodeBudget
      omega
    change (execute base a).steps+(execute base b).steps+
      (recolor g (execute base a).state).2+(recolor f (execute base b).state).2+
      (merge (recolor g (execute base a).state).1 (recolor f (execute base b).state).1).2≤_
    simp only [shape,MaskedEventBudget.size,MaskedEventBudget.lightVolume,nodes,
      Nat.add_mul,Nat.one_mul]
    omega

theorem execute_bound (base : Tree k m h) (p : Program k m h) :
    (execute base p).steps≤
      MaskedEventBudget.size (shape p)*(seedBudget k m h+nodeBudget k m)+
      (MaskedEventBudget.size (shape p)*Nat.log2 (MaskedEventBudget.size (shape p)))*importBudget k m h := by
  have hs := execute_steps base p
  have hn := nodes_size p
  have hl := Nat.mul_le_mul_right (importBudget k m h) (MaskedEventBudget.lightVolume_bound (shape p))
  have hnodes := Nat.mul_le_mul_right (nodeBudget k m) (show nodes p≤MaskedEventBudget.size (shape p) by omega)
  rw [Nat.mul_add]
  omega

theorem transfers_bound (base : Tree k m h) (p : Program k m h) :
    (execute base p).transfers≤MaskedEventBudget.size (shape p)*Nat.log2 (MaskedEventBudget.size (shape p)) := by
  rw [execute_transfers]
  exact MaskedEventBudget.lightVolume_bound _

end REWB.BoundaryIndex.MergeSchedule
