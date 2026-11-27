import REWB.BoundaryIndexMergeBuild

/-! Persistent boundary-index merging with distinct source and target roles.

Silent source leaves count toward the heavy-child mass but introduce no
endpoint record. Target leaves introduce one colored endpoint. Only target
lists are imported; cached total mass chooses the retained child. This is
the weighting needed by source-leaf heavy-path queries. -/
namespace REWB.BoundaryIndex.Mixed
open REWB.BoundaryIndex.Merge
variable {k m h : Nat}

/-- Retain the child of larger total source+target mass. The branch cost
is explicit; only the chosen light child's target records are traversed. -/
def combine (left right : Merge.State k m h) (leftMass rightMass : Nat) : Merge.State k m h×Nat :=
  let out := if leftMass≤rightMass then importMany left.tree left.positions right
    else importMany right.tree right.positions left
  (out.1,out.2+1)

def imported (left right : Merge.State k m h) (leftMass rightMass : Nat) : Nat :=
  if leftMass≤rightMass then left.cachedSize else right.cachedSize

theorem combine_valid (left right : Merge.State k m h) (lm rm : Nat)
    (hl : Valid left) (hr : Valid right) : Valid (combine left right lm rm).1 := by
  unfold combine
  split
  · exact importMany_valid _ _ hl hr
  · exact importMany_valid _ _ hr hl

theorem combine_size (left right : Merge.State k m h) (lm rm : Nat)
    (hl : left.cachedSize=left.positions.length) (hr : right.cachedSize=right.positions.length) :
    (combine left right lm rm).1.cachedSize=left.cachedSize+right.cachedSize := by
  unfold combine
  split <;> simp only [importMany_size,← hl,← hr]
  exact Nat.add_comm _ _

theorem combine_perm (left right : Merge.State k m h) (lm rm : Nat) :
    (combine left right lm rm).1.positions.Perm (left.positions++right.positions) := by
  unfold combine
  split
  · rw [importMany_positions]
    exact (List.reverse_perm _).append (List.Perm.refl _)
  · rw [importMany_positions]
    exact ((List.reverse_perm _).append (List.Perm.refl _)).trans List.perm_append_comm

theorem combine_active (left right : Merge.State k m h) (lm rm : Nat)
    (hl : Valid left) (hr : Valid right) (i : Position h) (c : Fin k) (q : Fin m) :
    (point (combine left right lm rm).1.tree i).active c q=true ↔
      (point left.tree i).active c q=true ∨ (point right.tree i).active c q=true := by
  unfold combine
  split
  · rw [importMany_active _ _ hl]
    exact or_comm
  · exact importMany_active _ _ hr _ _ _

theorem combine_trans (left right : Merge.State k m h) (lm rm : Nat) (i : Position h)
    (he : (point left.tree i).trans=(point right.tree i).trans) :
    (point (combine left right lm rm).1.tree i).trans=(point left.tree i).trans := by
  unfold combine
  split
  · rw [importMany_trans,he]
  · exact importMany_trans _ _ _ _

theorem imported_le (left right : Merge.State k m h) (lm rm : Nat)
    (hl : left.cachedSize≤lm) (hr : right.cachedSize≤rm) :
    imported left right lm rm≤min lm rm := by
  unfold imported
  split
  next he => simpa only [Nat.min_eq_left he] using hl
  next he => simpa only [Nat.min_eq_right (by omega : rm≤lm)] using hr

theorem combine_steps (left right : Merge.State k m h) (lm rm : Nat)
    (hl : left.cachedSize=left.positions.length) (hr : right.cachedSize=right.positions.length) :
    (combine left right lm rm).2≤imported left right lm rm*importBudget k m h+1 := by
  unfold combine imported
  split
  · have hh := importMany_steps left.tree left.positions right
    rw [← hl] at hh
    change (importMany left.tree left.positions right).2+1≤_
    omega
  · have hh := importMany_steps right.tree right.positions left
    rw [← hr] at hh
    change (importMany right.tree right.positions left).2+1≤_
    omega

inductive Program (k m h : Nat) where
  | source : Position h→Program k m h
  | target : Position h→Fin k→Fin m→Program k m h
  | node : Vector (Fin k) k→Vector (Fin k) k→Program k m h→Program k m h→Program k m h

def shape : Program k m h→MaskedEventBudget.MergeTree
  | .source p => .leaf p.val
  | .target p _ _ => .leaf p.val
  | .node _ _ a b => .node (shape a) (shape b)

def targetPositions : Program k m h→List (Position h)
  | .source _ => []
  | .target p _ _ => [p]
  | .node _ _ a b => targetPositions a++targetPositions b

def nodes : Program k m h→Nat
  | .source _ => 0
  | .target _ _ _ => 0
  | .node _ _ a b => nodes a+nodes b+1

def Active : Program k m h→Position h→Fin k→Fin m→Prop
  | .source _,_,_,_ => False
  | .target p c q,i,d,r => i=p ∧ d=c ∧ r=q
  | .node g f a b,i,c,q =>
      (∃ old,g.get old=c ∧ Active a i old q) ∨
      (∃ old,f.get old=c ∧ Active b i old q)

theorem targetPositions_bound (p : Program k m h) :
    (targetPositions p).length≤MaskedEventBudget.size (shape p) := by
  induction p with
  | source _ => exact Nat.zero_le _
  | target _ _ _ => exact Nat.le_refl _
  | node g f a b ha hb =>
    simp only [targetPositions,List.length_append,shape,MaskedEventBudget.size]
    omega

theorem nodes_size (p : Program k m h) : nodes p+1=MaskedEventBudget.size (shape p) := by
  induction p with
  | source _ => rfl
  | target _ _ _ => rfl
  | node g f a b ha hb =>
    simp only [nodes,shape,MaskedEventBudget.size]
    omega

structure Result (k m h : Nat) where
  state : Merge.State k m h
  totalMass : Nat
  steps : Nat
  transfers : Nat

def execute (base : Tree k m h) : Program k m h→Result k m h
  | .source _ => ⟨⟨base,[],0⟩,1,1,0⟩
  | .target p c q =>
    let out := Tree.insert base p.val c q
    ⟨⟨out.1,[p],1⟩,1,out.2+2,0⟩
  | .node g f a b =>
    let aa := execute base a
    let bb := execute base b
    let ll := recolor g aa.state
    let rr := recolor f bb.state
    let out := combine ll.1 rr.1 aa.totalMass bb.totalMass
    ⟨out.1,aa.totalMass+bb.totalMass,
      aa.steps+bb.steps+ll.2+rr.2+out.2+1,
      aa.transfers+bb.transfers+imported ll.1 rr.1 aa.totalMass bb.totalMass⟩

theorem execute_mass (base : Tree k m h) (p : Program k m h) :
    (execute base p).totalMass=MaskedEventBudget.size (shape p) := by
  induction p with
  | source _ => rfl
  | target _ _ _ => rfl
  | node g f a b ha hb => simp only [execute,shape,MaskedEventBudget.size,ha,hb]

theorem execute_perm (base : Tree k m h) (p : Program k m h) :
    (execute base p).state.positions.Perm (targetPositions p) := by
  induction p with
  | source _ => exact List.Perm.refl _
  | target _ _ _ => exact List.Perm.refl _
  | node g f a b ha hb => exact (combine_perm _ _ _ _).trans (ha.append hb)

theorem execute_length (base : Tree k m h) (p : Program k m h) :
    (execute base p).state.positions.length=(targetPositions p).length :=
  (execute_perm base p).length_eq

theorem execute_size (base : Tree k m h) (p : Program k m h) :
    (execute base p).state.cachedSize=(targetPositions p).length := by
  induction p with
  | source _ => rfl
  | target _ _ _ => rfl
  | node g f a b ha hb =>
    change (combine (recolor g (execute base a).state).1 (recolor f (execute base b).state).1
      (execute base a).totalMass (execute base b).totalMass).1.cachedSize=_
    rw [combine_size _ _ _ _ (by simpa only [recolor,ha] using (execute_length base a).symm)
      (by simpa only [recolor,hb] using (execute_length base b).symm)]
    simp only [recolor,ha,hb,targetPositions,List.length_append]

theorem execute_targets_le_mass (base : Tree k m h) (p : Program k m h) :
    (execute base p).state.cachedSize≤(execute base p).totalMass := by
  rw [execute_size,execute_mass]
  exact targetPositions_bound p

theorem execute_nodup (base : Tree k m h) (p : Program k m h) (hp : (targetPositions p).Nodup) :
    (execute base p).state.positions.Nodup := (execute_perm base p).symm.nodup hp

theorem execute_valid (base : Tree k m h) (hg : Tree.Good base) (hb : MergeSchedule.Blank base)
    (p : Program k m h) : Valid (execute base p).state := by
  induction p with
  | source pos =>
    refine ⟨hg,rfl,?_⟩
    intro i
    change i∈([] : List (Position h)) ↔ ∃ c q,(point base i).active c q=true
    constructor
    · intro hx; exact False.elim (List.not_mem_nil hx)
    · rintro ⟨c,q,hc⟩
      rw [hb i c q] at hc
      cases hc
  | target pos c q =>
    exact MergeSchedule.execute_valid base hg hb (.leaf pos c q)
  | node g f a b ha hb => exact combine_valid _ _ _ _ (recolor_valid _ _ ha) (recolor_valid _ _ hb)

theorem execute_active (base : Tree k m h) (hg : Tree.Good base) (hb : MergeSchedule.Blank base)
    (p : Program k m h) (i : Position h) (c : Fin k) (q : Fin m) :
    (point (execute base p).state.tree i).active c q=true ↔ Active p i c q := by
  induction p generalizing c with
  | source _ =>
    change (point base i).active c q=true ↔ False
    rw [hb]
    simp only [Bool.false_eq_true]
  | target pos color state => exact MergeSchedule.insert_active base hb _ _ _ _ _ _
  | node g f a b ha hc =>
    change (point (combine (recolor g (execute base a).state).1 (recolor f (execute base b).state).1
      (execute base a).totalMass (execute base b).totalMass).1.tree i).active c q=true ↔ _
    rw [combine_active _ _ _ _ (recolor_valid _ _ (execute_valid base hg hb a))
      (recolor_valid _ _ (execute_valid base hg hb b))]
    change (point (Tree.recolor g (execute base a).state.tree).1 i).active c q=true ∨
      (point (Tree.recolor f (execute base b).state.tree).1 i).active c q=true ↔ _
    simp only [point_recolor,View.rename_active,ha,hc,Active]

theorem execute_trans (base : Tree k m h) (p : Program k m h) (i : Position h) :
    (point (execute base p).state.tree i).trans=(point base i).trans := by
  induction p with
  | source _ => rfl
  | target pos c q => exact MergeSchedule.execute_trans base (.leaf pos c q) i
  | node g f a b ha hb =>
    change (point (combine (recolor g (execute base a).state).1 (recolor f (execute base b).state).1
      (execute base a).totalMass (execute base b).totalMass).1.tree i).trans=_
    have hla : (point (recolor g (execute base a).state).1.tree i).trans=(point base i).trans := by
      change (point (Tree.recolor g (execute base a).state.tree).1 i).trans=_
      rw [point_recolor]
      exact ha
    have hlb : (point (recolor f (execute base b).state).1.tree i).trans=(point base i).trans := by
      change (point (Tree.recolor f (execute base b).state.tree).1 i).trans=_
      rw [point_recolor]
      exact hb
    rw [combine_trans _ _ _ _ i (hla.trans hlb.symm),hla]

theorem execute_transfers (base : Tree k m h) (p : Program k m h) :
    (execute base p).transfers≤MaskedEventBudget.lightVolume (shape p) := by
  induction p with
  | source _ => exact Nat.le_refl _
  | target _ _ _ => exact Nat.le_refl _
  | node g f a b ha hb =>
    have hh := imported_le (recolor g (execute base a).state).1 (recolor f (execute base b).state).1
      (execute base a).totalMass (execute base b).totalMass
      (execute_targets_le_mass base a) (execute_targets_le_mass base b)
    rw [execute_mass,execute_mass] at hh
    change (execute base a).transfers+(execute base b).transfers+
      imported (recolor g (execute base a).state).1 (recolor f (execute base b).state).1
        (execute base a).totalMass (execute base b).totalMass≤_
    simp only [shape,MaskedEventBudget.lightVolume,execute_mass]
    omega

/-- Source records cost one, target records cost the actual point seed.
The shared upper bound is the existing seed budget. -/
def seedBudget (k m h : Nat) : Nat := MergeSchedule.seedBudget k m h

/-- Recolor two children, choose the heavy one, and write total mass. -/
def nodeBudget (k m : Nat) : Nat := 2*(Tree.recolorBudget k m+1)+2

theorem execute_steps (base : Tree k m h) (p : Program k m h) :
    (execute base p).steps≤MaskedEventBudget.size (shape p)*seedBudget k m h+
      nodes p*nodeBudget k m+MaskedEventBudget.lightVolume (shape p)*importBudget k m h := by
  induction p with
  | source _ =>
    simp only [execute,shape,MaskedEventBudget.size,MaskedEventBudget.lightVolume,nodes,
      Nat.one_mul,Nat.zero_mul,Nat.add_zero,seedBudget,MergeSchedule.seedBudget]
    omega
  | target pos c q =>
    have hh := Tree.insert_steps base pos.val c q
    simpa only [execute,shape,MaskedEventBudget.size,MaskedEventBudget.lightVolume,nodes,
      Nat.one_mul,Nat.zero_mul,Nat.add_zero,seedBudget,MergeSchedule.seedBudget] using Nat.add_le_add_right hh 2
  | node g f a b ha hb =>
    have hl := recolor_steps g (execute base a).state
    have hr := recolor_steps f (execute base b).state
    have hm := combine_steps (recolor g (execute base a).state).1 (recolor f (execute base b).state).1
      (execute base a).totalMass (execute base b).totalMass
      (by change (execute base a).state.cachedSize=(execute base a).state.positions.length
          rw [execute_size,execute_length])
      (by change (execute base b).state.cachedSize=(execute base b).state.positions.length
          rw [execute_size,execute_length])
    have ht := Nat.mul_le_mul_right (importBudget k m h)
      (imported_le (recolor g (execute base a).state).1 (recolor f (execute base b).state).1
        (execute base a).totalMass (execute base b).totalMass
        (execute_targets_le_mass base a) (execute_targets_le_mass base b))
    rw [execute_mass,execute_mass] at ht hm
    have hn : (recolor g (execute base a).state).2+(recolor f (execute base b).state).2+2≤nodeBudget k m := by
      unfold nodeBudget
      omega
    change (execute base a).steps+(execute base b).steps+
      (recolor g (execute base a).state).2+(recolor f (execute base b).state).2+
      (combine (recolor g (execute base a).state).1 (recolor f (execute base b).state).1
        (execute base a).totalMass (execute base b).totalMass).2+1≤_
    simp only [shape,MaskedEventBudget.size,MaskedEventBudget.lightVolume,nodes,
      Nat.add_mul,Nat.one_mul,execute_mass]
    omega

theorem execute_bound (base : Tree k m h) (p : Program k m h) :
    (execute base p).steps≤MaskedEventBudget.size (shape p)*(seedBudget k m h+nodeBudget k m)+
      (MaskedEventBudget.size (shape p)*Nat.log2 (MaskedEventBudget.size (shape p)))*importBudget k m h := by
  have hs := execute_steps base p
  have hn := nodes_size p
  have hl := Nat.mul_le_mul_right (importBudget k m h) (MaskedEventBudget.lightVolume_bound (shape p))
  have hnodes := Nat.mul_le_mul_right (nodeBudget k m) (show nodes p≤MaskedEventBudget.size (shape p) by omega)
  rw [Nat.mul_add]
  omega

theorem transfers_bound (base : Tree k m h) (p : Program k m h) :
    (execute base p).transfers≤MaskedEventBudget.size (shape p)*Nat.log2 (MaskedEventBudget.size (shape p)) :=
  Nat.le_trans (execute_transfers base p) (MaskedEventBudget.lightVolume_bound _)

/-- Maximum number of light edges on any root-to-leaf path under the
same total-mass comparison used by the executable scheduler. -/
def lightHeight : Program k m h→Nat
  | .source _ => 0
  | .target _ _ _ => 0
  | .node _ _ a b =>
    if MaskedEventBudget.size (shape a)≤MaskedEventBudget.size (shape b) then
      max (lightHeight a+1) (lightHeight b)
    else max (lightHeight a) (lightHeight b+1)

private theorem log_mono {a n : Nat} (ha : 0<a) (han : a≤n) : a.log2≤n.log2 := by
  apply (Nat.le_log2 (by omega : n≠0)).mpr
  exact Nat.le_trans (Nat.log2_self_le (by omega : a≠0)) han

private theorem log_double {a b : Nat} (ha : 0<a) (hab : a≤b) : a.log2+1≤(a+b).log2 := by
  apply (Nat.le_log2 (by omega : a+b≠0)).mpr
  rw [Nat.pow_succ]
  have hh := Nat.mul_le_mul_right 2 (Nat.log2_self_le (by omega : a≠0))
  omega

theorem lightHeight_bound (p : Program k m h) :
    lightHeight p≤Nat.log2 (MaskedEventBudget.size (shape p)) := by
  induction p with
  | source _ => exact Nat.zero_le _
  | target _ _ _ => exact Nat.zero_le _
  | node g f a b ha hb =>
    have hpa := MaskedEventBudget.size_pos (shape a)
    have hpb := MaskedEventBudget.size_pos (shape b)
    simp only [lightHeight,shape,MaskedEventBudget.size]
    split
    next he =>
      apply Nat.max_le.mpr
      constructor
      · exact Nat.le_trans (Nat.add_le_add_right ha 1) (log_double hpa he)
      · exact Nat.le_trans hb (log_mono hpb (by omega))
    next he =>
      apply Nat.max_le.mpr
      constructor
      · exact Nat.le_trans ha (log_mono hpa (by omega))
      · have hd := log_double hpb (show MaskedEventBudget.size (shape b)≤MaskedEventBudget.size (shape a) by omega)
        rw [Nat.add_comm (MaskedEventBudget.size (shape b)) (MaskedEventBudget.size (shape a))] at hd
        exact Nat.le_trans (Nat.add_le_add_right hb 1) hd

/-- One-time static preparation and the actual mixed construction. -/
def run (rows : Array (Vector (Fin m) m)) (p : Program k m h) : Result k m h :=
  let base := MergeBuild.prepare rows h
  let out := execute base.1 p
  {out with steps:=base.2+out.steps}

theorem run_valid (rows : Array (Vector (Fin m) m)) (p : Program k m h) :
    Valid (run rows p).state := execute_valid _ (MergeBuild.prepare_good _ _) (MergeBuild.prepare_blank _ _) _

theorem run_active (rows : Array (Vector (Fin m) m)) (p : Program k m h)
    (i : Position h) (c : Fin k) (q : Fin m) :
    (point (run rows p).state.tree i).active c q=true ↔ Active p i c q :=
  execute_active _ (MergeBuild.prepare_good _ _) (MergeBuild.prepare_blank _ _) _ _ _ _

theorem run_trans (rows : Array (Vector (Fin m) m)) (p : Program k m h) (i : Position h) :
    (point (run rows p).state.tree i).trans=(rows[i.val]?.getD (Vector.ofFn id)).get := by
  change (point (execute (MergeBuild.prepare rows h).1 p).state.tree i).trans=_
  rw [execute_trans,MergeBuild.prepare_trans]

theorem run_auto_steps (rows : Array (Vector (Fin m) m))
    (p : Program k m (Tree.heightFor rows.size)) :
    (run rows p).steps≤rows.size*(k*m+1)+2*(rows.size+1)*(Tree.joinBudget k m+Tree.leafBudget k m)+
      MaskedEventBudget.size (shape p)*(seedBudget k m (Tree.heightFor rows.size)+nodeBudget k m)+
      (MaskedEventBudget.size (shape p)*Nat.log2 (MaskedEventBudget.size (shape p)))*
        importBudget k m (Tree.heightFor rows.size) := by
  have hp := MergeBuild.prepare_steps (k:=k) rows (Tree.heightFor rows.size)
  have hh := execute_bound (MergeBuild.prepare rows (Tree.heightFor rows.size)).1 p
  have hc := Nat.mul_le_mul_right (Tree.joinBudget k m+Tree.leafBudget k m) (Tree.capacity_upper rows.size)
  change (MergeBuild.prepare rows (Tree.heightFor rows.size)).2+
    (execute (MergeBuild.prepare rows (Tree.heightFor rows.size)).1 p).steps≤_
  omega

end REWB.BoundaryIndex.Mixed
