import REWB.BoundaryApplicationStartLocate

/-! One preorder pass materializes every parent row and terminal slot.
No input-size traversal is performed: the supplied level count comes
from a cached upper bound at the caller. Earlier cells and payloads are
preserved, and every terminal slot follows its actual final write. -/
namespace REWB.BoundaryApplication.StartLocate
universe u
variable {κ : Type u} {terminals : Nat}

structure Store (κ : Type u) (terminals : Nat) where
  cells : Array (Cell κ)
  targets : Vector (Option Nat) terminals
  work : Nat

def empty (κ : Type u) (terminals : Nat) : Store κ terminals :=
  ⟨#[],Vector.replicate terminals none,terminals+1⟩

def push (levels : Nat) (s : Store κ terminals) (par : Option Nat) (d : Nat) (a : κ)
    (terminal : Option (Fin terminals)) : Store κ terminals :=
  let out:=makeCell levels s.cells par d a
  let labels:=match terminal with
    | none => (s.targets,1)
    | some p => (s.targets.set p (some s.cells.size),3)
  ⟨s.cells.push out.1,labels.1,s.work+out.2+labels.2+3⟩

def walk (levels : Nat) : Tree κ terminals→Store κ terminals→Option Nat→Store κ terminals
  | .leaf d a terminal,s,par => push levels s par d a terminal
  | .node d a l r,s,par =>
    let root:=s.cells.size
    let out:=push levels s par d a none
    let mid:=walk levels l out (some root)
    walk levels r mid (some root)

def build (levels : Nat) (t : Tree κ terminals) : Store κ terminals :=
  walk levels t (empty κ terminals) none

theorem extends_trans {xs ys zs : Array (Cell κ)} (hxy : Extends xs ys) (hyz : Extends ys zs) : Extends xs zs :=
  fun i c hi=>hyz i c (hxy i c hi)

theorem push_cells (levels : Nat) (s : Store κ terminals) (par : Option Nat) (d : Nat) (a : κ)
    (terminal : Option (Fin terminals)) :
    (push levels s par d a terminal).cells=s.cells.push (makeCell levels s.cells par d a).1 := rfl

theorem push_size (levels : Nat) (s : Store κ terminals) (par : Option Nat) (d : Nat) (a : κ)
    (terminal : Option (Fin terminals)) : (push levels s par d a terminal).cells.size=s.cells.size+1 := by
  rw [push_cells,Array.size_push]

theorem push_keep (levels : Nat) (s : Store κ terminals) (par : Option Nat) (d : Nat) (a : κ)
    (terminal : Option (Fin terminals)) : Extends s.cells (push levels s par d a terminal).cells :=
  push_extends s.cells _

theorem push_here (levels : Nat) (s : Store κ terminals) (par : Option Nat) (d : Nat) (a : κ)
    (terminal : Option (Fin terminals)) :
    (push levels s par d a terminal).cells[s.cells.size]?=some (makeCell levels s.cells par d a).1 :=
  Array.getElem?_push_size

theorem push_target (levels : Nat) (s : Store κ terminals) (par : Option Nat) (d : Nat) (a : κ)
    (terminal : Option (Fin terminals)) (p : Fin terminals) :
    (push levels s par d a terminal).targets.get p=
      if terminal=some p then some s.cells.size else s.targets.get p := by
  cases terminal with
  | none => rfl
  | some q =>
    change (s.targets.set q.val (some s.cells.size)).get p=(if some q=some p then some s.cells.size else s.targets.get p)
    change (s.targets.set q.val (some s.cells.size))[p.val]=_
    rw [Vector.getElem_set]
    by_cases hqp : q=p
    · subst q; simp
    · have hval : q.val≠p.val := fun he=>hqp (Fin.ext he)
      simp only [hval,if_false,Option.some.injEq,hqp]
      rfl

theorem push_work (levels : Nat) (s : Store κ terminals) (par : Option Nat) (d : Nat) (a : κ)
    (terminal : Option (Fin terminals)) :
    (push levels s par d a terminal).work≤s.work+6*levels+8 := by
  have hh:=makeCell_work levels s.cells par d a
  cases terminal <;> simp only [push] <;> omega

theorem walk_extends (levels : Nat) (t : Tree κ terminals) (s : Store κ terminals) (par : Option Nat) :
    Extends s.cells (walk levels t s par).cells := by
  induction t generalizing s par with
  | leaf d a terminal => exact push_keep levels s par d a terminal
  | node d a l r ihl ihr =>
    exact extends_trans (push_keep levels s par d a none)
      (extends_trans (ihl _ _) (ihr _ _))

theorem walk_size (levels : Nat) (t : Tree κ terminals) (s : Store κ terminals) (par : Option Nat) :
    (walk levels t s par).cells.size=s.cells.size+t.nodes := by
  induction t generalizing s par with
  | leaf d a terminal => exact push_size levels s par d a terminal
  | node d a l r ihl ihr =>
    simp only [walk,ihl,ihr,push_size,Tree.nodes]
    omega

theorem walk_work (levels : Nat) (t : Tree κ terminals) (s : Store κ terminals) (par : Option Nat) :
    (walk levels t s par).work≤s.work+t.nodes*(6*levels+8) := by
  induction t generalizing s par with
  | leaf d a terminal =>
    have hh:=push_work levels s par d a terminal
    simpa only [Tree.nodes,Nat.one_mul,Nat.add_assoc,walk] using hh
  | node d a l r ihl ihr =>
    have hl:=ihl (push levels s par d a none) (some s.cells.size)
    have hr:=ihr (walk levels l (push levels s par d a none) (some s.cells.size)) (some s.cells.size)
    have hp:=push_work levels s par d a none
    simp only [walk,Tree.nodes,Nat.add_mul,Nat.one_mul]
    omega

theorem walk_good (levels : Nat) (t : Tree κ terminals) (s : Store κ terminals) (par : Option Nat)
    (hg : Good levels s.cells) (hp : ∀i,par=some i→i<s.cells.size) :
    Good levels (walk levels t s par).cells := by
  induction t generalizing s par with
  | leaf d a terminal => exact makeCell_good levels s.cells hg par hp d a
  | node d a l r ihl ihr =>
    have hpush : Good levels (push levels s par d a none).cells := makeCell_good levels s.cells hg par hp d a
    have hroot : ∀i,some s.cells.size=some i→i<(push levels s par d a none).cells.size := by
      intro i hi
      have he : s.cells.size=i := Option.some.inj hi
      rw [push_size]
      omega
    apply ihr
    · exact ihl _ _ hpush hroot
    · intro i hi
      rw [walk_size,push_size]
      have he : s.cells.size=i := Option.some.inj hi
      omega

theorem empty_good (levels : Nat) : Good levels (empty κ terminals).cells := by
  constructor
  · intro i c hi
    simp only [empty,Array.getElem?_empty] at hi
    cases hi
  · intro i c hi
    simp only [empty,Array.getElem?_empty] at hi
    cases hi

theorem build_good (levels : Nat) (t : Tree κ terminals) : Good levels (build levels t).cells :=
  walk_good levels t (empty κ terminals) none (empty_good levels) (by intro i hi; cases hi)

theorem build_size (levels : Nat) (t : Tree κ terminals) : (build levels t).cells.size=t.nodes := by
  simpa only [build,empty,Array.size_empty,Nat.zero_add] using walk_size levels t (empty κ terminals) none

theorem build_work (levels : Nat) (t : Tree κ terminals) :
    (build levels t).work≤terminals+1+t.nodes*(6*levels+8) :=
  walk_work levels t (empty κ terminals) none

def HasTarget (p : Fin terminals) : Tree κ terminals→Prop
  | .leaf _ _ terminal => terminal=some p
  | .node _ _ l r => HasTarget p l ∨ HasTarget p r

/-- The original annotated-tree path of the terminal whose slot was
actually stored. Every root-to-leaf cell retains its exact payload,
word depth, and parent address. The relation is erased from execution. -/
inductive Path (xs : Array (Cell κ)) (p : Fin terminals) :
    Option Nat→Tree κ terminals→Nat→Prop
  | leaf {par d a terminal i c} : xs[i]?=some c→c.depth=d→c.payload=a→c.parent=par→
      terminal=some p→Path xs p par (.leaf d a terminal) i
  | left {par d a l r i c j} : xs[i]?=some c→c.depth=d→c.payload=a→c.parent=par→
      Path xs p (some i) l j→Path xs p par (.node d a l r) j
  | right {par d a l r i c j} : xs[i]?=some c→c.depth=d→c.payload=a→c.parent=par→
      Path xs p (some i) r j→Path xs p par (.node d a l r) j

theorem path_extends {xs ys : Array (Cell κ)} (hxy : Extends xs ys)
    (p : Fin terminals) (par : Option Nat) (t : Tree κ terminals) (i : Nat)
    (hp : Path xs p par t i) : Path ys p par t i := by
  induction hp with
  | leaf hi hd ha hpar hterm => exact Path.leaf (hxy _ _ hi) hd ha hpar hterm
  | left hi hd ha hpar _ ih => exact Path.left (hxy _ _ hi) hd ha hpar ih
  | right hi hd ha hpar _ ih => exact Path.right (hxy _ _ hi) hd ha hpar ih

theorem walk_unchanged (levels : Nat) (t : Tree κ terminals) (s : Store κ terminals)
    (par : Option Nat) (p : Fin terminals) (hn : ¬HasTarget p t) :
    (walk levels t s par).targets.get p=s.targets.get p := by
  induction t generalizing s par with
  | leaf d a terminal =>
    exact (push_target levels s par d a terminal p).trans (if_neg hn)
  | node d a l r ihl ihr =>
    have hl : ¬HasTarget p l := fun h=>hn (Or.inl h)
    have hr : ¬HasTarget p r := fun h=>hn (Or.inr h)
    simp only [walk,ihr _ _ hr,ihl _ _ hl,push_target,reduceCtorEq,if_false]

theorem walk_path (levels : Nat) (t : Tree κ terminals) (s : Store κ terminals)
    (par : Option Nat) (p : Fin terminals) (ht : HasTarget p t) :
    ∃i,(walk levels t s par).targets.get p=some i ∧ Path (walk levels t s par).cells p par t i := by
  induction t generalizing s par with
  | leaf d a terminal =>
    refine ⟨s.cells.size,?_,Path.leaf (push_here levels s par d a terminal) rfl rfl rfl ht⟩
    exact (push_target levels s par d a terminal p).trans (if_pos ht)
  | node d a l r ihl ihr =>
    let out:=push levels s par d a none
    let mid:=walk levels l out (some s.cells.size)
    have hroot : (walk levels r mid (some s.cells.size)).cells[s.cells.size]?=
        some (makeCell levels s.cells par d a).1 :=
      walk_extends levels r mid _ _ _ (walk_extends levels l out _ _ _ (push_here levels s par d a none))
    by_cases hr : HasTarget p r
    · obtain ⟨i,hi,hpath⟩:=ihr mid (some s.cells.size) hr
      exact ⟨i,hi,Path.right hroot rfl rfl rfl hpath⟩
    · have hl : HasTarget p l := by
        rcases ht with hl | ht
        · exact hl
        · exact False.elim (hr ht)
      obtain ⟨i,hi,hpath⟩:=ihl out (some s.cells.size) hl
      refine ⟨i,?_,Path.left hroot rfl rfl rfl (path_extends (walk_extends levels r mid _) p _ _ _ hpath)⟩
      exact (walk_unchanged levels r mid _ p hr).trans hi

theorem build_path (levels : Nat) (t : Tree κ terminals) (p : Fin terminals) (ht : HasTarget p t) :
    ∃i,(build levels t).targets.get p=some i ∧ Path (build levels t).cells p none t i :=
  walk_path levels t (empty κ terminals) none p ht

end REWB.BoundaryApplication.StartLocate
