import REWB.MaskedOrderedOwnerSnapshot
import REWB.BoundaryApplicationStartLocateIndex

/-! A counted preorder annotation of the actual suffix descriptor trie.
Only an integer owner-array address and a terminal suffix start are copied.
The next free address is threaded through both children: no subtree sizes,
leaf lists, or text positions are traversed to compute child addresses. -/
namespace REWB.MaskedSuffixClass
open REWB.BoundaryTrie
abbrev Locator := REWB.BoundaryApplication.StartLocate.Tree Nat
open REWB.BoundaryApplication
variable {n σ : Nat}

structure Annotated (n : Nat) where
  tree : Locator (n+1)
  next : Nat
  work : Nat

def terminal (a : Key n Nat) : Fin (n+1) :=
  ⟨a.start,by have hh:=a.bounded; omega⟩

def annotate : Tree n Nat→Nat→Annotated n
  | .empty,base => ⟨.leaf 0 base none,base+1,4⟩
  | .leaf a,base => ⟨.leaf a.length base (some (terminal a)),base+1,5⟩
  | .node _ d l r,base =>
    let a:=annotate l (base+1)
    let b:=annotate r a.next
    ⟨.node d base a.tree b.tree,b.next,a.work+b.work+5⟩

theorem annotate_next (t : Tree n Nat) (base : Nat) :
    (annotate t base).next=base+MaskedOrdered.Owner.slots t := by
  induction t generalizing base with
  | empty => rfl
  | leaf _ => rfl
  | node _ _ l r il ir =>
    simp only [annotate,ir,il,MaskedOrdered.Owner.slots]
    omega

theorem annotate_nodes (t : Tree n Nat) (base : Nat) :
    (annotate t base).tree.nodes=MaskedOrdered.Owner.slots t := by
  induction t generalizing base with
  | empty => rfl
  | leaf _ => rfl
  | node _ _ l r il ir => simp only [annotate,StartLocate.Tree.nodes,ir,il,MaskedOrdered.Owner.slots]

theorem annotate_work (t : Tree n Nat) (base : Nat) :
    (annotate t base).work≤5*MaskedOrdered.Owner.slots t := by
  induction t generalizing base with
  | empty => change 4≤5; decide
  | leaf _ => exact Nat.le_refl _
  | node _ _ l r il ir =>
    have hl:=il (base+1)
    have hr:=ir (annotate l (base+1)).next
    simp only [annotate,MaskedOrdered.Owner.slots]
    omega

theorem annotate_depth (t : Tree n Nat) (base : Nat) :
    (annotate t base).tree.depth=t.depth := by cases t <;> rfl

theorem annotate_payload (t : Tree n Nat) (base : Nat) :
    (annotate t base).tree.payload=base := by cases t <;> rfl

theorem annotate_good (f : Nat→Fin σ) (t : Tree n Nat) (base : Nat)
    (hg : t.Good f) : (annotate t base).tree.Good := by
  induction t generalizing base with
  | empty => trivial
  | leaf _ => trivial
  | node stem d l r il ir =>
    refine ⟨il _ hg.1,ir _ hg.2.1,?_,?_⟩
    · rw [annotate_depth]; exact (Tree.edge_depths f stem d l r hg).1
    · rw [annotate_depth]; exact (Tree.edge_depths f stem d l r hg).2

theorem annotate_target (t : Tree n Nat) (base : Nat) (p : Fin (n+1)) :
    StartLocate.HasTarget p (annotate t base).tree ↔ ∃a,a∈t.leaves ∧ a.start=p.val := by
  induction t generalizing base with
  | empty => simp [annotate,StartLocate.HasTarget,Tree.leaves]
  | leaf a =>
    simp only [annotate,StartLocate.HasTarget,Option.some.injEq,Tree.leaves,List.mem_singleton]
    constructor
    · intro h
      exact ⟨a,rfl,congrArg Fin.val h⟩
    · rintro ⟨b,rfl,h⟩
      exact Fin.ext h
  | node _ _ l r il ir =>
    simp only [annotate,StartLocate.HasTarget,il,ir,Tree.leaves,List.mem_append]
    constructor
    · rintro (⟨a,ha,hp⟩|⟨a,ha,hp⟩)
      · exact ⟨a,Or.inl ha,hp⟩
      · exact ⟨a,Or.inr ha,hp⟩
    · rintro ⟨a,ha,hp⟩
      rcases ha with ha|ha
      · exact Or.inl ⟨a,ha,hp⟩
      · exact Or.inr ⟨a,ha,hp⟩

theorem annotate_targetDepth (t : Tree n Nat) (base : Nat) (p : Fin (n+1)) (H : Nat)
    (hd : ∀a,a∈t.leaves→a.start=p.val→H≤a.length) :
    StartLocate.TargetDepth p H (annotate t base).tree := by
  induction t generalizing base with
  | empty => intro he; cases he
  | leaf a =>
    intro he
    exact hd a (by simp [Tree.leaves]) (congrArg Fin.val (Option.some.inj he))
  | node _ _ l r il ir =>
    exact ⟨il _ (fun a ha=>hd a (List.mem_append_left _ ha)),
      ir _ (fun a ha=>hd a (List.mem_append_right _ ha))⟩

end REWB.MaskedSuffixClass
