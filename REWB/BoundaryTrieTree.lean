import REWB.BoundaryTrieKeys

/-! A binary refinement of a compressed prefix trie. Every input record
has its own terminal leaf. Duplicate keys and keys terminating at a branch
therefore permit zero-length refinement edges. Internal labels are stored
as one representative descriptor and one depth, never copied words. -/
namespace REWB.BoundaryTrie
variable {n σ : Nat} {ρ : Type}

inductive Tree (n : Nat) (ρ : Type) where
  | empty : Tree n ρ
  | leaf : Key n ρ → Tree n ρ
  | node : Key n ρ → Nat → Tree n ρ → Tree n ρ → Tree n ρ
  deriving Repr

namespace Tree

def leaves : Tree n ρ→List (Key n ρ)
  | .empty => []
  | .leaf a => [a]
  | .node _ _ l r => leaves l++leaves r

def nodes : Tree n ρ→Nat
  | .empty => 0
  | .leaf _ => 1
  | .node _ _ l r => nodes l+nodes r+1

def depth : Tree n ρ→Nat
  | .empty => 0
  | .leaf a => a.length
  | .node _ d _ _ => d

def Good (f : Nat→Fin σ) : Tree n ρ→Prop
  | .empty => True
  | .leaf _ => True
  | .node a d l r =>
    Good f l ∧ Good f r ∧ leaves l≠[] ∧ leaves r≠[] ∧ a∈leaves l ∧
    (∀b,b∈leaves l++leaves r→Key.Common f a b d) ∧
    (∀b,b∈leaves l→∀c,c∈leaves r→Key.Exact f b c d)

/-- A path is a sequence of actual left/right child choices. -/
def lookup : Tree n ρ→List Bool→Option (Key n ρ)
  | .empty,_ => none
  | .leaf a,[] => some a
  | .leaf _,_::_ => none
  | .node _ _ _ _,[] => none
  | .node _ _ l r,b::path => lookup (if b then r else l) path

theorem lookup_mem (t : Tree n ρ) (path : List Bool) (a : Key n ρ)
    (h : lookup t path=some a) : a∈leaves t := by
  induction t generalizing path with
  | empty => simp only [lookup] at h; cases h
  | leaf b =>
    cases path with
    | nil => simp only [lookup,Option.some.injEq] at h; simp only [leaves,List.mem_singleton,h]
    | cons p path => cases h
  | node b d l r ihl ihr =>
    cases path with
    | nil => cases h
    | cons p path =>
      cases p with
      | false => exact List.mem_append_left _ (ihl path h)
      | true => exact List.mem_append_right _ (ihr path h)

theorem mem_lookup (t : Tree n ρ) (a : Key n ρ) (h : a∈leaves t) :
    ∃path,lookup t path=some a := by
  induction t with
  | empty => simp only [leaves,List.not_mem_nil] at h
  | leaf b =>
    simp only [leaves,List.mem_singleton] at h
    exact ⟨[],by simp only [lookup,h]⟩
  | node b d l r ihl ihr =>
    rcases List.mem_append.mp h with hl | hr
    · obtain ⟨path,hp⟩:=ihl hl
      exact ⟨false::path,hp⟩
    · obtain ⟨path,hp⟩:=ihr hr
      exact ⟨true::path,hp⟩

theorem lookup_iff_mem (t : Tree n ρ) (a : Key n ρ) :
    (∃path,lookup t path=some a) ↔ a∈leaves t :=
  ⟨fun ⟨path,hp⟩=>lookup_mem t path a hp,mem_lookup t a⟩

/-- The common-ancestor witness follows the actual binary paths. A leaf
compared with itself has its full key length; a divergence uses the
stored branch depth. -/
inductive LCA : Tree n ρ→Key n ρ→Key n ρ→Nat→Prop
  | leaf (a) : LCA (.leaf a) a a a.length
  | left {stem d l r a b e} : LCA l a b e→LCA (.node stem d l r) a b e
  | right {stem d l r a b e} : LCA r a b e→LCA (.node stem d l r) a b e
  | cross {stem d l r a b} : a∈leaves l→b∈leaves r→LCA (.node stem d l r) a b d
  | crossRev {stem d l r a b} : a∈leaves r→b∈leaves l→LCA (.node stem d l r) a b d

theorem lca_complete (t : Tree n ρ) (a b : Key n ρ)
    (ha : a∈leaves t) (hb : b∈leaves t) : ∃d,LCA t a b d := by
  induction t with
  | empty => simp only [leaves,List.not_mem_nil] at ha
  | leaf c =>
    simp only [leaves,List.mem_singleton] at ha hb
    subst a
    subst b
    exact ⟨c.length,.leaf c⟩
  | node stem d l r ihl ihr =>
    rcases List.mem_append.mp ha with hal | har
    · rcases List.mem_append.mp hb with hbl | hbr
      · obtain ⟨e,he⟩:=ihl hal hbl
        exact ⟨e,.left he⟩
      · exact ⟨d,.cross hal hbr⟩
    · rcases List.mem_append.mp hb with hbl | hbr
      · exact ⟨d,.crossRev har hbl⟩
      · obtain ⟨e,he⟩:=ihr har hbr
        exact ⟨e,.right he⟩

theorem lca_exact (f : Nat→Fin σ) (t : Tree n ρ) (a b : Key n ρ) (d : Nat)
    (hg : Good f t) (h : LCA t a b d) : Key.Exact f a b d := by
  induction h with
  | leaf a => exact ⟨⟨Nat.le_refl _,Nat.le_refl _,rfl⟩,fun _ he=>he.1⟩
  | left h ih => exact ih hg.1
  | right h ih => exact ih hg.2.1
  | cross hal hbr => exact hg.2.2.2.2.2.2 _ hal _ hbr
  | crossRev har hbl =>
    have hh:=hg.2.2.2.2.2.2 _ hbl _ har
    exact ⟨(Key.common_symmetric _ _ _ _).mp hh.1,
      fun e he=>hh.2 e ((Key.common_symmetric _ _ _ _).mp he)⟩

theorem path_commonPrefix (f : Nat→Fin σ) (t : Tree n ρ) (a b : Key n ρ)
    (pa pb : List Bool) (hg : Good f t)
    (ha : lookup t pa=some a) (hb : lookup t pb=some b) :
    ∃d,LCA t a b d ∧ Key.Exact f a b d := by
  obtain ⟨d,hd⟩:=lca_complete t a b (lookup_mem t pa a ha) (lookup_mem t pb b hb)
  exact ⟨d,hd,lca_exact f t a b d hg hd⟩

theorem depth_common (f : Nat→Fin σ) (t : Tree n ρ)
    (hg : Good f t) (a b : Key n ρ) (ha : a∈leaves t) (hb : b∈leaves t) :
    Key.Common f a b (depth t) := by
  cases t with
  | empty => simp only [leaves,List.not_mem_nil] at ha
  | leaf c =>
    simp only [leaves,List.mem_singleton] at ha hb
    subst a
    subst b
    exact ⟨Nat.le_refl _,Nat.le_refl _,rfl⟩
  | node stem d l r =>
    have hca:=hg.2.2.2.2.2.1 a ha
    have hcb:=hg.2.2.2.2.2.1 b hb
    exact Key.common_trans f a stem b d ((Key.common_symmetric _ _ _ _).mp hca) hcb

theorem edge_depths (f : Nat→Fin σ) (stem : Key n ρ) (d : Nat) (l r : Tree n ρ)
    (hg : Good f (.node stem d l r)) : d≤depth l ∧ d≤depth r := by
  have lower : ∀(child : Tree n ρ),Good f child→leaves child≠[]→
      (∀a,a∈leaves child→Key.Common f stem a d)→d≤depth child := by
    intro child hc hn hp
    cases child with
    | empty => exact False.elim (hn rfl)
    | leaf a => exact (hp a (by simp only [leaves,List.mem_singleton])).2.1
    | node s e a b =>
      obtain ⟨x,hx⟩:=List.exists_mem_of_ne_nil (leaves a) hc.2.2.1
      obtain ⟨y,hy⟩:=List.exists_mem_of_ne_nil (leaves b) hc.2.2.2.1
      have he:=hc.2.2.2.2.2.2 x hx y hy
      have hpx:=hp x (List.mem_append_left _ hx)
      have hpy:=hp y (List.mem_append_right _ hy)
      exact he.2 d (Key.common_trans f x stem y d
        ((Key.common_symmetric _ _ _ _).mp hpx) hpy)
  exact ⟨lower l hg.1 hg.2.2.1
      (fun a ha=>hg.2.2.2.2.2.1 a (List.mem_append_left _ ha)),
    lower r hg.2.1 hg.2.2.2.1
      (fun a ha=>hg.2.2.2.2.2.1 a (List.mem_append_right _ ha))⟩

end Tree
end REWB.BoundaryTrie
