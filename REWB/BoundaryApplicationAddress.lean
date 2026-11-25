import REWB.BoundaryApplicationHeavySound

/-! Materialize the saved heavy-path versions into a direct-address
array. A linear preorder pass writes each node once, maintains the source
endpoint-to-leaf-address vector, and stores the parent of the heavy-chain
head as one jump. The cached rank is the number of light edges above a
node. No root-to-leaf path list is constructed or searched.

Counters charge array push/set and scalar metadata operations; they do
not claim a bit/allocator bound for the Lean runtime. -/
namespace REWB.BoundaryApplication.Address
open REWB.BoundaryIndex
open REWB.BoundaryApplication.Heavy
variable {σ : Nat} {A D E : DFA (Fin σ)} {n : Nat}

structure Cell (A D E : DFA (Fin σ)) (n : Nat) where
  entry : Heavy.Entry A D E n
  jump : Option Nat
  rank : Nat
  terminal : Option (Endpoint n)

structure Store (A D E : DFA (Fin σ)) (n : Nat) where
  nodes : Array (Cell A D E n)
  sources : Vector (Option Nat) (n+1)
  work : Nat

def empty (A D E : DFA (Fin σ)) (n : Nat) : Store A D E n :=
  ⟨#[],Vector.ofFn (fun _=>none),n+2⟩

def push (s : Store A D E n) (e : Heavy.Entry A D E n) (jump : Option Nat) (rank : Nat)
    (terminal : Option (Endpoint n)) : Store A D E n :=
  let addr:=s.nodes.size
  let sources:=match terminal with
    | some (.source p) => s.sources.set p.val (some addr) p.isLt
    | _ => s.sources
  ⟨s.nodes.push ⟨e,jump,rank,terminal⟩,sources,s.work+12⟩

def walk : Heavy.Saved A D E n→Store A D E n→Option Nat→Nat→Store A D E n
  | .leaf e terminal,s,jump,rank => push s e jump rank terminal
  | .node e chooseRight l r,s,jump,rank =>
    let addr:=s.nodes.size
    let out:=push s e jump rank none
    let mid:=walk l out (if chooseRight then some addr else jump) (if chooseRight then rank+1 else rank)
    walk r mid (if chooseRight then jump else some addr) (if chooseRight then rank else rank+1)

def build (t : Heavy.Saved A D E n) : Store A D E n := walk t (empty A D E n) none 0

/-- Structural specifications only; neither is scanned by `walk`. -/
def nodes : Heavy.Saved A D E n→Nat
  | .leaf _ _ => 1
  | .node _ _ l r => nodes l+nodes r+1

def HasSource (p : Fin (n+1)) : Heavy.Saved A D E n→Prop
  | .leaf _ terminal => terminal=some (.source p)
  | .node _ _ l r => HasSource p l ∨ HasSource p r

def Extends (xs ys : Array (Cell A D E n)) : Prop :=
  ∀(i : Nat) (c : Cell A D E n),xs[i]?=some c→ys[i]?=some c

theorem extends_refl (xs : Array (Cell A D E n)) : Extends xs xs := fun _ _ h=>h
theorem extends_trans {xs ys zs : Array (Cell A D E n)} (hxy : Extends xs ys) (hyz : Extends ys zs) :
    Extends xs zs := fun i c h=>hyz i c (hxy i c h)

theorem push_nodes (s : Store A D E n) (e : Heavy.Entry A D E n) (jump : Option Nat) (rank : Nat)
    (terminal : Option (Endpoint n)) :
    (push s e jump rank terminal).nodes=s.nodes.push ⟨e,jump,rank,terminal⟩ := rfl

theorem push_extends (s : Store A D E n) (e : Heavy.Entry A D E n) (jump : Option Nat) (rank : Nat)
    (terminal : Option (Endpoint n)) : Extends s.nodes (push s e jump rank terminal).nodes := by
  intro i c hi
  have hlt : i<s.nodes.size := (Array.getElem?_eq_some_iff.mp hi).1
  rw [push_nodes,Array.getElem?_push]
  simp only [if_neg (by omega : i≠s.nodes.size),hi]

theorem push_here (s : Store A D E n) (e : Heavy.Entry A D E n) (jump : Option Nat) (rank : Nat)
    (terminal : Option (Endpoint n)) :
    (push s e jump rank terminal).nodes[s.nodes.size]?=some ⟨e,jump,rank,terminal⟩ :=
  Array.getElem?_push_size

theorem walk_extends (t : Heavy.Saved A D E n) (s : Store A D E n) (jump : Option Nat) (rank : Nat) :
    Extends s.nodes (walk t s jump rank).nodes := by
  induction t generalizing s jump rank with
  | leaf e terminal => exact push_extends s e jump rank terminal
  | node e b l r ihl ihr =>
    exact extends_trans (push_extends s e jump rank none) (extends_trans (ihl _ _ _) (ihr _ _ _))

theorem walk_size (t : Heavy.Saved A D E n) (s : Store A D E n) (jump : Option Nat) (rank : Nat) :
    (walk t s jump rank).nodes.size=s.nodes.size+nodes t := by
  induction t generalizing s jump rank with
  | leaf e terminal => simp only [walk,push,Array.size_push,nodes]
  | node e b l r ihl ihr =>
    simp only [walk,ihr,ihl,push,Array.size_push,nodes]
    omega

theorem walk_work (t : Heavy.Saved A D E n) (s : Store A D E n) (jump : Option Nat) (rank : Nat) :
    (walk t s jump rank).work=s.work+12*nodes t := by
  induction t generalizing s jump rank with
  | leaf e terminal => simp only [walk,push,nodes,Nat.mul_one]
  | node e b l r ihl ihr =>
    simp only [walk,ihr,ihl,push,nodes,Nat.mul_add,Nat.mul_one]
    omega

theorem build_size (t : Heavy.Saved A D E n) : (build t).nodes.size=nodes t := by
  rw [build,walk_size]
  exact Nat.zero_add _

theorem build_work (t : Heavy.Saved A D E n) : (build t).work=n+2+12*nodes t := walk_work _ _ _ _

/-- The head-parent jump either ends at rank zero or reaches a stored
node whose rank is exactly one smaller. -/
def AtRank (xs : Array (Cell A D E n)) (jump : Option Nat) (rank : Nat) : Prop :=
  match jump with
  | none => rank=0
  | some i => ∃c,xs[i]?=some c ∧ c.rank+1=rank

def Good (xs : Array (Cell A D E n)) : Prop :=
  ∀(i : Nat) (c : Cell A D E n),xs[i]?=some c→AtRank xs c.jump c.rank

theorem rank_extends {xs ys : Array (Cell A D E n)} (hxy : Extends xs ys)
    (jump : Option Nat) (rank : Nat) (hr : AtRank xs jump rank) : AtRank ys jump rank := by
  cases jump with
  | none => exact hr
  | some i => obtain ⟨c,hc,he⟩:=hr; exact ⟨c,hxy i c hc,he⟩

theorem push_good (s : Store A D E n) (e : Heavy.Entry A D E n) (jump : Option Nat) (rank : Nat)
    (terminal : Option (Endpoint n)) (hg : Good s.nodes) (hr : AtRank s.nodes jump rank) :
    Good (push s e jump rank terminal).nodes := by
  intro i c hi
  rw [push_nodes,Array.getElem?_push] at hi
  split at hi
  · have he : (⟨e,jump,rank,terminal⟩ : Cell A D E n)=c := Option.some.inj hi
    subst c
    exact rank_extends (push_extends s e jump rank terminal) jump rank hr
  · exact rank_extends (push_extends s e jump rank terminal) c.jump c.rank (hg i c hi)

theorem walk_good (t : Heavy.Saved A D E n) (s : Store A D E n) (jump : Option Nat) (rank : Nat)
    (hg : Good s.nodes) (hr : AtRank s.nodes jump rank) : Good (walk t s jump rank).nodes := by
  induction t generalizing s jump rank with
  | leaf e terminal => exact push_good s e jump rank terminal hg hr
  | node e b l r ihl ihr =>
    let out:=push s e jump rank none
    have ho : Good out.nodes := push_good s e jump rank none hg hr
    have hkeep : AtRank out.nodes jump rank := rank_extends (push_extends s e jump rank none) jump rank hr
    have hlight : AtRank out.nodes (some s.nodes.size) (rank+1) :=
      ⟨⟨e,jump,rank,none⟩,push_here s e jump rank none,rfl⟩
    have hl : AtRank out.nodes (if b then some s.nodes.size else jump) (if b then rank+1 else rank) := by
      cases b <;> assumption
    have hmid:=ihl out _ _ ho hl
    apply ihr _ _ _ hmid
    apply rank_extends (walk_extends l out _ _)
    cases b <;> assumption

theorem build_good (t : Heavy.Saved A D E n) : Good (build t).nodes := by
  apply walk_good
  · intro i c hi
    simp only [empty,Array.getElem?_empty] at hi
    cases hi
  · rfl

end REWB.BoundaryApplication.Address
