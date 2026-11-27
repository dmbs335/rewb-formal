import REWB.BoundaryApplicationAddress

namespace REWB.BoundaryApplication.Address
open REWB.BoundaryIndex
open REWB.BoundaryApplication.Heavy
variable {σ : Nat} {A D E : DFA (Fin σ)} {n : Nat}

theorem push_source (s : Store A D E n) (e : Heavy.Entry A D E n) (jump : Option Nat) (rank : Nat)
    (terminal : Option (Endpoint n)) (p : Fin (n+1)) :
    (push s e jump rank terminal).sources.get p=
      if terminal=some (.source p) then some s.nodes.size else s.sources.get p := by
  cases terminal with
  | none => rfl
  | some terminal =>
    cases terminal with
    | target _ => rfl
    | source q =>
      change (s.sources.set q.val (some s.nodes.size) q.isLt)[p.val]=_
      rw [Vector.getElem_set]
      simp only [Option.some.injEq,Endpoint.source.injEq]
      by_cases he : q=p
      · subst p; simp only [if_pos rfl,if_true]
      · have hv : q.val≠p.val := fun h=>he (Fin.ext h)
        simp only [if_neg he,if_neg hv]
        rfl

def SlotsGood (s : Store A D E n) : Prop :=
  ∀(p : Fin (n+1)) (i : Nat),s.sources.get p=some i→
    ∃c,s.nodes[i]?=some c ∧ c.terminal=some (.source p)

theorem push_slots (s : Store A D E n) (e : Heavy.Entry A D E n) (jump : Option Nat) (rank : Nat)
    (terminal : Option (Endpoint n)) (hg : SlotsGood s) : SlotsGood (push s e jump rank terminal) := by
  intro p i hi
  rw [push_source] at hi
  split at hi
  next he =>
    have haddr : s.nodes.size=i := Option.some.inj hi
    subst i
    exact ⟨⟨e,jump,rank,terminal⟩,push_here s e jump rank terminal,he⟩
  next he =>
    obtain ⟨c,hc,ht⟩:=hg p i hi
    exact ⟨c,push_extends s e jump rank terminal i c hc,ht⟩

theorem walk_slots (t : Heavy.Saved A D E n) (s : Store A D E n) (jump : Option Nat) (rank : Nat)
    (hg : SlotsGood s) : SlotsGood (walk t s jump rank) := by
  induction t generalizing s jump rank with
  | leaf e terminal => exact push_slots s e jump rank terminal hg
  | node e b l r ihl ihr => exact ihr _ _ _ (ihl _ _ _ (push_slots s e jump rank none hg))

theorem build_slots (t : Heavy.Saved A D E n) : SlotsGood (build t) := by
  apply walk_slots
  intro p i hi
  simp only [empty,Table.get_ofFn] at hi
  cases hi

theorem push_source_exists (s : Store A D E n) (e : Heavy.Entry A D E n) (jump : Option Nat) (rank : Nat)
    (terminal : Option (Endpoint n)) (p : Fin (n+1)) :
    (∃i,(push s e jump rank terminal).sources.get p=some i) ↔
      (∃i,s.sources.get p=some i) ∨ terminal=some (.source p) := by
  rw [push_source]
  by_cases he : terminal=some (.source p)
  · simp [he]
  · simp [he]

theorem walk_source_exists (t : Heavy.Saved A D E n) (s : Store A D E n) (jump : Option Nat) (rank : Nat)
    (p : Fin (n+1)) :
    (∃i,(walk t s jump rank).sources.get p=some i) ↔
      (∃i,s.sources.get p=some i) ∨ HasSource p t := by
  induction t generalizing s jump rank with
  | leaf e terminal => exact push_source_exists s e jump rank terminal p
  | node e b l r ihl ihr =>
    simp only [walk,ihr,ihl,push_source_exists,reduceCtorEq,or_false,HasSource,or_assoc]

theorem build_source_exists (t : Heavy.Saved A D E n) (p : Fin (n+1)) :
    (∃i,(build t).sources.get p=some i) ↔ HasSource p t := by
  rw [build,walk_source_exists]
  simp only [empty,Table.get_ofFn,reduceCtorEq,exists_false,false_or]

def Bounded (xs : Array (Cell A D E n)) (limit : Nat) : Prop :=
  ∀(i : Nat) (c : Cell A D E n),xs[i]?=some c→c.rank≤limit

theorem push_bounded (s : Store A D E n) (e : Heavy.Entry A D E n) (jump : Option Nat) (rank : Nat)
    (terminal : Option (Endpoint n)) (limit : Nat) (hb : Bounded s.nodes limit) (hr : rank≤limit) :
    Bounded (push s e jump rank terminal).nodes limit := by
  intro i c hi
  rw [push_nodes,Array.getElem?_push] at hi
  split at hi
  · have he : (⟨e,jump,rank,terminal⟩ : Cell A D E n)=c := Option.some.inj hi
    subst c
    exact hr
  · exact hb i c hi

theorem walk_bounded (t : Heavy.Saved A D E n) (s : Store A D E n) (jump : Option Nat) (rank limit : Nat)
    (hb : Bounded s.nodes limit) (ht : rank+Heavy.lightHeight t≤limit) :
    Bounded (walk t s jump rank).nodes limit := by
  induction t generalizing s jump rank with
  | leaf e terminal => exact push_bounded s e jump rank terminal limit hb ht
  | node e b l r ihl ihr =>
    have hroot : rank≤limit := by omega
    have hl : (if b then rank+1 else rank)+Heavy.lightHeight l≤limit := by
      cases b <;> simp only [Heavy.lightHeight,Bool.false_eq_true,if_false,if_true] at ht ⊢ <;> omega
    have hr : (if b then rank else rank+1)+Heavy.lightHeight r≤limit := by
      cases b <;> simp only [Heavy.lightHeight,Bool.false_eq_true,if_false,if_true] at ht ⊢ <;> omega
    exact ihr _ _ _ (ihl _ _ _ (push_bounded s e jump rank none limit hb hroot) hl) hr

theorem build_bounded (t : Heavy.Saved A D E n) : Bounded (build t).nodes (Heavy.lightHeight t) := by
  apply walk_bounded
  · intro i c hi
    simp only [empty,Array.getElem?_empty] at hi
    cases hi
  · omega

def Stored (P : Heavy.Entry A D E n→Prop) (xs : Array (Cell A D E n)) : Prop :=
  ∀(i : Nat) (c : Cell A D E n),xs[i]?=some c→P c.entry

theorem push_stored (P : Heavy.Entry A D E n→Prop) (s : Store A D E n) (e : Heavy.Entry A D E n)
    (jump : Option Nat) (rank : Nat) (terminal : Option (Endpoint n))
    (hs : Stored P s.nodes) (he : P e) : Stored P (push s e jump rank terminal).nodes := by
  intro i c hi
  rw [push_nodes,Array.getElem?_push] at hi
  split at hi
  · have hh : (⟨e,jump,rank,terminal⟩ : Cell A D E n)=c := Option.some.inj hi
    subst c
    exact he
  · exact hs i c hi

theorem walk_stored (P : Heavy.Entry A D E n→Prop) (t : Heavy.Saved A D E n)
    (s : Store A D E n) (jump : Option Nat) (rank : Nat)
    (hs : Stored P s.nodes) (ht : Heavy.All P t) : Stored P (walk t s jump rank).nodes := by
  induction t generalizing s jump rank with
  | leaf e terminal => exact push_stored P s e jump rank terminal hs ht
  | node e b l r ihl ihr => exact ihr _ _ _ (ihl _ _ _ (push_stored P s e jump rank none hs ht.1) ht.2.1) ht.2.2

theorem build_stored (P : Heavy.Entry A D E n→Prop) (t : Heavy.Saved A D E n)
    (ht : Heavy.All P t) : Stored P (build t).nodes := by
  apply walk_stored P t _ _ _ _ ht
  intro i c hi
  simp only [empty,Array.getElem?_empty] at hi
  cases hi

theorem go_nodes (A B D E : DFA (Fin σ)) (w : Word (Fin σ)) (rows : RTable.Shared A B D)
    (ranges : Range.Index A) (base : BoundaryIndex.Tree (Subset.count A) E.stateCount (height w.length))
    (t : TrieFor w) (s : Versions.Snapshot D.stateCount E.stateCount (height w.length))
    (incoming : Merge.State (Subset.count A) E.stateCount (height w.length)) :
    nodes (Heavy.go A B D E w rows ranges base t s incoming).saved=
      (Heavy.go A B D E w rows ranges base t s incoming).allocated := by
  induction t generalizing s incoming with
  | empty => rfl
  | leaf _ => rfl
  | node key depth l r ihl ihr => simp only [Heavy.go,nodes,ihl,ihr]

theorem go_source (A B D E : DFA (Fin σ)) (w : Word (Fin σ)) (rows : RTable.Shared A B D)
    (ranges : Range.Index A) (base : BoundaryIndex.Tree (Subset.count A) E.stateCount (height w.length))
    (t : TrieFor w) (s : Versions.Snapshot D.stateCount E.stateCount (height w.length))
    (incoming : Merge.State (Subset.count A) E.stateCount (height w.length)) (p : Fin (w.length+1)) :
    HasSource p (Heavy.go A B D E w rows ranges base t s incoming).saved ↔
      ∃a,a∈t.leaves ∧ a.record=.source p := by
  induction t generalizing s incoming with
  | empty => simp only [Heavy.go,HasSource,reduceCtorEq,BoundaryTrie.Tree.leaves,List.not_mem_nil,false_and,exists_false]
  | leaf key => simp only [Heavy.go,HasSource,Option.some.injEq,BoundaryTrie.Tree.leaves,List.mem_singleton,exists_eq_left]
  | node key depth l r ihl ihr =>
    simp only [Heavy.go,HasSource,ihl,ihr,BoundaryTrie.Tree.leaves,List.mem_append]
    constructor
    · rintro (⟨a,ha,he⟩|⟨a,ha,he⟩)
      · exact ⟨a,Or.inl ha,he⟩
      · exact ⟨a,Or.inr ha,he⟩
    · rintro ⟨a,ha|ha,he⟩
      · exact Or.inl ⟨a,ha,he⟩
      · exact Or.inr ⟨a,ha,he⟩

end REWB.BoundaryApplication.Address
