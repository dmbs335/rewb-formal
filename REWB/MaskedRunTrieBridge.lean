import REWB.MaskedRunCoverage
import REWB.MaskedRunDiscoveryEvents

/-! A concrete binary merge schedule from the constructed suffix trie.
Only substring starts become occurrence records. The empty constructor
is rejected rather than inventing a record. LCA splits retain their
actual trie depth for the later complete-owner event execution. -/
namespace REWB.MaskedRunTrieBridge
open REWB.BoundaryTrie REWB.MaskedRunDiscovery
open REWB.MaskedEventBudget (MergeTree)
variable {n σ : Nat}

def compile : Tree n Nat→Option MergeTree×Nat
  | .empty => (none,1)
  | .leaf a => (some (.leaf a.start),2)
  | .node _ _ l r =>
    let a:=compile l
    let b:=compile r
    ((do let x←a.1; let y←b.1; pure (.node x y)),a.2+b.2+3)

theorem compile_work (t : Tree n Nat) : (compile t).2≤4*t.nodes+1 := by
  induction t with
  | empty => exact Nat.le_refl _
  | leaf a => change 2≤5; decide
  | node _ _ l r il ir =>
    simp only [compile,Tree.nodes]
    omega

theorem compile_correct (f : Nat→Fin σ) (t : Tree n Nat)
    (hg : t.Good f) (hn : t.leaves≠[]) :
    ∃m,(compile t).1=some m ∧ MaskedEventBudget.leaves m=positions t ∧
      MaskedEventBudget.size m=t.leaves.length := by
  induction t with
  | empty => exact False.elim (hn rfl)
  | leaf a => exact ⟨.leaf a.start,rfl,rfl,rfl⟩
  | node _ _ l r il ir =>
    obtain ⟨a,ha,hea,hsa⟩:=il hg.1 hg.2.2.1
    obtain ⟨b,hb,heb,hsb⟩:=ir hg.2.1 hg.2.2.2.1
    refine ⟨.node a b,by simp [compile,ha,hb],?_,?_⟩
    · simp only [MaskedEventBudget.leaves,hea,heb,positions,Tree.leaves,List.map_append]
    · simp only [MaskedEventBudget.size,hsa,hsb,Tree.leaves,List.length_append]

theorem suffix_starts (n : Nat) : (suffixKeys n).map Key.start=List.range (n+1) := by
  apply List.ext_getElem?
  intro i
  simp only [suffixKeys,List.getElem?_map,List.getElem?_ofFn]
  by_cases hi : i<n+1
  · simp [hi,suffixKey,List.getElem?_range]
  · simp [hi,List.getElem?_range]; omega

theorem suffix_positions (text : Array (Fin σ)) (fallback : Fin σ) :
    (positions (prepareSuffixes text fallback).trie.tree).Perm (List.range (text.size+1)) := by
  have hh:=(Build.run_correct text fallback (suffixKeys text.size)).1.map Key.start
  rw [suffix_starts] at hh
  exact hh

theorem suffix_positions_nodup (text : Array (Fin σ)) (fallback : Fin σ) :
    (positions (prepareSuffixes text fallback).trie.tree).Nodup :=
  (suffix_positions text fallback).symm.nodup List.nodup_range

theorem compile_suffixes (text : Array (Fin σ)) (fallback : Fin σ) :
    ∃m,(compile (prepareSuffixes text fallback).trie.tree).1=some m ∧
      (MaskedEventBudget.leaves m).Perm (List.range (text.size+1)) ∧
      (MaskedEventBudget.leaves m).Nodup ∧ MaskedEventBudget.size m=text.size+1 ∧
      (compile (prepareSuffixes text fallback).trie.tree).2≤8*(text.size+1)+1 := by
  have hg:=(Build.run_correct text fallback (suffixKeys text.size)).2.1
  have hperm:=suffix_positions text fallback
  have hne : (prepareSuffixes text fallback).trie.tree.leaves≠[] := by
    intro h
    have hh:=hperm.length_eq
    simp only [positions,h,List.map_nil,List.length_nil,List.length_range] at hh
    omega
  obtain ⟨m,hm,hmem,hsize⟩:=compile_correct _ _ hg hne
  have hp : (MaskedEventBudget.leaves m).Perm (List.range (text.size+1)) := by rw [hmem]; exact hperm
  have hnodes:=(Build.run_correct text fallback (suffixKeys text.size)).2.2.1
  rw [suffixKeys_length] at hnodes
  change (prepareSuffixes text fallback).trie.tree.nodes≤2*(text.size+1) at hnodes
  have hw:=compile_work (prepareSuffixes text fallback).trie.tree
  have hsize' : MaskedEventBudget.size m=text.size+1 := by
    have hh:=(Build.run_correct text fallback (suffixKeys text.size)).1.length_eq
    rw [suffixKeys_length] at hh
    exact hsize.trans hh
  exact ⟨m,hm,hp,hp.symm.nodup List.nodup_range,hsize',by omega⟩

inductive Subtree : Tree n Nat→Tree n Nat→Prop
  | refl (t) : Subtree t t
  | left {u stem d l r} : Subtree u l→Subtree u (.node stem d l r)
  | right {u stem d l r} : Subtree u r→Subtree u (.node stem d l r)

theorem subtree_mem {u t : Tree n Nat} (h : Subtree u t) :
    ∀a,a∈u.leaves→a∈t.leaves := by
  induction h with
  | refl => exact fun _ h=>h
  | left _ ih => exact fun a ha=>List.mem_append_left _ (ih a ha)
  | right _ ih => exact fun a ha=>List.mem_append_right _ (ih a ha)

theorem subtree_positions {u t : Tree n Nat} (h : Subtree u t) :
    (positions u).Sublist (positions t) := by
  induction h with
  | refl => exact List.Sublist.refl _
  | @left stem d l r h ih =>
    exact ih.trans (by simp only [positions,Tree.leaves,List.map_append]; exact List.sublist_append_left _ _)
  | @right stem d l r h ih =>
    exact ih.trans (by simp only [positions,Tree.leaves,List.map_append]; exact List.sublist_append_right _ _)

theorem subtree_good (f : Nat→Fin σ) {u t : Tree n Nat} (h : Subtree u t)
    (hg : t.Good f) : u.Good f := by
  induction h with
  | refl => exact hg
  | left _ ih => exact ih hg.1
  | right _ ih => exact ih hg.2.1

/-- A distinct-position LCA is an actual split at the stated depth.
This fact does not mistake an equal-depth refinement for a full class. -/
theorem lca_split (t : Tree n Nat) (a b : Key n Nat) (H : Nat)
    (hlca : Tree.LCA t a b H) (hne : a.start≠b.start) :
    ∃stem l r,Subtree (.node stem H l r) t ∧
      ((a∈l.leaves ∧ b∈r.leaves) ∨ (a∈r.leaves ∧ b∈l.leaves)) := by
  induction hlca with
  | leaf a => exact False.elim (hne rfl)
  | @left stem d l r a b H h ih =>
    obtain ⟨s,x,y,hs,hh⟩:=ih hne
    exact ⟨s,x,y,.left hs,hh⟩
  | @right stem d l r a b H h ih =>
    obtain ⟨s,x,y,hs,hh⟩:=ih hne
    exact ⟨s,x,y,.right hs,hh⟩
  | @cross stem d l r a b ha hb => exact ⟨stem,l,r,.refl _,Or.inl ⟨ha,hb⟩⟩
  | @crossRev stem d l r a b ha hb => exact ⟨stem,l,r,.refl _,Or.inr ⟨ha,hb⟩⟩

end REWB.MaskedRunTrieBridge
