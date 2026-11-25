import REWB.MaskedSuffixClassIndex
import REWB.MaskedRunEnumerationCost

/-! Total counters for the concrete suffix class preparation, including
the existing owner event ledger, annotation, parent rows and direct
terminal array. Logarithms and capacity construction are charged once. -/
namespace REWB.MaskedSuffixClass
open REWB.BoundaryTrie REWB.BoundaryApplication REWB.MaskedRunDiscovery
variable {σ : Nat}

def ownerBudget (h n : Nat) : Nat :=
  h+1+2*(n+1)*(28*h+32)+((n+1)*(n+1).log2)*(35*h+46)

def extraBudget (n : Nat) : Nat :=
  10*(n+1)+(n+2)+2*(n+1)*(6*levels n+8)+levels n+8+height n+2

def budget (σ n : Nat) : Nat :=
  MaskedOrdered.Owner.preparationBudget σ n+ownerBudget (height n) n+extraBudget n

theorem prepare_work (text : Array (Fin σ)) (fallback : Fin σ) :
    (prepare text fallback).work≤budget σ text.size := by
  let t:=(prepareSuffixes text fallback).trie.tree
  have hp:=prepareSuffixes_work text fallback
  have hx:=(MaskedRunOwnerCost.suffix_execution text fallback (height text.size)
    (height_capacity text.size)).2.2
  have ha:=annotate_work t 0
  have hn:=(MaskedRunOwnerCost.suffix_shape text fallback).1
  have hl:=StartLocate.build_work (levels text.size) (annotate t 0).tree
  rw [annotate_nodes] at hl
  have hm:=Nat.mul_le_mul_right (6*levels text.size+8) hn
  change (prepareSuffixes text fallback).work≤MaskedOrdered.Owner.preparationBudget σ text.size at hp
  change (MaskedOrdered.Owner.run (height text.size) t).2.work≤ownerBudget (height text.size) text.size at hx
  change MaskedOrdered.Owner.slots t≤2*(text.size+1) at hn
  change MaskedOrdered.Owner.slots t*(6*levels text.size+8)≤_ at hm
  change (prepareSuffixes text fallback).work+
    (MaskedOrdered.Owner.run (height text.size) t).2.work+(annotate t 0).work+
    (StartLocate.build (levels text.size) (annotate t 0).tree).work+
    levels text.size+8+height text.size+2≤_
  unfold budget extraBudget
  omega

theorem prepare_addresses (text : Array (Fin σ)) (fallback : Fin σ) :
    (prepare text fallback).addresses.cells.size=(prepare text fallback).owner.nodes.size ∧
      (prepare text fallback).addresses.cells.size≤2*(text.size+1) := by
  have ha:=StartLocate.build_size (levels text.size)
    (annotate (prepareSuffixes text fallback).trie.tree 0).tree
  rw [annotate_nodes] at ha
  have ho:=MaskedOrdered.Owner.visit_size (MaskedOrdered.capacity (height text.size)).1
    (prepareSuffixes text fallback).trie.tree none
    ({work:=(MaskedOrdered.capacity (height text.size)).2} : MaskedOrdered.Owner.Store (height text.size))
  change (MaskedOrdered.Owner.run (height text.size) (prepareSuffixes text fallback).trie.tree).2.nodes.size=
    0+MaskedOrdered.Owner.slots (prepareSuffixes text fallback).trie.tree at ho
  change (prepare text fallback).addresses.cells.size=MaskedOrdered.Owner.slots
    (prepareSuffixes text fallback).trie.tree at ha
  change (prepare text fallback).owner.nodes.size=_ at ho
  have hn:=(MaskedRunOwnerCost.suffix_shape text fallback).1
  exact ⟨by omega,by omega⟩

theorem prepare_addresses_exact (text : Array (Fin σ)) (fallback : Fin σ) :
    (prepare text fallback).addresses.cells.size+1=2*(text.size+1) := by
  let t:=(prepareSuffixes text fallback).trie.tree
  have hg : t.Good (ArrayText.read text fallback) :=
    (BoundaryTrie.Build.run_correct text fallback (suffixKeys text.size)).2.1
  have hlen : t.leaves.length=text.size+1 :=
    (BoundaryTrie.Build.run_correct text fallback (suffixKeys text.size)).1.length_eq.trans
      (suffixKeys_length text.size)
  have hn : t.leaves≠[] := by intro he; rw [he,List.length_nil] at hlen; omega
  obtain ⟨m,hm,_,_⟩:=MaskedRunTrieBridge.compile_correct _ t hg hn
  have hs:=(MaskedRunOwnerCost.compile_measures _ t hg hn m hm).1
  have ha:=StartLocate.build_size (levels text.size) (annotate t 0).tree
  rw [annotate_nodes,hs] at ha
  have hd : suffixKeys text.size≠[] := by
    intro he
    have hh:=suffixKeys_length text.size
    rw [he,List.length_nil] at hh
    omega
  have he:=BoundaryTrie.Build.run_nodes text fallback (suffixKeys text.size) hd
  rw [suffixKeys_length] at he
  change t.nodes+1=2*(text.size+1) at he
  change (prepare text fallback).addresses.cells.size=t.nodes at ha
  omega

theorem levels_height (n : Nat) : levels n=height n+1 := by
  unfold levels StartLocate.levelsFor height
  rw [Nat.log2,if_pos (by omega : 2≤2*(n+1))]
  have he : 2*(n+1)/2=n+1 := by omega
  rw [he]

theorem extra_bound (n : Nat) : extraBudget n≤80*MaskedRunEnumerationCost.volume n := by
  have hv:=MaskedRunEnumerationCost.square_bounds n
  have hh:=MaskedRunEnumerationCost.height_pos n
  change 1≤height n at hh
  change 1≤MaskedRunEnumerationCost.volume n ∧ n+1≤MaskedRunEnumerationCost.volume n ∧
    height n≤MaskedRunEnumerationCost.volume n ∧ (n+1)*height n≤MaskedRunEnumerationCost.volume n at hv
  have hc : 6*levels n+8≤26*height n := by rw [levels_height]; omega
  have hm:=Nat.mul_le_mul_left (2*(n+1)) hc
  have he : 2*(n+1)*(26*height n)=52*((n+1)*height n) := by
    calc
      _ = (2*26)*((n+1)*height n) := by ac_rfl
      _ = _ := rfl
  rw [he] at hm
  have hb:=Nat.mul_le_mul_left 52 hv.2.2.2
  have hl:=levels_height n
  unfold extraBudget
  omega

theorem budget_closed (σ n : Nat) :
    budget σ n≤(32*(σ+2)+830)*(n+1)*((n+1).log2+1)^2 := by
  have hp:=MaskedRunEnumerationCost.preparation_bound σ n
  have hx:=MaskedRunEnumerationCost.execution_bound n
  have he:=extra_bound n
  have ho : ownerBudget (height n) n≤MaskedOrdered.Owner.executionBudget (height n) n := by
    unfold ownerBudget MaskedOrdered.Owner.executionBudget
    omega
  change MaskedOrdered.Owner.executionBudget (height n) n≤416*MaskedRunEnumerationCost.volume n at hx
  have hc : 32*(σ+2)+830=(2*(16*(σ+2)+5)+324)+416+80 := by omega
  rw [Nat.mul_assoc]
  change budget σ n≤(32*(σ+2)+830)*MaskedRunEnumerationCost.volume n
  rw [hc,Nat.add_mul,Nat.add_mul]
  unfold budget
  omega

/-- The complete actual preparation is near-linear for each fixed
alphabet in the declared natural-number/array-slot operation model. -/
theorem prepare_work_closed (text : Array (Fin σ)) (fallback : Fin σ) :
    (prepare text fallback).work≤
      (32*(σ+2)+830)*(text.size+1)*((text.size+1).log2+1)^2 :=
  Nat.le_trans (prepare_work text fallback) (budget_closed σ text.size)

theorem query_work_height (text : Array (Fin σ)) (fallback : Fin σ)
    (p : Fin (text.size+1)) (H : Nat) :
    (query (prepare text fallback) p H).work≤6*((text.size+1).log2+1)+15 := by
  have hh:=query_work (prepare text fallback) p H
  change (query (prepare text fallback) p H).work≤6*levels text.size+9 at hh
  rw [levels_height] at hh
  exact hh

end REWB.MaskedSuffixClass
