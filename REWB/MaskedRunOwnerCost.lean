import REWB.MaskedRunOwnerCoverage

/-! Actual suffix-trie owner execution budgets. The binary schedule is
constructed from the input trie; its small-to-large light volume is not
an externally supplied complexity certificate. -/
namespace REWB.MaskedRunOwnerCost
open REWB.BoundaryTrie REWB.MaskedRunDiscovery REWB.MaskedOrdered.Owner
open REWB.MaskedRunTrieBridge (compile)
variable {n σ : Nat}

theorem compile_measures (f : Nat→Fin σ) (t : Trie n Nat)
    (hg : t.Good f) (hn : t.leaves≠[]) (m : MaskedEventBudget.MergeTree)
    (hm : (compile t).1=some m) :
    slots t=t.nodes ∧ mass t=MaskedEventBudget.size m ∧
      light t=MaskedEventBudget.lightVolume m := by
  induction t generalizing m with
  | empty => exact False.elim (hn rfl)
  | leaf a =>
    have he : MaskedEventBudget.MergeTree.leaf a.start=m := Option.some.inj hm
    subst m
    exact ⟨rfl,rfl,rfl⟩
  | node stem d l r il ir =>
    obtain ⟨a,ha,_,_⟩:=MaskedRunTrieBridge.compile_correct f l hg.1 hg.2.2.1
    obtain ⟨b,hb,_,_⟩:=MaskedRunTrieBridge.compile_correct f r hg.2.1 hg.2.2.2.1
    have he : MaskedEventBudget.MergeTree.node a b=m := by
      simpa [compile,ha,hb] using hm
    subst m
    have hl:=il hg.1 hg.2.2.1 a ha
    have hr:=ir hg.2.1 hg.2.2.2.1 b hb
    refine ⟨?_,?_,?_⟩
    · simp only [slots,Tree.nodes,hl.1,hr.1]
    · simp only [mass,Tree.leaves,List.length_append,MaskedEventBudget.size]
      rw [←hl.2.1,←hr.2.1]
      rfl
    · simp only [light,hl.2.1,hr.2.1,hl.2.2,hr.2.2,MaskedEventBudget.lightVolume]

theorem suffix_shape (text : Array (Fin σ)) (fallback : Fin σ) :
    slots (prepareSuffixes text fallback).trie.tree≤2*(text.size+1) ∧
      mass (prepareSuffixes text fallback).trie.tree=text.size+1 ∧
      light (prepareSuffixes text fallback).trie.tree≤(text.size+1)*(text.size+1).log2 := by
  let t:=(prepareSuffixes text fallback).trie.tree
  have hg : t.Good (ArrayText.read text fallback) :=
    (Build.run_correct text fallback (suffixKeys text.size)).2.1
  have hlen : t.leaves.length=text.size+1 :=
    (Build.run_correct text fallback (suffixKeys text.size)).1.length_eq.trans (suffixKeys_length _)
  have hn : t.leaves≠[] := by intro he; rw [he,List.length_nil] at hlen; omega
  obtain ⟨m,hm,_,_,hsize,_⟩:=MaskedRunTrieBridge.compile_suffixes text fallback
  have hmeasure:=compile_measures _ t hg hn m hm
  have hnodes:=(Build.run_correct text fallback (suffixKeys text.size)).2.2.1
  rw [suffixKeys_length] at hnodes
  have hlight:=MaskedEventBudget.lightVolume_bound m
  rw [←hmeasure.2.2,hsize] at hlight
  refine ⟨?_,hlen,hlight⟩
  rw [hmeasure.1]
  exact hnodes

/-- Every node is materialized once; only light imports can emit
generations. The retained-heavy list is absent from this bound. -/
theorem suffix_execution (text : Array (Fin σ)) (fallback : Fin σ) (h : Nat)
    (hcap : text.size<2^h) :
    (run h (prepareSuffixes text fallback).trie.tree).2.nodes.size≤2*(text.size+1) ∧
      (run h (prepareSuffixes text fallback).trie.tree).2.events.size≤
        2*((text.size+1)*(text.size+1).log2) ∧
      (run h (prepareSuffixes text fallback).trie.tree).2.work≤
        h+1+2*(text.size+1)*(28*h+32)+((text.size+1)*(text.size+1).log2)*(35*h+46) := by
  let t:=(prepareSuffixes text fallback).trie.tree
  have hb:=MaskedRunOwnerCoverage.suffix_bounded text fallback h hcap
  have hn:=MaskedRunTrieBridge.suffix_positions_nodup text fallback
  have hs:=suffix_shape text fallback
  have hw:=visit_work (MaskedOrdered.capacity h).1 t none
    ({work:=(MaskedOrdered.capacity h).2} : Store h) (MaskedOrdered.capacity_value h) hb hn
  have he:=visit_events_bound (MaskedOrdered.capacity h).1 t none
    ({work:=(MaskedOrdered.capacity h).2} : Store h) (MaskedOrdered.capacity_value h) hb hn
  have hsize:=visit_size (MaskedOrdered.capacity h).1 t none
    ({work:=(MaskedOrdered.capacity h).2} : Store h)
  change (run h t).2.nodes.size=0+slots t at hsize
  change (run h t).2.events.size≤0+2*light t at he
  change (run h t).2.work≤(MaskedOrdered.capacity h).2+slots t*nodeBudget h+
    light t*(MaskedOrdered.importBudget h+6) at hw
  rw [MaskedOrdered.capacity_work] at hw
  have hnwork:=Nat.mul_le_mul_right (nodeBudget h) hs.1
  have hlwork:=Nat.mul_le_mul_right (MaskedOrdered.importBudget h+6) hs.2.2
  have hlevents:=Nat.mul_le_mul_left 2 hs.2.2
  dsimp only [t] at *
  refine ⟨by omega,by omega,?_⟩
  simp only [nodeBudget,MaskedOrdered.importBudget,show 35*h+40+6=35*h+46 by omega] at hw hnwork hlwork
  omega

end REWB.MaskedRunOwnerCost
