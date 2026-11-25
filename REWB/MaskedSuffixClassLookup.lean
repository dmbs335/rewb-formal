import REWB.MaskedSuffixClass
import REWB.MaskedRunOwnerCost

/-! The parent-jump cutoff selects a real saved owner-array address at
the first depth threshold. This is a complete prefix class even when
the requested length lies strictly inside a compressed edge. -/
namespace REWB.MaskedSuffixClass
open REWB.BoundaryTrie REWB.BoundaryApplication
open REWB.MaskedRunDiscovery
variable {n σ : Nat}

theorem cut_locus (t : Tree n Nat) (base : Nat) (parent : Option MaskedOrdered.Owner.Parent)
    (p : Fin (n+1)) (H : Nat) (v : Locator (n+1))
    (hc : StartLocate.CutPath p H (annotate t base).tree v) :
    ∃u pu,Tree.Locus t H u ∧ MaskedOrdered.Owner.Location t parent base u pu v.payload ∧
      v.depth=u.depth ∧ ∃a,a∈u.leaves ∧ a.start=p.val := by
  induction t generalizing base parent v with
  | empty =>
    cases hc with
    | here _ ht _ => cases ht
  | leaf a =>
    cases hc with
    | here _ ht hd =>
      exact ⟨.leaf a,parent,.here _ hd,.here _ _ _,rfl,
        (annotate_target (.leaf a) base p).mp ht⟩
  | node stem d l r il ir =>
    cases hc with
    | here _ ht hd =>
      exact ⟨.node stem d l r,parent,.here _ hd,.here _ _ _,rfl,
        (annotate_target (.node stem d l r) base p).mp ht⟩
    | left hd hc =>
      obtain ⟨u,pu,hl,hid,hdepth,ha⟩:=il (base+1)
        (some ⟨d,MaskedOrdered.Owner.select parent d base⟩) v hc
      exact ⟨u,pu,.left hd hl,.left hid,hdepth,ha⟩
    | right hd hc =>
      obtain ⟨u,pu,hl,hid,hdepth,ha⟩:=ir (annotate l (base+1)).next
        (some ⟨d,MaskedOrdered.Owner.select parent d base⟩) v hc
      rw [annotate_next] at hid
      exact ⟨u,pu,.right hd hl,.right hid,hdepth,ha⟩

theorem terminal_path (t : Tree n Nat) (base : Nat) (p : Fin (n+1))
    (xs : Array (StartLocate.Cell Nat)) (par : Option Nat) (i : Nat)
    (hp : StartLocate.Path xs p par (annotate t base).tree i) :
    ∃a c,a∈t.leaves ∧ a.start=p.val ∧ xs[i]?=some c ∧ c.depth=a.length := by
  induction t generalizing base par with
  | empty =>
    cases hp with
    | leaf _ _ _ _ ht => cases ht
  | leaf a =>
    cases hp with
    | leaf hc hd _ _ ht =>
      exact ⟨a,_,by simp [Tree.leaves],congrArg Fin.val (Option.some.inj ht),hc,hd⟩
  | node _ _ l r il ir =>
    cases hp with
    | left _ _ _ _ hpath =>
      obtain ⟨a,c,ha,hstart,hc,hd⟩:=il _ _ hpath
      exact ⟨a,c,List.mem_append_left _ ha,hstart,hc,hd⟩
    | right _ _ _ _ hpath =>
      obtain ⟨a,c,ha,hstart,hc,hd⟩:=ir _ _ hpath
      exact ⟨a,c,List.mem_append_right _ ha,hstart,hc,hd⟩

theorem suffix_length (text : Array (Fin σ)) (fallback : Fin σ)
    (a : Key text.size Nat) (ha : a∈(prepareSuffixes text fallback).trie.tree.leaves) :
    a.length=text.size-a.start := by
  have hm:=(BoundaryTrie.Build.run_correct text fallback (suffixKeys text.size)).1.mem_iff.mp ha
  obtain ⟨q,hq⟩:=List.mem_ofFn.mp hm
  have he : suffixKey text.size q=a := hq
  rw [←he]
  rfl

theorem suffix_target (text : Array (Fin σ)) (fallback : Fin σ)
    (p : Fin (text.size+1)) :
    StartLocate.HasTarget p (annotate (prepareSuffixes text fallback).trie.tree 0).tree := by
  apply (annotate_target _ 0 p).mpr
  refine ⟨suffixKey text.size p,?_,rfl⟩
  exact (BoundaryTrie.Build.run_correct text fallback (suffixKeys text.size)).1.mem_iff.mpr
    (suffixKey_mem text.size p)

theorem suffix_targetDepth (text : Array (Fin σ)) (fallback : Fin σ)
    (p : Fin (text.size+1)) (H : Nat) (hH : H≤text.size-p.val) :
    StartLocate.TargetDepth p H (annotate (prepareSuffixes text fallback).trie.tree 0).tree := by
  apply annotate_targetDepth
  intro a ha hap
  rw [suffix_length text fallback a ha,hap]
  exact hH

theorem suffix_cut_invalid (text : Array (Fin σ)) (fallback : Fin σ)
    (rowWidth : Nat) (p : Fin (text.size+1)) (H : Nat) (hH : text.size-p.val<H) :
    (StartLocate.query rowWidth
      (StartLocate.build rowWidth (annotate (prepareSuffixes text fallback).trie.tree 0).tree) p H).value=none := by
  obtain ⟨i,hslot,hpath⟩:=StartLocate.build_path rowWidth
    (annotate (prepareSuffixes text fallback).trie.tree 0).tree p (suffix_target text fallback p)
  obtain ⟨a,c,ha,hstart,hc,hd⟩:=terminal_path _ 0 p _ none i hpath
  have hn : ¬H≤c.depth := by
    rw [hd,suffix_length text fallback a ha,hstart]
    omega
  simp only [StartLocate.query,hslot,hc,if_neg hn]

theorem retained_at (text : Array (Fin σ)) (fallback : Fin σ) (h : Nat)
    (hcap : text.size<2^h) (u : Tree text.size Nat) (pu : Option MaskedOrdered.Owner.Parent) (id : Nat)
    (hl : MaskedOrdered.Owner.Location (prepareSuffixes text fallback).trie.tree none 0 u pu id) :
    ∃r,(MaskedOrdered.Owner.run h (prepareSuffixes text fallback).trie.tree).2.nodes[id]?=some r ∧
      MaskedOrdered.Owner.Snapshot u pu id r := by
  exact MaskedOrdered.Owner.visit_at (MaskedOrdered.capacity h).1 _ none
    ({work:=(MaskedOrdered.capacity h).2} : MaskedOrdered.Owner.Store h)
    (MaskedOrdered.capacity_value h)
    (MaskedRunOwnerCoverage.suffix_bounded text fallback h hcap) u pu id hl

theorem snapshot_complete (text : Array (Fin σ)) (fallback : Fin σ)
    (u : Tree text.size Nat) (pu : Option MaskedOrdered.Owner.Parent) (id h H : Nat)
    (p : Fin (text.size+1)) (r : MaskedOrdered.Owner.Record h)
    (hl : Tree.Locus (prepareSuffixes text fallback).trie.tree H u)
    (hs : MaskedOrdered.Owner.Snapshot u pu id r) (ha : ∃a,a∈u.leaves ∧ a.start=p.val) :
    r.state.Valid ∧ Complete (ArrayText.read text fallback) text.size p.val H r.state.tree.entries := by
  obtain ⟨a,ha,hap⟩:=ha
  have hf:=prepareSuffixes_complete text fallback u H a hl ha
  refine ⟨hs.2.2.2.1,?_⟩
  intro k
  rw [hs.2.2.2.2 k]
  simpa only [hap] using hf k

end REWB.MaskedSuffixClass
