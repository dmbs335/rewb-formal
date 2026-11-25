import REWB.MaskedTraversalPositiveCoverageGeometry

/-! Every band in the actual suffix traversal has an occurrence.  Its
positive lower length reaches a genuine, nonempty locus of the constructed
suffix trie.  The representative and complete-class metadata therefore
need no externally supplied witness. -/
namespace REWB.MaskedTraversalDriver
open REWB.BoundaryTrie REWB.MaskedRunDiscovery
variable {h n σ : Nat}

theorem positive_depth_nonempty (f : Nat→Fin σ) (t : Tree n Nat)
    (hg : t.Good f) (hd : 0<t.depth) : ∃a,a∈t.leaves := by
  cases t with
  | empty => simp only [Tree.depth] at hd; omega
  | leaf a => exact ⟨a,by simp only [Tree.leaves,List.mem_singleton]⟩
  | node stem depth left right =>
    exact ⟨stem,List.mem_append_left _ hg.2.2.2.2.1⟩

theorem build_band_nonempty (capacity floor : Nat) (f : Nat→Fin σ) (t : Tree n Nat)
    (hg : t.Good f) (hc : capacity=2^h) (hn : n<2^h) (hf : floor≤t.depth)
    (b : MaskedTraversalEdge.Band h) (hb : (build capacity floor t).plan.HasBand b) :
    ∃p,p∈b.snapshot.occurrences.entries := by
  have hs:=build_band_locus capacity floor f t hg hc hn hf b hb
  obtain ⟨u,hu,hm⟩:=hs.2.2 b.lo (Nat.le_refl _) hs.2.1.bounds
  have hd:=Tree.locus_depth hu
  obtain ⟨a,ha⟩:=positive_depth_nonempty f u (Tree.locus_good f hg hu)
    (by have hl:=hs.1; omega)
  exact ⟨a.start,(hm a.start).mpr (List.mem_map.mpr ⟨a,ha,rfl⟩)⟩

theorem suffix_band_nonempty (text : Array (Fin σ)) (fallback : Fin σ) (h : Nat)
    (hn : text.size<2^h) (b : MaskedTraversalEdge.Band h)
    (hb : (run h (prepareSuffixes text fallback).trie.tree).plan.HasBand b) :
    ∃p,p∈b.snapshot.occurrences.entries :=
  build_band_nonempty (MaskedOrdered.capacity h).1 0 _ _
    (Build.run_correct text fallback (suffixKeys text.size)).2.1
    (MaskedOrdered.capacity_value h) hn (Nat.zero_le _) b hb

end REWB.MaskedTraversalDriver

namespace REWB.MaskedTraversalPositiveCoverage
open REWB.MaskedTraversalDriver REWB.MaskedRunDiscovery
variable {σ : Nat}

theorem actual_band_metadata (text : Array (Fin σ)) (fallback : Fin σ) (h : Nat)
    (capacity : Nat) (hcap : capacity=2^h) (hn : text.size<2^h)
    (b : MaskedTraversalEdge.Band h)
    (hb : (MaskedTraversalDriver.run h (prepareSuffixes text fallback).trie.tree).plan.HasBand b) :
    Metadata text fallback capacity b := by
  obtain ⟨p,hp⟩:=suffix_band_nonempty text fallback h hn b hb
  exact band_metadata text fallback h capacity hcap hn b hb p hp

end REWB.MaskedTraversalPositiveCoverage
