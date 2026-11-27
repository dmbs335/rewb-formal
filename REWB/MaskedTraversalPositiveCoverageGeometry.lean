import REWB.MaskedTraversalBandUnique
import REWB.MaskedTraversalPeriodicCoverage

/-! The representative for an emitted band is the actual cached first
occurrence. Complete class and leader geometry follow from the built
suffix trie and the real driver's band snapshots, including every length
inside a compressed edge. Equal-depth refinements emit no such band. -/
namespace REWB.MaskedTraversalPositiveCoverage
open REWB.MaskedTraversalDriver REWB.MaskedTraversalEdge REWB.BoundaryTrie REWB.MaskedRunDiscovery
variable {σ h : Nat}

def representative (b : Band h) : Nat := b.snapshot.occurrences.first.getD 0

theorem suffix_band_valid (text : Array (Fin σ)) (fallback : Fin σ) (h : Nat)
    (capacity : Nat) (hcap : capacity=2^h) (hn : text.size<2^h) (b : Band h)
    (hb : (MaskedTraversalDriver.run h (prepareSuffixes text fallback).trie.tree).plan.HasBand b) :
    0<b.lo ∧ b.Valid capacity b.snapshot.occurrences := by
  have hg : (prepareSuffixes text fallback).trie.tree.Good (ArrayText.read text fallback) :=
    (Build.run_correct text fallback (suffixKeys text.size)).2.1
  have hh:=build_band_locus (MaskedOrdered.capacity h).1 0 (ArrayText.read text fallback)
    (prepareSuffixes text fallback).trie.tree hg (MaskedOrdered.capacity_value h) hn (Nat.zero_le _) b hb
  have he : (MaskedOrdered.capacity h).1=capacity := (MaskedOrdered.capacity_value h).trans hcap.symm
  rw [he] at hh
  exact ⟨hh.1,hh.2.1⟩

theorem representative_mem (text : Array (Fin σ)) (fallback : Fin σ) (h : Nat)
    (hn : text.size<2^h) (b : Band h)
    (hb : (MaskedTraversalDriver.run h (prepareSuffixes text fallback).trie.tree).plan.HasBand b)
    (p : Nat) (hp : p∈b.snapshot.occurrences.entries) : representative b∈b.snapshot.occurrences.entries := by
  have valid:=(suffix_band_valid text fallback h (2^h) rfl hn b hb).2
  have first:=MaskedOrdered.Tree.first_spec b.snapshot.occurrences 0 valid.invariant.occGood valid.invariant.occFits
  cases hf : b.snapshot.occurrences.first with
  | none=>
    rw [hf] at first
    change b.snapshot.occurrences.entries=[] at first
    rw [first] at hp
    cases hp
  | some firstAt=>
    rw [hf] at first
    simpa only [representative,hf,Option.getD_some] using first.1

structure Metadata (text : Array (Fin σ)) (fallback : Fin σ) (capacity : Nat) (b : Band h) : Prop where
  positive : 0<b.lo
  valid : b.Valid capacity b.snapshot.occurrences
  representative_mem : representative b∈b.snapshot.occurrences.entries
  complete : ∀L,b.lo≤L→L≤b.hi→Complete (ArrayText.read text fallback) text.size (representative b) L b.snapshot.occurrences.entries
  bounded : representative b+b.hi≤text.size

theorem band_metadata (text : Array (Fin σ)) (fallback : Fin σ) (h : Nat)
    (capacity : Nat) (hcap : capacity=2^h) (hn : text.size<2^h) (b : Band h)
    (hb : (MaskedTraversalDriver.run h (prepareSuffixes text fallback).trie.tree).plan.HasBand b)
    (p : Nat) (hp : p∈b.snapshot.occurrences.entries) : Metadata text fallback capacity b := by
  have hv:=suffix_band_valid text fallback h capacity hcap hn b hb
  have hm:=representative_mem text fallback h hn b hb p hp
  have full:=fun L hL hH=>suffix_band_complete text fallback h hn b hb L (representative b) hL hH hm
  exact ⟨hv.1,hv.2,hm,full,((full b.hi hv.2.bounds (Nat.le_refl _) (representative b)).mp hm).1⟩

theorem Metadata.invariant {text : Array (Fin σ)} {fallback : Fin σ} {capacity : Nat} {b : Band h}
    (metadata : Metadata text fallback capacity b) (hcap : capacity=2^h) (L : Nat) (hl : b.lo≤L) (hh : L≤b.hi) :
    MaskedClusterLeaders.Invariant L b.snapshot := (metadata.valid.at hcap hl hh).1

end REWB.MaskedTraversalPositiveCoverage
