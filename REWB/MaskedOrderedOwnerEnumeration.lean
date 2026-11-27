import REWB.MaskedOrderedOwnerBatch
import REWB.MaskedOrderedOwnerOrigin
import REWB.MaskedRunOwnerCost

/-! A concrete cubic-run enumerator from a materialized text. It builds
exact forward/reverse indexes and the suffix descriptor trie once,
generates fresh pairs by persistent light merges, checks them against
completed owner snapshots, extends surviving dense pairs, and removes
duplicates with the existing exact binary-key registry. -/
namespace REWB.MaskedOrdered.Owner
open REWB.RunGeometry (Bounds)
open REWB.MaskedRunDiscovery (prepareSuffixes)
variable {σ : Nat}

structure Enumeration where
  runs : List Bounds
  work : Nat
  nodeCount : Nat
  eventCount : Nat
  deriving Repr

def enumerate (h : Nat) (text : Array (Fin σ)) (fallback : Fin σ) : Enumeration :=
  let prepared:=prepareSuffixes text fallback
  let c:=capacity h
  let built:=visit c.1 prepared.trie.tree none ({work:=c.2} : Store h)
  let found:=batch prepared.trie.prepared.ranks prepared.backward text.size c.1
    built.2.nodes built.2.events
  ⟨found.runs,prepared.work+built.2.work+found.work+8,built.2.nodes.size,built.2.events.size⟩

theorem suffix_probe_sound (text : Array (Fin σ)) (fallback : Fin σ) (h : Nat)
    (hcap : text.size<2^h) (e : Event)
    (he : e∈(run h (prepareSuffixes text fallback).trie.tree).2.events.toList) (R : Bounds)
    (hr : (probe (prepareSuffixes text fallback).trie.prepared.ranks
      (prepareSuffixes text fallback).backward text.size (capacity h).1
      (run h (prepareSuffixes text fallback).trie.tree).2.nodes e).1=some R) :
    R.Valid (ArrayText.read text fallback) text.size ∧ R.period=e.edge.2-e.edge.1 ∧
      3*R.period≤R.hi-R.lo := by
  apply probe_sound (ArrayText.read text fallback) text.size (capacity h).1
    (run h (prepareSuffixes text fallback).trie.tree).2.nodes e R (capacity_value h)
  · exact suffix_event_certified text fallback h (capacity h).1 (capacity h).2
      (capacity_value h) (MaskedRunOwnerCoverage.suffix_bounded text fallback h hcap) e he
  · simpa only [MaskedRunDiscovery.prepareSuffixes_forward,
      MaskedRunDiscovery.prepareSuffixes_backward] using hr

theorem enumerate_mem (h : Nat) (text : Array (Fin σ)) (fallback : Fin σ)
    (hcap : text.size<2^h) (R : Bounds) :
    R∈(enumerate h text fallback).runs ↔
      R.Valid (ArrayText.read text fallback) text.size ∧ 3*R.period≤R.hi-R.lo := by
  change R∈(batch (prepareSuffixes text fallback).trie.prepared.ranks
    (prepareSuffixes text fallback).backward text.size (capacity h).1
    (run h (prepareSuffixes text fallback).trie.tree).2.nodes
    (run h (prepareSuffixes text fallback).trie.tree).2.events).runs ↔ _
  rw [batch_mem _ _ _ _ _ _ (fun e he R hr=>RunDedup.valid_bounded _ _ _
    (suffix_probe_sound text fallback h hcap e he R hr).1)]
  constructor
  · rintro ⟨e,he,hr⟩
    have hh:=suffix_probe_sound text fallback h hcap e he R hr
    exact ⟨hh.1,hh.2.2⟩
  · rintro ⟨hv,hc⟩
    exact MaskedRunOwnerCoverage.cubic_probe text fallback R hv hc h hcap

theorem enumerate_nodup (h : Nat) (text : Array (Fin σ)) (fallback : Fin σ) :
    (enumerate h text fallback).runs.Nodup := batch_nodup _ _ _ _ _ _

def executionBudget (h n : Nat) : Nat :=
  h+1+2*(n+1)*(28*h+32)+((n+1)*(n+1).log2)*(35*h+46)+
    (2*((n+1)*(n+1).log2))*(probeBudget h n+26*((n+1).log2+1)+10)+13

theorem enumerate_work (h : Nat) (text : Array (Fin σ)) (fallback : Fin σ)
    (hcap : text.size<2^h) :
    (enumerate h text fallback).work≤(prepareSuffixes text fallback).work+executionBudget h text.size := by
  have hx:=MaskedRunOwnerCost.suffix_execution text fallback h hcap
  have hb:=batch_work (ArrayText.read text fallback) text.size (capacity h).1
    (run h (prepareSuffixes text fallback).trie.tree).2.nodes
    (run h (prepareSuffixes text fallback).trie.tree).2.events
  rw [←MaskedRunDiscovery.prepareSuffixes_forward text fallback,
    ←MaskedRunDiscovery.prepareSuffixes_backward text fallback] at hb
  have hm:=Nat.mul_le_mul_right (probeBudget h text.size+26*((text.size+1).log2+1)+10) hx.2.1
  change (prepareSuffixes text fallback).work+
    (run h (prepareSuffixes text fallback).trie.tree).2.work+
    (batch (prepareSuffixes text fallback).trie.prepared.ranks (prepareSuffixes text fallback).backward
      text.size (capacity h).1 (run h (prepareSuffixes text fallback).trie.tree).2.nodes
      (run h (prepareSuffixes text fallback).trie.tree).2.events).work+8≤_
  have hw:=hx.2.2
  simp only [executionBudget]
  omega

def preparationBudget (σ n : Nat) : Nat :=
  2*((n+1)*((n.log2+1)*(16*RankIndex.width σ n+4)+1))+
    (13*(n.log2+1)+12)*(8*(n+1)*((n+1).log2+1))+
    5*(n+1)+3+2*(n+1)*BoundaryTrie.Build.budget n (n+1)

theorem enumerate_full_work (h : Nat) (text : Array (Fin σ)) (fallback : Fin σ)
    (hcap : text.size<2^h) :
    (enumerate h text fallback).work≤preparationBudget σ text.size+executionBudget h text.size := by
  have hp:=MaskedRunDiscovery.prepareSuffixes_work text fallback
  have he:=enumerate_work h text fallback hcap
  change (prepareSuffixes text fallback).work≤preparationBudget σ text.size at hp
  omega

theorem enumerate_dimensions (h : Nat) (text : Array (Fin σ)) (fallback : Fin σ)
    (hcap : text.size<2^h) :
    (enumerate h text fallback).nodeCount≤2*(text.size+1) ∧
      (enumerate h text fallback).eventCount≤2*((text.size+1)*(text.size+1).log2) := by
  have hh:=MaskedRunOwnerCost.suffix_execution text fallback h hcap
  exact ⟨hh.1,hh.2.1⟩

/-- The automatic universe choice contains every suffix start, including
the empty suffix at the text's right endpoint. Its logarithm is charged
once by a height-sized scalar allowance. -/
def enumerateAuto (text : Array (Fin σ)) (fallback : Fin σ) : Enumeration :=
  let h:=(text.size+1).log2+1
  let r:=enumerate h text fallback
  {r with work:=r.work+h+2}

theorem auto_capacity (n : Nat) : n<2^((n+1).log2+1) := by
  have hh:=Nat.lt_log2_self (n:=n+1)
  omega

theorem enumerateAuto_mem (text : Array (Fin σ)) (fallback : Fin σ) (R : Bounds) :
    R∈(enumerateAuto text fallback).runs ↔
      R.Valid (ArrayText.read text fallback) text.size ∧ 3*R.period≤R.hi-R.lo :=
  enumerate_mem _ _ _ (auto_capacity text.size) R

theorem enumerateAuto_nodup (text : Array (Fin σ)) (fallback : Fin σ) :
    (enumerateAuto text fallback).runs.Nodup := enumerate_nodup _ _ _

theorem enumerateAuto_work (text : Array (Fin σ)) (fallback : Fin σ) :
    (enumerateAuto text fallback).work≤preparationBudget σ text.size+
      executionBudget ((text.size+1).log2+1) text.size+((text.size+1).log2+1)+2 := by
  have hh:=enumerate_full_work ((text.size+1).log2+1) text fallback (auto_capacity text.size)
  exact Nat.add_le_add_right (Nat.add_le_add_right hh _) _

end REWB.MaskedOrdered.Owner
