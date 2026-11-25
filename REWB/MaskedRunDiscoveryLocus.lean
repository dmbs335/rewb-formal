import REWB.MaskedRunDiscoveryCoverage
import REWB.BoundaryTrieLocus

/-! Full occurrence classes from an actual constructed descriptor trie.
All n+1 suffixes, including the empty suffix, are represented by constant
size descriptors. The first-threshold locus theorem excludes incomplete
equal-depth binary refinements. Its leaf positions are exactly all text
occurrences of the requested prefix. -/
namespace REWB.MaskedRunDiscovery
open REWB.Periodic REWB.RunGeometry REWB.LCEIndex
open REWB.BoundaryTrie
variable {σ n : Nat}

def suffixKey (n : Nat) (i : Fin (n+1)) : Key n Nat :=
  ⟨i.val,n-i.val,by have hh:=i.isLt; omega,i.val⟩

def suffixKeys (n : Nat) : List (Key n Nat) := List.ofFn (suffixKey n)

theorem suffixKeys_length (n : Nat) : (suffixKeys n).length=n+1 := by
  simp only [suffixKeys,List.length_ofFn]

theorem suffixKey_mem (n : Nat) (i : Fin (n+1)) : suffixKey n i∈suffixKeys n :=
  List.mem_ofFn.mpr ⟨i,rfl⟩

def positions (t : Tree n Nat) : List Nat := t.leaves.map Key.start

/-- Exact completeness, derived from the real suffix descriptors and
the qualified locus, rather than supplied as a tree-node invariant. -/
theorem suffix_locus_complete (f : Nat→Fin σ) (t u : Tree n Nat) (d : Nat)
    (a : Key n Nat) (hg : t.Good f) (hp : t.leaves.Perm (suffixKeys n))
    (hl : Tree.Locus t d u) (ha : a∈u.leaves) :
    Complete f n a.start d (positions u) := by
  have haroot:=Tree.locus_mem hl a ha
  have haa:=(Tree.locus_complete f hg hl a a ha haroot).mpr ha
  intro k
  constructor
  · intro hk
    obtain ⟨b,hb,he⟩:=List.mem_map.mp hk
    have hroot:=Tree.locus_mem hl b hb
    have hc:=(Tree.locus_complete f hg hl a b ha hroot).mpr hb
    have hbound:=b.bounded
    have hlen:=hc.2.1
    refine ⟨by omega,?_⟩
    simpa only [he] using hc.2.2.symm
  · intro hk
    let i : Fin (n+1):=⟨k,by have hh:=hk.1; omega⟩
    let b:=suffixKey n i
    have hbroot : b∈t.leaves := hp.mem_iff.mpr (suffixKey_mem n i)
    have hc : Key.Common f a b d := by
      refine ⟨haa.1,?_,?_⟩
      · change d≤n-k
        have hh:=hk.1
        omega
      · exact hk.2.symm
    have hbu:=(Tree.locus_complete f hg hl a b ha hbroot).mp hc
    exact List.mem_map.mpr ⟨b,hbu,rfl⟩

structure SuffixIndex (n : Nat) where
  trie : BoundaryTrie.Build.Index n Nat
  backward : RankIndex.Index
  work : Nat
  deriving Repr

/-- Forward ranks are retained by the trie preparation; reverse ranks
are built once here. Four scalar slots per suffix descriptor charge its
three stored values and the list cell. -/
def prepareSuffixes (text : Array (Fin σ)) (fallback : Fin σ) : SuffixIndex text.size :=
  let descriptors:=suffixKeys text.size
  let trie:=BoundaryTrie.Build.run text fallback descriptors
  let backward:=prepareReverse (ArrayText.read text fallback) text.size
  ⟨trie,backward,trie.work+backward.countedWork+4*(text.size+1)+1⟩

theorem prepareSuffixes_forward (text : Array (Fin σ)) (fallback : Fin σ) :
    (prepareSuffixes text fallback).trie.prepared.ranks=
      LCEIndex.prepare (ArrayText.read text fallback) text.size := by
  change (BoundaryTrie.Build.run text fallback (suffixKeys text.size)).prepared.ranks=_
  rw [BoundaryTrie.Build.run_prepared,BoundaryTrie.prepare_ranks]

theorem prepareSuffixes_backward (text : Array (Fin σ)) (fallback : Fin σ) :
    (prepareSuffixes text fallback).backward=
      prepareReverse (ArrayText.read text fallback) text.size := rfl

theorem prepareSuffixes_complete (text : Array (Fin σ)) (fallback : Fin σ)
    (u : Tree text.size Nat) (d : Nat) (a : Key text.size Nat)
    (hl : Tree.Locus (prepareSuffixes text fallback).trie.tree d u) (ha : a∈u.leaves) :
    Complete (ArrayText.read text fallback) text.size a.start d (positions u) := by
  have hh:=BoundaryTrie.Build.run_correct text fallback (suffixKeys text.size)
  exact suffix_locus_complete _ _ u d a hh.2.1 hh.1 hl ha

/-- Following an actual terminal path stops at the first complete class
for depth d. Lower equal-depth refinements cannot be selected instead. -/
theorem locate_complete (text : Array (Fin σ)) (fallback : Fin σ)
    (path : List Bool) (a : Key text.size Nat) (d : Nat)
    (hp : (prepareSuffixes text fallback).trie.tree.lookup path=some a) (hd : d≤a.length) :
    ∃u,Tree.locate d (prepareSuffixes text fallback).trie.tree path=some u ∧
      Tree.Locus (prepareSuffixes text fallback).trie.tree d u ∧
      a∈u.leaves ∧ Complete (ArrayText.read text fallback) text.size a.start d (positions u) := by
  have hg:=(BoundaryTrie.Build.run_correct text fallback (suffixKeys text.size)).2.1
  obtain ⟨u,hu,hl,ha⟩:=Tree.locate_correct _ _ path a d hg hp hd
  exact ⟨u,hu,hl,ha,prepareSuffixes_complete text fallback u d a hl ha⟩

def SuffixIndex.discover (I : SuffixIndex n) (i j L : Nat) : Option Bounds×Nat :=
  MaskedRunDiscovery.discover I.trie.prepared.ranks I.backward n i j L

theorem discover_locus (text : Array (Fin σ)) (fallback : Fin σ)
    (u : Tree text.size Nat) (a : Key text.size Nat) (L i j : Nat)
    (hl : Tree.Locus (prepareSuffixes text fallback).trie.tree L u) (ha : a∈u.leaves)
    (hadj : Adjacent (positions u) i j) (hdense : 2*(j-i)≤L) :
    ∃R,((prepareSuffixes text fallback).discover i j L).1=some R ∧
      R.Valid (ArrayText.read text fallback) text.size ∧ R.period=j-i ∧
      R.lo≤i ∧ j+L≤R.hi ∧ 3*R.period≤R.hi-R.lo := by
  have hh:=complete_discovery (ArrayText.read text fallback) text.size a.start L (positions u) i j
    (prepareSuffixes_complete text fallback u L a hl ha) hadj hdense
  simpa only [SuffixIndex.discover,prepareSuffixes_forward,prepareSuffixes_backward] using hh

theorem discover_locus_work (text : Array (Fin σ)) (fallback : Fin σ) (i j L : Nat) :
    ((prepareSuffixes text fallback).discover i j L).2≤26*(text.size.log2+1)+14 := by
  simp only [SuffixIndex.discover,prepareSuffixes_forward,prepareSuffixes_backward]
  exact discover_work _ _ i j L

theorem prepareSuffixes_work (text : Array (Fin σ)) (fallback : Fin σ) :
    (prepareSuffixes text fallback).work≤
      2*((text.size+1)*((text.size.log2+1)*(16*RankIndex.width σ text.size+4)+1))+
      (13*(text.size.log2+1)+12)*(8*(text.size+1)*((text.size+1).log2+1))+
      5*(text.size+1)+3+2*(text.size+1)*BoundaryTrie.Build.budget text.size (text.size+1) := by
  have ht:=BoundaryTrie.Build.run_work text fallback (suffixKeys text.size)
  rw [suffixKeys_length] at ht
  have hb:=prepareReverse_work (ArrayText.read text fallback) text.size
  simp only [prepareSuffixes]
  omega

end REWB.MaskedRunDiscovery
