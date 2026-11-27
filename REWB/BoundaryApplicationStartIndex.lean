import REWB.BoundaryApplicationStartSound
import REWB.BoundaryApplicationStartLocateIndex

/-! Closed fixed-start construction from the input word and boundary.
The alphabet array, exact-LCE descriptor trie, four materialized DFA
range indexes, joint-cut index, source rows, top-down payloads, and
parent-doubling table are all built here. No tree or answer is supplied
by the caller. Word length and ancestor width are cached once. -/
namespace REWB.BoundaryApplication.StartIndex
open REWB.BoundaryTrie
open REWB.BoundaryIndex
variable {σ : Nat}

theorem forward_source (w : Word (Fin σ)) (g : Nat) (hg : g≤w.length)
    (i : Fin (w.length+1)) (hi : i.val≤g) :
    ∃a,a∈StartKeys.forwardKeys w g hg ∧ a.record=.source i := by
  obtain ⟨a,ha,ht⟩:=StartKeys.source_mem w.length g hg i hi
  have hm : a∈(StartKeys.forwardKeys w g hg).map (StartKeys.originalKey w) := by
    rw [StartKeys.original_forwardKeys]; exact ha
  obtain ⟨b,hb,he⟩:=List.mem_map.mp hm
  exact ⟨b,hb,(congrArg Key.record he).trans ht⟩

theorem forward_target (w : Word (Fin σ)) (g : Nat) (hg : g≤w.length)
    (j : Fin (w.length+1)) (hj : g≤j.val) :
    ∃a,a∈StartKeys.forwardKeys w g hg ∧ a.record=.target j := by
  obtain ⟨a,ha,ht⟩:=StartKeys.target_mem w.length g hg j hj
  have hm : a∈(StartKeys.forwardKeys w g hg).map (StartKeys.originalKey w) := by
    rw [StartKeys.original_forwardKeys]; exact ha
  obtain ⟨b,hb,he⟩:=List.mem_map.mp hm
  exact ⟨b,hb,(congrArg Key.record he).trans ht⟩

def levels (n : Nat) : Nat := (2*(n+2)).log2+1

def rangeBuildWork (D : DFA (Fin σ)) (idx : Range.Index D) : Nat :=
  D.stateCount*idx.products+idx.letterCells+idx.length+3

def cutBuildWork (B C E : DFA (Fin σ)) (idx : StartCuts.Index B C E) : Nat :=
  let z:=(MarkedTransfer.enum B (StartCuts.rightDFA C E)).elems.length
  idx.products+(idx.length+1)*(z*z)+idx.length+2

structure Index (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) where
  trie : BoundaryTrie.Build.Index w.toArray.size (Endpoint w.length)
  cranges : Range.Index C
  eranges : Range.Index E
  cuts : StartCuts.Index B C E
  paths : StartLocate.Tree (StartStep.Entry B C E) (w.length+1)
  addresses : StartLocate.Store (StartStep.Entry B C E) (w.length+1)
  cachedLength : Nat
  length_eq : cachedLength=w.length
  levels : Nat
  work : Nat

def build (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat) (hg : g≤w.length) :
    Index A B C E w :=
  let trie:=BoundaryTrie.Build.run w.toArray fallback (StartKeys.forwardKeys w g hg)
  let aranges:=Range.build A w
  let branges:=Range.build B w
  let cranges:=Range.build C w
  let eranges:=Range.build E w
  let cuts:=StartCuts.build B C E w
  let summaries:=StartSummary.build A C w aranges cranges trie.tree
  let paths:=StartPass.go B C E cuts branges cranges eranges summaries.1 0 B.initial (Vector.ofFn (fun _=>false))
  let n:=w.toArray.size
  let rows:=levels n
  let addresses:=StartLocate.build rows paths.1
  ⟨trie,cranges,eranges,cuts,paths.1,addresses,n,by simp only [n,List.size_toArray],rows,
    trie.work+rangeBuildWork A aranges+rangeBuildWork B branges+rangeBuildWork C cranges+
      rangeBuildWork E eranges+cutBuildWork B C E cuts+summaries.2+paths.2+addresses.work+
        3*n+E.stateCount+10⟩

theorem trie_good (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat) (hg : g≤w.length) :
    (BoundaryTrie.Build.run w.toArray fallback (StartKeys.forwardKeys w g hg)).tree.Good (StartKeys.text w fallback) :=
  (BoundaryTrie.Build.run_correct w.toArray fallback (StartKeys.forwardKeys w g hg)).2.1

theorem trie_nonempty (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat) (hg : g≤w.length) :
    (BoundaryTrie.Build.run w.toArray fallback (StartKeys.forwardKeys w g hg)).tree.leaves≠[] := by
  have hh:=(BoundaryTrie.Build.run_correct w.toArray fallback (StartKeys.forwardKeys w g hg)).1.length_eq
  rw [StartKeys.forwardKeys_length] at hh
  intro he
  rw [he,List.length_nil] at hh
  omega

theorem trie_valid (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat) (hg : g≤w.length)
    (a : StartKeys.KeyFor w)
    (ha : a∈(BoundaryTrie.Build.run w.toArray fallback (StartKeys.forwardKeys w g hg)).tree.leaves) :
    StartKeys.ValidKey g (StartKeys.originalKey w a) :=
  StartKeys.forwardKeys_valid w g hg a ((BoundaryTrie.Build.run_correct w.toArray fallback
    (StartKeys.forwardKeys w g hg)).1.mem_iff.mp ha)

theorem build_good (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat) (hg : g≤w.length) :
    (build A B C E w fallback g hg).paths.Good := by
  apply StartPass.go_good B C E _ _ _ _ (StartKeys.text w fallback)
  · rw [StartSummary.build_shape]; exact trie_good w fallback g hg
  · rw [StartSummary.build_shape]; exact trie_nonempty w fallback g hg

theorem build_linked (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat) (hg : g≤w.length) :
    StartSound.Linked B C E (build A B C E w fallback g hg).paths 0 :=
  StartSound.go_linked B C E _ _ _ _ _ _ _ _

theorem build_sound (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat) (hg : g≤w.length) :
    StartSound.Sound A B C E w g (build A B C E w fallback g hg).trie.tree (build A B C E w fallback g hg).paths := by
  apply StartSound.go_sound A B C E w fallback g _ _ (trie_valid w fallback g hg)
    (trie_good w fallback g hg) (trie_nonempty w fallback g hg) (trie_valid w fallback g hg) 0 (Nat.zero_le _)
    (StartCoverage.covered_root w fallback _ 0) B.initial
  · intro b hb j ht
    simp only [Nat.add_zero,Spec.slice,Nat.sub_self,List.take_zero,DFA.run]
  · exact Or.inl ⟨rfl,rfl,fun q=>Table.get_ofFn _ _⟩

theorem build_nodes (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat) (hg : g≤w.length) :
    (build A B C E w fallback g hg).paths.nodes≤2*(w.length+2) := by
  have hn:=StartPass.go_nodes B C E (StartCuts.build B C E w) (Range.build B w) (Range.build C w) (Range.build E w)
    (StartKeys.text w fallback)
    (StartSummary.build A C w (Range.build A w) (Range.build C w)
      (BoundaryTrie.Build.run w.toArray fallback (StartKeys.forwardKeys w g hg)).tree).1
    (by rw [StartSummary.build_shape]; exact trie_good w fallback g hg)
    (by rw [StartSummary.build_shape]; exact trie_nonempty w fallback g hg) 0 B.initial (Vector.ofFn (fun _=>false))
  rw [StartSummary.build_shape] at hn
  have hb:=(BoundaryTrie.Build.run_correct w.toArray fallback (StartKeys.forwardKeys w g hg)).2.2.1
  rw [StartKeys.forwardKeys_length] at hb
  exact Nat.le_trans (Nat.le_of_eq hn) hb

theorem build_capacity (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat) (hg : g≤w.length) :
    (build A B C E w fallback g hg).paths.nodes≤2^(build A B C E w fallback g hg).levels := by
  have hn:=build_nodes A B C E w fallback g hg
  change _≤2^(levels w.toArray.size)
  rw [List.size_toArray]
  exact Nat.le_trans hn (Nat.le_of_lt Nat.lt_log2_self)

theorem build_target (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat) (hg : g≤w.length)
    (j : Fin (w.length+1)) (hj : g≤j.val) : StartLocate.HasTarget j (build A B C E w fallback g hg).paths := by
  apply (StartSound.go_target B C E _ _ _ _ _ _ _ _ j).mpr
  rw [StartSummary.build_shape]
  obtain ⟨a,ha,ht⟩:=forward_target w g hg j hj
  exact ⟨a,(BoundaryTrie.Build.run_correct w.toArray fallback (StartKeys.forwardKeys w g hg)).1.mem_iff.mpr ha,ht⟩

end REWB.BoundaryApplication.StartIndex
