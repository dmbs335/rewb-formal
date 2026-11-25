import REWB.BoundaryApplicationCoverage
import REWB.BoundaryApplicationStartStep

/-! Actual descriptors for two separated boundaries g0≤g1. Sources
end at a≤g0; targets are factors beginning at g1. The common reversed
text and exact LCE builder are shared, and no key word is copied. -/
namespace REWB.BoundaryApplication.Separated
open REWB.BoundaryTrie
variable {σ : Nat}

def keep (g0 : Nat) {n : Nat} (a : Key n (Endpoint n)) : Bool :=
  match a.record with
  | .source p => decide (p.val≤g0)
  | .target _ => true

def keys (w : Word (Fin σ)) (g0 g1 : Nat) (h1 : g1≤w.length) : List (KeyFor w) :=
  (reverseKeys w g1 h1).filter (fun a=>keep g0 (originalKey w a))

theorem keys_length (w : Word (Fin σ)) (g0 g1 : Nat) (h1 : g1≤w.length) :
    (keys w g0 g1 h1).length≤w.length+2 := by
  have hh:=List.length_filter_le (fun a=>keep g0 (originalKey w a)) (reverseKeys w g1 h1)
  simpa only [reverseKeys_length] using hh

theorem keys_valid (w : Word (Fin σ)) (g0 g1 : Nat) (h1 : g1≤w.length)
    (a : KeyFor w) (ha : a∈keys w g0 g1 h1) : ValidKey g1 (originalKey w a) :=
  reverseKeys_valid w g1 h1 a (List.mem_filter.mp ha).1

theorem keys_source_bound (w : Word (Fin σ)) (g0 g1 : Nat) (h1 : g1≤w.length)
    (a : KeyFor w) (ha : a∈keys w g0 g1 h1) (p : Fin (w.length+1)) (hp : a.record=.source p) : p.val≤g0 := by
  have hh:=(List.mem_filter.mp ha).2
  simpa only [keep,originalKey,hp,decide_eq_true_eq] using hh

theorem source_mem (w : Word (Fin σ)) (g0 g1 : Nat) (h01 : g0≤g1) (h1 : g1≤w.length)
    (p : Fin (w.length+1)) (hp : p.val≤g0) : ∃a,a∈keys w g0 g1 h1 ∧ a.record=.source p := by
  obtain ⟨a,ha,ht⟩:=BoundaryApplication.source_mem w.length g1 h1 p (by omega)
  have hm : a∈(reverseKeys w g1 h1).map (originalKey w) := by rw [original_reverseKeys]; exact ha
  obtain ⟨b,hb,he⟩:=List.mem_map.mp hm
  have hr : b.record=.source p := (congrArg Key.record he).trans ht
  refine ⟨b,List.mem_filter.mpr ⟨hb,?_⟩,hr⟩
  simp only [keep,originalKey,hr,decide_eq_true_eq,hp]

theorem target_mem (w : Word (Fin σ)) (g0 g1 : Nat) (h1 : g1≤w.length)
    (p : Fin (w.length+1)) (hp : g1≤p.val) : ∃a,a∈keys w g0 g1 h1 ∧ a.record=.target p := by
  obtain ⟨a,ha,ht⟩:=BoundaryApplication.target_mem w.length g1 h1 p hp
  have hm : a∈(reverseKeys w g1 h1).map (originalKey w) := by rw [original_reverseKeys]; exact ha
  obtain ⟨b,hb,he⟩:=List.mem_map.mp hm
  have hr : b.record=.target p := (congrArg Key.record he).trans ht
  refine ⟨b,List.mem_filter.mpr ⟨hb,?_⟩,hr⟩
  simp only [keep,originalKey,hr]

def trie (w : Word (Fin σ)) (fallback : Fin σ) (g0 g1 : Nat) (h1 : g1≤w.length) :=
  BoundaryTrie.Build.run (reversed w) fallback (keys w g0 g1 h1)

theorem trie_good (w : Word (Fin σ)) (fallback : Fin σ) (g0 g1 : Nat) (h1 : g1≤w.length) :
    (trie w fallback g0 g1 h1).tree.Good (reverseText w fallback) :=
  (BoundaryTrie.Build.run_correct (reversed w) fallback (keys w g0 g1 h1)).2.1

theorem trie_valid (w : Word (Fin σ)) (fallback : Fin σ) (g0 g1 : Nat) (h1 : g1≤w.length)
    (a : KeyFor w) (ha : a∈(trie w fallback g0 g1 h1).tree.leaves) : ValidKey g1 (originalKey w a) :=
  keys_valid w g0 g1 h1 a ((BoundaryTrie.Build.run_correct (reversed w) fallback (keys w g0 g1 h1)).1.mem_iff.mp ha)

theorem trie_source_bound (w : Word (Fin σ)) (fallback : Fin σ) (g0 g1 : Nat) (h1 : g1≤w.length)
    (a : KeyFor w) (ha : a∈(trie w fallback g0 g1 h1).tree.leaves)
    (p : Fin (w.length+1)) (hp : a.record=.source p) : p.val≤g0 :=
  keys_source_bound w g0 g1 h1 a ((BoundaryTrie.Build.run_correct (reversed w) fallback (keys w g0 g1 h1)).1.mem_iff.mp ha) p hp

theorem trie_nonempty (w : Word (Fin σ)) (fallback : Fin σ) (g0 g1 : Nat) (h1 : g1≤w.length) :
    (trie w fallback g0 g1 h1).tree.leaves≠[] := by
  obtain ⟨a,ha,ht⟩:=target_mem w g0 g1 h1 ⟨g1,by omega⟩ (Nat.le_refl _)
  have hm:=(BoundaryTrie.Build.run_correct (reversed w) fallback (keys w g0 g1 h1)).1.mem_iff.mpr ha
  intro he
  change a∈(trie w fallback g0 g1 h1).tree.leaves at hm
  rw [he] at hm
  cases hm

theorem trie_nodes (w : Word (Fin σ)) (fallback : Fin σ) (g0 g1 : Nat) (h1 : g1≤w.length) :
    (trie w fallback g0 g1 h1).tree.nodes≤2*(keys w g0 g1 h1).length :=
  (BoundaryTrie.Build.run_correct (reversed w) fallback (keys w g0 g1 h1)).2.2.1

end REWB.BoundaryApplication.Separated
