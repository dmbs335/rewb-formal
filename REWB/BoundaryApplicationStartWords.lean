import REWB.BoundaryApplicationStartCoverage

/-! The prefix-trie relation is equivalent to equality of the two
actual text factors. This removes the chosen target descriptor from the
query invariant and keeps all endpoint bounds explicit. -/
namespace REWB.BoundaryApplication.StartCoverage
open REWB.BoundaryTrie
open REWB.Spec (slice)
variable {σ : Nat}

theorem common_words (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat)
    (a b : StartKeys.KeyFor w) (i j : Fin (w.length+1))
    (ha : StartKeys.ValidKey g (StartKeys.originalKey w a))
    (hb : StartKeys.ValidKey g (StartKeys.originalKey w b))
    (hi : a.record=.source i) (hj : b.record=.target j) (L : Nat) :
    Key.Common (StartKeys.text w fallback) a b L ↔
      L≤g-i.val ∧ L≤w.length-j.val ∧ slice w i.val (i.val+L)=slice w j.val (j.val+L) := by
  simp only [StartKeys.ValidKey,StartKeys.originalKey,hi,hj] at ha hb
  unfold Key.Common
  rw [ha.2.1,ha.2.2,hb.2.1,hb.2.2]
  constructor
  · rintro ⟨hs,ht,he⟩
    have hab:=a.bounded
    simp only [List.size_toArray,ha.2.1,ha.2.2] at hab
    rw [StartKeys.segment_slice w fallback i.val L (by omega),
      StartKeys.segment_slice w fallback j.val L (by have hh:=j.isLt; omega)] at he
    exact ⟨hs,ht,he⟩
  · rintro ⟨hs,ht,he⟩
    have hab:=a.bounded
    simp only [List.size_toArray,ha.2.1,ha.2.2] at hab
    refine ⟨hs,ht,?_⟩
    rwa [StartKeys.segment_slice w fallback i.val L (by omega),
      StartKeys.segment_slice w fallback j.val L (by have hh:=j.isLt; omega)]

def Words (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (g : Nat)
    (whole : StartKeys.TrieFor w) (j : Fin (w.length+1)) (bound finish : Nat) (q : Fin E.stateCount) : Prop :=
  ∃a,a∈whole.leaves ∧ ∃i,a.record=.source i ∧ ∃L,L≤bound ∧
    L≤g-i.val ∧ L≤w.length-j.val ∧ slice w i.val (i.val+L)=slice w j.val (j.val+L) ∧
    A.accepts (slice w 0 i.val) ∧ B.accepts (slice w j.val (j.val+L)) ∧
    C.accepts (slice w (i.val+L) g) ∧ E.run E.initial (slice w (j.val+L) (j.val+finish))=q

theorem hits_words (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat)
    (whole : StartKeys.TrieFor w)
    (hv : ∀a,a∈whole.leaves→StartKeys.ValidKey g (StartKeys.originalKey w a))
    (b : StartKeys.KeyFor w) (hb : StartKeys.ValidKey g (StartKeys.originalKey w b))
    (j : Fin (w.length+1)) (ht : b.record=.target j) (bound finish : Nat) (q : Fin E.stateCount) :
    Hits A B C E w fallback g whole b j bound finish q ↔ Words A B C E w g whole j bound finish q := by
  constructor
  · rintro ⟨a,ha,i,hi,L,hL,hcom,hA,hB,hC,hE⟩
    obtain ⟨hs,ht',he⟩:=(common_words w fallback g a b i j (hv a ha) hb hi ht L).mp hcom
    exact ⟨a,ha,i,hi,L,hL,hs,ht',he,hA,hB,hC,hE⟩
  · rintro ⟨a,ha,i,hi,L,hL,hs,ht',he,hA,hB,hC,hE⟩
    exact ⟨a,ha,i,hi,L,hL,(common_words w fallback g a b i j (hv a ha) hb hi ht L).mpr
      ⟨hs,ht',he⟩,hA,hB,hC,hE⟩

end REWB.BoundaryApplication.StartCoverage
