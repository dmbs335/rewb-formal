import REWB.BoundaryApplicationSeparatedCuts

/-! Exact coverage for the reversed-trie row pass. Ancestor rows retain
cuts from sources outside a selected child. The strict inequality in
Covered is essential: zero-depth binary refinements need not be complete
prefix occurrence classes, while every longer shared prefix is contained
in the selected child. -/
namespace REWB.BoundaryApplication.Separated.Coverage
open REWB.BoundaryTrie
open REWB.Spec (slice)
open REWB.BoundaryIndex
variable {σ : Nat}

def Covered (w : Word (Fin σ)) (fallback : Fin σ) (whole t : TrieFor w) (p : Nat) : Prop :=
  (∀a,a∈t.leaves→a∈whole.leaves) ∧
    ∀b,b∈t.leaves→∀a,a∈whole.leaves→∀L,p<L→Key.Common (reverseText w fallback) a b L→a∈t.leaves

theorem covered_root (w : Word (Fin σ)) (fallback : Fin σ) (t : TrieFor w) (p : Nat) :
    Covered w fallback t t p := ⟨fun _ h=>h,fun _ _ _ h _ _ _=>h⟩

theorem covered_left (w : Word (Fin σ)) (fallback : Fin σ) (whole : TrieFor w)
    (stem : KeyFor w) (d : Nat) (l r : TrieFor w) (p : Nat)
    (hg : (BoundaryTrie.Tree.node stem d l r).Good (reverseText w fallback))
    (hp : p≤d) (hc : Covered w fallback whole (.node stem d l r) p) : Covered w fallback whole l d := by
  refine ⟨fun a ha=>hc.1 a (List.mem_append_left _ ha),?_⟩
  intro b hb a ha L hL hcom
  have hin:=hc.2 b (List.mem_append_left _ hb) a ha L (by omega) hcom
  rcases List.mem_append.mp hin with hal | har
  · exact hal
  · have hex:=hg.2.2.2.2.2.2 b hb a har
    have hbound:=hex.2 L ((Key.common_symmetric _ _ _ _).mp hcom)
    omega

theorem covered_right (w : Word (Fin σ)) (fallback : Fin σ) (whole : TrieFor w)
    (stem : KeyFor w) (d : Nat) (l r : TrieFor w) (p : Nat)
    (hg : (BoundaryTrie.Tree.node stem d l r).Good (reverseText w fallback))
    (hp : p≤d) (hc : Covered w fallback whole (.node stem d l r) p) : Covered w fallback whole r d := by
  refine ⟨fun a ha=>hc.1 a (List.mem_append_right _ ha),?_⟩
  intro b hb a ha L hL hcom
  have hin:=hc.2 b (List.mem_append_right _ hb) a ha L (by omega) hcom
  rcases List.mem_append.mp hin with hal | har
  · have hex:=hg.2.2.2.2.2.2 a hal b hb
    have hbound:=hex.2 L hcom
    omega
  · exact har

theorem combine_iff (A B C D : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g0 g1 : Nat) (whole t : TrieFor w)
    (hv : ∀a,a∈whole.leaves→ValidKey g1 (originalKey w a))
    (p : Nat) (hp : p≤t.depth) (hc : Covered w fallback whole t p)
    (b : KeyFor w) (hb : b∈t.leaves) (target : Fin (w.length+1)) (ht : b.record=.target target) :
    Cuts.Hits A B C D w g0 g1 whole target p ∨ Cuts.Hits A B C D w g0 g1 t target t.depth ↔
      Cuts.Hits A B C D w g0 g1 whole target t.depth := by
  constructor
  · rintro (⟨a,ha,s,hs,hC,L,hL,hcut⟩ | ⟨a,ha,s,hs,hC,L,hL,hcut⟩)
    · exact ⟨a,ha,s,hs,hC,L,by omega,hcut⟩
    · exact ⟨a,hc.1 a ha,s,hs,hC,L,hL,hcut⟩
  · rintro ⟨a,ha,s,hs,hC,L,hL,hcut⟩
    by_cases hLp : L≤p
    · exact Or.inl ⟨a,ha,s,hs,hC,L,hLp,hcut⟩
    · have hcommon:=(BoundaryApplication.Coverage.shared_iff w fallback g1 a b s target
        (hv a ha) hs (hv b (hc.1 b hb)) ht L).mpr ⟨hcut.1,hcut.2.1,hcut.2.2.1⟩
      exact Or.inr ⟨a,hc.2 b hb a ha L (by omega) hcommon,s,hs,hC,L,hL,hcut⟩

def Previous (A B C D : DFA (Fin σ)) (w : Word (Fin σ)) (g0 g1 : Nat)
    (whole t : TrieFor w) (p : Nat) (incoming : Vector Bool D.stateCount) : Prop :=
  (t=whole ∧ ∀q,incoming.get q=false) ∨
    ∀b,b∈t.leaves→∀target,b.record=.target target→
      (incoming.get (color D w g1 target p)=true ↔ Cuts.Hits A B C D w g0 g1 whole target p)

theorem advance_hits (A B C D : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g0 g1 : Nat) (whole t : TrieFor w) (hg : t.Good (reverseText w fallback))
    (hv : ∀a,a∈whole.leaves→ValidKey g1 (originalKey w a))
    (p : Nat) (hp : p≤t.depth) (hc : Covered w fallback whole t p)
    (b : KeyFor w) (hb : b∈t.leaves) (target : Fin (w.length+1)) (ht : b.record=.target target)
    (source : Vector Bool A.stateCount)
    (hsource : ∀q,source.get q=true ↔ Summary.Source A C w g0 t q)
    (incoming : Vector Bool D.stateCount) (hprev : Previous A B C D w g0 g1 whole t p incoming) :
    (Cuts.advance A B D (RTable.prepare A B D w) (Range.build D w)
      (representative w t).start t.depth p source incoming).row.get (color D w g1 target t.depth)=true ↔
      Cuts.Hits A B C D w g0 g1 whole target t.depth := by
  rw [Cuts.advance_correct A B C D w fallback g0 g1 p t hg hp
    (fun a ha=>hv a (hc.1 a ha)) b hb target ht source hsource incoming]
  rcases hprev with ⟨he,hfalse⟩ | hprev
  · rw [hfalse,Bool.false_eq_true,false_or,he]
  · rw [hprev b hb target ht]
    exact combine_iff A B C D w fallback g0 g1 whole t hv p hp hc b hb target ht

def Full (A B C D : DFA (Fin σ)) (w : Word (Fin σ)) (g0 g1 : Nat)
    (whole : TrieFor w) (target : Fin (w.length+1)) : Prop :=
  ∃a,a∈whole.leaves ∧ ∃p,a.record=.source p ∧ C.accepts (slice w p.val g0) ∧
    ∃L,BoundaryApplication.Coverage.Cut A B D w g1 p target L

theorem leaf_full (A B C D : DFA (Fin σ)) (w : Word (Fin σ)) (g0 g1 : Nat)
    (whole : TrieFor w) (b : KeyFor w) (target : Fin (w.length+1))
    (hv : ValidKey g1 (originalKey w b)) (ht : b.record=.target target) :
    Cuts.Hits A B C D w g0 g1 whole target b.length ↔ Full A B C D w g0 g1 whole target := by
  have hd:=BoundaryApplication.Coverage.target_data w g1 b target hv ht
  constructor
  · rintro ⟨a,ha,p,hp,hC,L,_,hcut⟩
    exact ⟨a,ha,p,hp,hC,L,hcut⟩
  · rintro ⟨a,ha,p,hp,hC,L,hcut⟩
    refine ⟨a,ha,p,hp,hC,L,?_,hcut⟩
    rw [hd.2.2]
    have hh:=hcut.2.1
    omega

end REWB.BoundaryApplication.Separated.Coverage
