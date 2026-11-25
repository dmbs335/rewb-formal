import REWB.BoundaryApplicationHeavyQuery

/-! Exact source/target cut semantics in the actual reversed descriptor
trie. Node rows use one representative word; common-prefix proofs move
that word to the source and target endpoints without scanning it. -/
namespace REWB.BoundaryApplication.Coverage
open REWB.BoundaryTrie (Key)
open REWB.Spec (slice)
variable {σ : Nat}

def alpha (A : DFA (Fin σ)) (w : Word (Fin σ)) (source depth : Nat) : Fin A.stateCount :=
  A.run A.initial (slice w 0 (source-depth))

def Cut (A B D : DFA (Fin σ)) (w : Word (Fin σ)) (g : Nat)
    (source target : Fin (w.length+1)) (L : Nat) : Prop :=
  L≤source.val ∧ g+L≤target.val ∧
    slice w (source.val-L) source.val=slice w (target.val-L) target.val ∧
    A.accepts (slice w 0 (source.val-L)) ∧ B.accepts (slice w (source.val-L) source.val) ∧
    D.accepts (slice w g (target.val-L))

def Pair (A B D E : DFA (Fin σ)) (w : Word (Fin σ)) (g : Nat)
    (source target : Fin (w.length+1)) (right : Nat) : Prop :=
  target.val≤right ∧ E.accepts (slice w target.val right) ∧ ∃L,Cut A B D w g source target L

def Predicate (A B D E : DFA (Fin σ)) (w : Word (Fin σ)) (g : Nat)
    (source : Fin (w.length+1)) (right : Nat) : Prop :=
  ∃target,Pair A B D E w g source target right

theorem source_data (w : Word (Fin σ)) (g : Nat) (a : KeyFor w) (p : Fin (w.length+1))
    (hv : ValidKey g (originalKey w a)) (hp : a.record=.source p) :
    p.val≤g ∧ a.start=w.length-p.val ∧ a.length=p.val := by
  simpa only [ValidKey,originalKey,hp] using hv

theorem target_data (w : Word (Fin σ)) (g : Nat) (a : KeyFor w) (p : Fin (w.length+1))
    (hv : ValidKey g (originalKey w a)) (hp : a.record=.target p) :
    g≤p.val ∧ a.start=w.length-p.val ∧ a.length=p.val-g := by
  simpa only [ValidKey,originalKey,hp] using hv

theorem source_edge_word (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat)
    (a b : KeyFor w) (p : Fin (w.length+1))
    (hv : ValidKey g (originalKey w b)) (hp : b.record=.source p)
    (parent child : Nat) (hpc : parent≤child)
    (hc : Key.Common (reverseText w fallback) a b child) :
    edgeWord w a.start parent child=slice w (p.val-child) (p.val-parent) := by
  rw [edge_equal w fallback a b parent child hpc hc]
  have hh:=source_data w g b p hv hp
  unfold edgeWord
  rw [hh.2.1,show w.length-(w.length-p.val)=p.val by have h:=p.isLt; omega]

theorem shared_iff (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat)
    (a b : KeyFor w) (p t : Fin (w.length+1))
    (hva : ValidKey g (originalKey w a)) (ha : a.record=.source p)
    (hvb : ValidKey g (originalKey w b)) (hb : b.record=.target t) (L : Nat) :
    Key.Common (reverseText w fallback) a b L ↔
      L≤p.val ∧ g+L≤t.val ∧ slice w (p.val-L) p.val=slice w (t.val-L) t.val := by
  have hpa:=source_data w g a p hva ha
  have htb:=target_data w g b t hvb hb
  have hpbound : p.val≤w.length := by have hh:=p.isLt; omega
  have htbound : t.val≤w.length := by have hh:=t.isLt; omega
  constructor
  · intro hc
    have hc1 : L≤p.val := by rw [←hpa.2.2]; exact hc.1
    have hc2 : L≤t.val-g := by rw [←htb.2.2]; exact hc.2.1
    refine ⟨hc1,by omega,?_⟩
    have he:=target_edge w fallback g a b t hvb hb 0 L (Nat.zero_le _) hc
    simp only [edgeWord,hpa.2.1,Nat.sub_zero,
      show w.length-(w.length-p.val)=p.val by omega] at he
    exact he
  · rintro ⟨hL,hg,he⟩
    refine ⟨by rw [hpa.2.2]; exact hL,by rw [htb.2.2]; omega,?_⟩
    have hra:=reverse_segment w fallback a.start L (by rw [hpa.2.1]; omega)
    have hrb:=reverse_segment w fallback b.start L (by rw [htb.2.1]; omega)
    rw [hpa.2.1,show w.length-(w.length-p.val)=p.val by omega] at hra
    rw [htb.2.1,show w.length-(w.length-t.val)=t.val by omega] at hrb
    have hh:=congrArg List.reverse (hra.trans (he.trans hrb.symm))
    simpa only [List.reverse_reverse,hpa.2.1,htb.2.1] using hh

theorem prefix_run (A : DFA (Fin σ)) (w : Word (Fin σ)) (g endpoint depth L : Nat)
    (hg : g+depth≤endpoint) (hL : L≤depth) :
    A.run (A.run A.initial (slice w g (endpoint-depth))) (slice w (endpoint-depth) (endpoint-L))=
      A.run A.initial (slice w g (endpoint-L)) := by
  rw [←DFA.run_append,←OuterColumn.slice_split w g (endpoint-depth) (endpoint-L)
    (by omega) (by omega)]

theorem source_edge (A : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g parent : Nat) (child : TrieFor w) (a : KeyFor w) (p : Fin (w.length+1))
    (hg : child.Good (reverseText w fallback)) (ha : a∈child.leaves)
    (hv : ValidKey g (originalKey w a)) (hp : a.record=.source p)
    (hd : parent≤child.depth) :
    (edge A w (Range.build A w) parent child).map.get (alpha A w p.val child.depth)=
      alpha A w p.val parent := by
  have hc:=representative_common w fallback child hg a ha
  have hdata:=source_data w g a p hv hp
  have hdep : child.depth≤p.val := by rw [←hdata.2.2]; exact hc.2.1
  have he:=source_edge_word w fallback g (representative w child) a p hv hp parent child.depth hd hc
  simp only [edge,Range.build_length]
  rw [Range.query_correct A w _ _ (by omega) (by omega)]
  change A.run (alpha A w p.val child.depth) (edgeWord w (representative w child).start parent child.depth)=_
  rw [he]
  exact prefix_run A w 0 p.val child.depth parent (by omega) hd

theorem node_cut_iff (A B D : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g : Nat) (u : TrieFor w) (hg : u.Good (reverseText w fallback))
    (a b : KeyFor w) (p t : Fin (w.length+1))
    (ha : a∈u.leaves) (hb : b∈u.leaves)
    (hva : ValidKey g (originalKey w a)) (hsa : a.record=.source p)
    (hvb : ValidKey g (originalKey w b)) (htb : b.record=.target t) :
    BoundaryIndex.FixedEnd.Predicate A B D w (w.length-(representative w u).start)
      u.depth 0 u.depth (alpha A w p.val u.depth) (color D w g t u.depth) ↔
      ∃L,L≤u.depth ∧ Cut A B D w g p t L := by
  have hca:=representative_common w fallback u hg a ha
  have hcb:=representative_common w fallback u hg b hb
  have hpa:=source_data w g a p hva hsa
  have htarget:=target_data w g b t hvb htb
  have hdA : u.depth≤p.val := by rw [←hpa.2.2]; exact hca.2.1
  have hdD : g+u.depth≤t.val := by have hh:=hcb.2.1; rw [htarget.2.2] at hh; omega
  have hcommon:=BoundaryTrie.Tree.depth_common (reverseText w fallback) u hg a b ha hb
  have hwords : ∀L,L≤u.depth→
      slice w (w.length-(representative w u).start-u.depth) (w.length-(representative w u).start-L)=
        slice w (p.val-u.depth) (p.val-L) ∧
      slice w (w.length-(representative w u).start-u.depth) (w.length-(representative w u).start-L)=
        slice w (t.val-u.depth) (t.val-L) ∧
      slice w (w.length-(representative w u).start-L) (w.length-(representative w u).start)=
        slice w (p.val-L) p.val := by
    intro L hL
    refine ⟨source_edge_word w fallback g _ a p hva hsa L u.depth hL hca,
      target_edge w fallback g _ b t hvb htb L u.depth hL hcb,?_⟩
    have hh:=source_edge_word w fallback g _ a p hva hsa 0 L (Nat.zero_le _)
      (Key.common_shorten _ _ _ _ _ hca hL)
    simpa only [edgeWord,Nat.sub_zero] using hh
  constructor
  · rintro ⟨L,_,hL,hA,hD,hB⟩
    have hw:=hwords L hL
    have hc:=(shared_iff w fallback g a b p t hva hsa hvb htb L).mp
      (Key.common_shorten _ _ _ _ _ hcommon hL)
    refine ⟨L,hL,hc.1,hc.2.1,hc.2.2,?_,?_,?_⟩
    · rw [hw.1] at hA
      exact (show A.final (A.run A.initial (slice w 0 (p.val-L)))=true from by
        rwa [alpha,prefix_run A w 0 p.val u.depth L (by omega) hL] at hA)
    · rwa [hw.2.2] at hB
    · rw [hw.2.1] at hD
      exact (show D.final (D.run D.initial (slice w g (t.val-L)))=true from by
        rwa [color,prefix_run D w g t.val u.depth L hdD hL] at hD)
  · rintro ⟨L,hL,_,_,_,hA,hB,hD⟩
    have hw:=hwords L hL
    refine ⟨L,Nat.zero_le _,hL,?_,?_,?_⟩
    · rw [hw.1,alpha,prefix_run A w 0 p.val u.depth L (by omega) hL]
      exact hA
    · rw [hw.2.1,color,prefix_run D w g t.val u.depth L hdD hL]
      exact hD
    · rwa [hw.2.2]

theorem lca_cut_bound (A B D : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g : Nat) (u : TrieFor w) (hg : u.Good (reverseText w fallback))
    (a b : KeyFor w) (p t : Fin (w.length+1)) (H L : Nat)
    (hva : ValidKey g (originalKey w a)) (hsa : a.record=.source p)
    (hvb : ValidKey g (originalKey w b)) (htb : b.record=.target t)
    (hlca : BoundaryTrie.Tree.LCA u a b H) (hc : Cut A B D w g p t L) : L≤H := by
  apply (BoundaryTrie.Tree.lca_exact (reverseText w fallback) u a b H hg hlca).2
  exact (shared_iff w fallback g a b p t hva hsa hvb htb L).mpr ⟨hc.1,hc.2.1,hc.2.2.1⟩

end REWB.BoundaryApplication.Coverage
