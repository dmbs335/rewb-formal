import REWB.BoundaryApplicationStartStep

/-! Local text semantics for one actual forward-trie edge. The dynamic
C row comes from the measured source-summary pass. All three automata
use the same cut, including epsilon at either closed endpoint. -/
namespace REWB.BoundaryApplication.StartLocal
open REWB.BoundaryTrie
open REWB.Spec (slice)
open REWB.BoundaryIndex
variable {σ : Nat}

def entry (B C E : DFA (Fin σ)) (w : Word (Fin σ)) (t : StartKeys.TrieFor w)
    (p : Nat) (beta : Fin B.stateCount) (incoming : StartCuts.Row E) (row : StartCuts.Row C) :
    StartStep.Entry B C E :=
  ⟨(StartKeys.representative w t).start,t.depth,p,beta,incoming,row⟩

theorem target_segment (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat)
    (t : StartKeys.TrieFor w) (hg : t.Good (StartKeys.text w fallback)) (b : StartKeys.KeyFor w)
    (hb : b∈t.leaves) (j : Fin (w.length+1)) (hv : StartKeys.ValidKey g (StartKeys.originalKey w b))
    (ht : b.record=.target j) (p d : Nat) (hp : p≤d) (hd : d≤t.depth) :
    StartKeys.edgeWord w (StartKeys.representative w t).start p d=slice w (j.val+p) (j.val+d) :=
  StartKeys.target_edge w fallback g _ b j hv ht p d hp
    (Key.common_shorten _ _ _ _ _ (StartKeys.representative_common w fallback t hg b hb) hd)

theorem source_continue (C : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat)
    (t : StartKeys.TrieFor w) (hg : t.Good (StartKeys.text w fallback)) (a : StartKeys.KeyFor w)
    (ha : a∈t.leaves) (i : Fin (w.length+1)) (hv : StartKeys.ValidKey g (StartKeys.originalKey w a))
    (ht : a.record=.source i) (L : Nat) (hL : L≤t.depth) :
    C.run (C.run C.initial (StartKeys.edgeWord w (StartKeys.representative w t).start L t.depth))
      (slice w (i.val+t.depth) g)=C.run C.initial (slice w (i.val+L) g) := by
  have hc:=StartKeys.representative_common w fallback t hg a ha
  rw [StartKeys.source_edge w fallback g _ a i hv ht L t.depth hL hc]
  have hd:=hc.2.1
  simp only [StartKeys.ValidKey,StartKeys.originalKey] at hv
  rw [ht] at hv
  rw [hv.2.2] at hd
  rw [← DFA.run_append,← OuterColumn.slice_split w (i.val+L) (i.val+t.depth) g (by omega) (by omega)]

theorem row_continue (A C : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat)
    (t : StartKeys.TrieFor w) (hg : t.Good (StartKeys.text w fallback))
    (hv : ∀a,a∈t.leaves→StartKeys.ValidKey g (StartKeys.originalKey w a))
    (row : StartCuts.Row C) (hrow : ∀q,row.get q=true ↔ StartSummary.Source A C w g t q)
    (L : Nat) (hL : L≤t.depth) :
    row.get (C.run C.initial (StartKeys.edgeWord w (StartKeys.representative w t).start L t.depth))=true ↔
      ∃a,a∈t.leaves ∧ ∃i,a.record=.source i ∧ A.accepts (slice w 0 i.val) ∧
        C.accepts (slice w (i.val+L) g) := by
  rw [hrow]
  constructor
  · rintro ⟨a,ha,i,ht,hA,hC⟩
    exact ⟨a,ha,i,ht,hA,by
      unfold DFA.accepts
      rwa [source_continue C w fallback g t hg a ha i (hv a ha) ht L hL] at hC⟩
  · rintro ⟨a,ha,i,ht,hA,hC⟩
    exact ⟨a,ha,i,ht,hA,by
      rw [source_continue C w fallback g t hg a ha i (hv a ha) ht L hL]
      exact hC⟩

def Fresh (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (g : Nat)
    (t : StartKeys.TrieFor w) (j : Fin (w.length+1)) (p m : Nat) (q : Fin E.stateCount) : Prop :=
  ∃a,a∈t.leaves ∧ ∃i,a.record=.source i ∧ ∃L,p≤L ∧ L≤m ∧
    A.accepts (slice w 0 i.val) ∧ B.accepts (slice w j.val (j.val+L)) ∧
    C.accepts (slice w (i.val+L) g) ∧ E.run E.initial (slice w (j.val+L) (j.val+m))=q

theorem fresh_iff (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat)
    (t : StartKeys.TrieFor w) (hg : t.Good (StartKeys.text w fallback))
    (hv : ∀a,a∈t.leaves→StartKeys.ValidKey g (StartKeys.originalKey w a))
    (b : StartKeys.KeyFor w) (hb : b∈t.leaves) (j : Fin (w.length+1)) (ht : b.record=.target j)
    (p m : Nat) (hp : p≤m) (hm : m≤t.depth) (beta : Fin B.stateCount)
    (hbeta : beta=B.run B.initial (slice w j.val (j.val+p)))
    (row : StartCuts.Row C) (hrow : ∀q,row.get q=true ↔ StartSummary.Source A C w g t q)
    (q : Fin E.stateCount) :
    (∃x,(StartKeys.representative w t).start+p≤x ∧ x≤(StartKeys.representative w t).start+m ∧
      B.final (B.run beta (slice w ((StartKeys.representative w t).start+p) x))=true ∧
      row.get (C.run C.initial (slice w x ((StartKeys.representative w t).start+t.depth)))=true ∧
      E.run E.initial (slice w x ((StartKeys.representative w t).start+m))=q) ↔
      Fresh A B C E w g t j p m q := by
  let s:=(StartKeys.representative w t).start
  have hseg (a d : Nat) (had : a≤d) (hd : d≤t.depth) :
      slice w (s+a) (s+d)=slice w (j.val+a) (j.val+d) :=
    target_segment w fallback g t hg b hb j (hv b hb) ht a d had hd
  have hB (L : Nat) (hpl : p≤L) (hl : L≤m) :
      B.run beta (slice w (s+p) (s+L))=B.run B.initial (slice w j.val (j.val+L)) := by
    rw [hseg p L hpl (by omega),hbeta,← DFA.run_append,
      ← OuterColumn.slice_split w j.val (j.val+p) (j.val+L) (by omega) (by omega)]
  have hC (L : Nat) (hl : L≤m) := row_continue A C w fallback g t hg hv row hrow L (by omega)
  constructor
  · rintro ⟨x,hpx,hxm,hb',hc,he⟩
    let L:=x-s
    have hx : x=s+L := by dsimp only [L,s] at *; omega
    have hpl : p≤L := by dsimp only [L,s] at *; omega
    have hlm : L≤m := by dsimp only [L,s] at *; omega
    rw [hx,hB L hpl hlm] at hb'
    rw [hx] at hc he
    change row.get (C.run C.initial (StartKeys.edgeWord w s L t.depth))=true at hc
    obtain ⟨a,ha,i,ht',ha',hc'⟩:=(hC L hlm).mp hc
    refine ⟨a,ha,i,ht',L,hpl,hlm,ha',hb',hc',?_⟩
    rwa [hseg L m hlm hm] at he
  · rintro ⟨a,ha,i,ht',L,hpl,hlm,ha',hb',hc',he⟩
    refine ⟨s+L,by omega,by omega,?_,?_,?_⟩
    · rw [hB L hpl hlm]
      exact hb'
    · exact (hC L hlm).mpr ⟨a,ha,i,ht',ha',hc'⟩
    · rwa [hseg L m hlm hm]

theorem query_correct (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat)
    (t : StartKeys.TrieFor w) (hg : t.Good (StartKeys.text w fallback))
    (hv : ∀a,a∈t.leaves→StartKeys.ValidKey g (StartKeys.originalKey w a))
    (b : StartKeys.KeyFor w) (hb : b∈t.leaves) (j : Fin (w.length+1)) (ht : b.record=.target j)
    (p m : Nat) (hp : p≤m) (hm : m≤t.depth) (beta : Fin B.stateCount)
    (hbeta : beta=B.run B.initial (slice w j.val (j.val+p)))
    (incoming : StartCuts.Row E) (row : StartCuts.Row C)
    (hrow : ∀q,row.get q=true ↔ StartSummary.Source A C w g t q) (q : Fin E.stateCount) :
    (StartStep.query B C E (StartCuts.build B C E w) (Range.build C w) (Range.build E w)
      (entry B C E w t p beta incoming row) m).states.get q=true ↔
      (∃old,incoming.get old=true ∧ E.run old (slice w (j.val+p) (j.val+m))=q) ∨
        Fresh A B C E w g t j p m q := by
  have hn : t.leaves≠[] := by intro he; rw [he] at hb; cases hb
  rw [StartStep.query_correct B C E w _ m hp hm (StartKeys.representative_bound w fallback t hg hn)]
  simp only [entry]
  change (∃old,incoming.get old=true ∧ E.run old
      (StartKeys.edgeWord w (StartKeys.representative w t).start p m)=q) ∨ _ ↔ _
  rw [target_segment w fallback g t hg b hb j (hv b hb) ht p m hp hm,
    fresh_iff A B C E w fallback g t hg hv b hb j ht p m hp hm beta hbeta row hrow q]

end REWB.BoundaryApplication.StartLocal
