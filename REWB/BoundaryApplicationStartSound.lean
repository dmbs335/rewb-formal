import REWB.BoundaryApplicationStartWords
import REWB.BoundaryApplicationStartLocateBuild

/-! Every payload produced by the measured top-down pass has exact
global fixed-start text semantics for every target below it. The generic
ancestor locator can therefore select a payload without inspecting any
source, key word, or stored path. -/
namespace REWB.BoundaryApplication.StartSound
open REWB.BoundaryTrie
open REWB.BoundaryIndex
open REWB.Spec (slice)
open StartCoverage
variable {α : Type} {σ n m : Nat}

theorem go_target (B C E : DFA α) (cuts : StartCuts.Index B C E) (branges : Range.Index B)
    (cranges : Range.Index C) (eranges : Range.Index E)
    (s : StartSummary.Saved C.stateCount n (Endpoint m)) (p : Nat) (beta : Fin B.stateCount)
    (incoming : StartCuts.Row E) (j : Fin (m+1)) :
    StartLocate.HasTarget j (StartPass.go B C E cuts branges cranges eranges s p beta incoming).1 ↔
      ∃a,a∈(StartSummary.shape s).leaves ∧ a.record=.target j := by
  induction s generalizing p beta incoming with
  | empty => simp only [StartPass.go,StartLocate.HasTarget,StartSummary.shape,BoundaryTrie.Tree.leaves,
      List.not_mem_nil,false_and,exists_false,reduceCtorEq]
  | leaf key row =>
    cases ht : key.record <;> simp only [StartPass.go,StartLocate.HasTarget,StartPass.terminal,ht,
      StartSummary.shape,BoundaryTrie.Tree.leaves,List.mem_singleton,exists_eq_left,
      Option.some.injEq,Endpoint.target.injEq,reduceCtorEq]
  | node key d row l r ihl ihr =>
    simp only [StartPass.go,StartLocate.HasTarget,ihl,ihr,StartSummary.shape,BoundaryTrie.Tree.leaves,List.mem_append]
    constructor
    · rintro (⟨a,ha,ht⟩ | ⟨a,ha,ht⟩)
      · exact ⟨a,Or.inl ha,ht⟩
      · exact ⟨a,Or.inr ha,ht⟩
    · rintro ⟨a,ha,ht⟩
      exact ha.elim (fun h=>Or.inl ⟨a,h,ht⟩) (fun h=>Or.inr ⟨a,h,ht⟩)

def Linked (B C E : DFA α) : StartLocate.Tree (StartStep.Entry B C E) (m+1)→Nat→Prop
  | .leaf _ e _,p => e.parentDepth=p
  | .node d e l r,p => e.parentDepth=p ∧ Linked B C E l d ∧ Linked B C E r d

theorem linked_root (B C E : DFA α) (t : StartLocate.Tree (StartStep.Entry B C E) (m+1))
    (p : Nat) (h : Linked B C E t p) : t.payload.parentDepth=p := by
  cases t with
  | leaf _ _ _ => exact h
  | node _ _ _ _ => exact h.1

theorem go_linked (B C E : DFA α) (cuts : StartCuts.Index B C E) (branges : Range.Index B)
    (cranges : Range.Index C) (eranges : Range.Index E)
    (s : StartSummary.Saved C.stateCount n (Endpoint m)) (p : Nat) (beta : Fin B.stateCount)
    (incoming : StartCuts.Row E) :
    Linked B C E (StartPass.go B C E cuts branges cranges eranges s p beta incoming).1 p := by
  induction s generalizing p beta incoming with
  | empty => rfl
  | leaf key row => rfl
  | node key d row l r ihl ihr => exact ⟨rfl,ihl _ _ _,ihr _ _ _⟩

def NodeSound (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (g : Nat) (whole : StartKeys.TrieFor w)
    (t : StartLocate.Tree (StartStep.Entry B C E) (w.length+1)) : Prop :=
  t.payload.depth=t.depth ∧ t.payload.start+t.payload.depth≤w.length ∧
    ∀j,StartLocate.HasTarget j t→∀m,t.payload.parentDepth≤m→m≤t.depth→∀q,
      (StartStep.query B C E (StartCuts.build B C E w) (Range.build C w) (Range.build E w) t.payload m).states.get q=true ↔
        Words A B C E w g whole j m m q

def Sound (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (g : Nat) (whole : StartKeys.TrieFor w) :
    StartLocate.Tree (StartStep.Entry B C E) (w.length+1)→Prop
  | .leaf d e term => NodeSound A B C E w g whole (.leaf d e term)
  | .node d e l r => NodeSound A B C E w g whole (.node d e l r) ∧
      Sound A B C E w g whole l ∧ Sound A B C E w g whole r

theorem sound_root (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (g : Nat) (whole : StartKeys.TrieFor w)
    (t : StartLocate.Tree (StartStep.Entry B C E) (w.length+1)) (h : Sound A B C E w g whole t) :
    NodeSound A B C E w g whole t := by
  cases t with
  | leaf _ _ _ => exact h
  | node _ _ _ _ => exact h.1

theorem root_sound (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat)
    (whole t : StartKeys.TrieFor w)
    (hwhole : ∀a,a∈whole.leaves→StartKeys.ValidKey g (StartKeys.originalKey w a))
    (hg : t.Good (StartKeys.text w fallback)) (hn : t.leaves≠[])
    (hv : ∀a,a∈t.leaves→StartKeys.ValidKey g (StartKeys.originalKey w a))
    (p : Nat) (hp : p≤t.depth) (hcover : Covered w fallback whole t p)
    (beta : Fin B.stateCount)
    (hbeta : ∀b,b∈t.leaves→∀j,b.record=.target j→beta=B.run B.initial (slice w j.val (j.val+p)))
    (incoming : StartCuts.Row E) (hprev : Previous A B C E w fallback g whole t p incoming) :
    NodeSound A B C E w g whole
      (StartPass.go B C E (StartCuts.build B C E w) (Range.build B w) (Range.build C w) (Range.build E w)
        (StartSummary.build A C w (Range.build A w) (Range.build C w) t).1 p beta incoming).1 := by
  let s:=(StartSummary.build A C w (Range.build A w) (Range.build C w) t).1
  let out:=(StartPass.go B C E (StartCuts.build B C E w) (Range.build B w) (Range.build C w) (Range.build E w)
    s p beta incoming).1
  have hs : StartSummary.shape s=t := StartSummary.build_shape A C w _ _ t
  have he : out.payload=StartLocal.entry B C E w t p beta incoming (StartSummary.root s) := by
    rw [StartPass.go_payload,StartPass.makeEntry_shape,hs]
  have hd : out.depth=t.depth := (StartPass.go_depth B C E _ _ _ _ s p beta incoming).trans (congrArg BoundaryTrie.Tree.depth hs)
  change NodeSound A B C E w g whole out
  refine ⟨by rw [he,hd]; rfl,?_,?_⟩
  · rw [he]
    exact StartKeys.representative_bound w fallback t hg hn
  · intro j hj m hm hmd q
    obtain ⟨b,hb,ht⟩:=(go_target B C E _ _ _ _ s p beta incoming j).mp hj
    rw [hs] at hb
    rw [he] at hm ⊢
    rw [hd] at hmd
    exact (query_hits A B C E w fallback g whole t hg hv b hb j ht p m hm hmd hcover beta
      (hbeta b hb j ht) incoming hprev (StartSummary.root s)
      (StartSummary.build_root A C w fallback g t hg hn hv) q).trans
        (hits_words A B C E w fallback g whole hwhole b (hv b hb) j ht m m q)

theorem go_sound (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat)
    (whole t : StartKeys.TrieFor w)
    (hwhole : ∀a,a∈whole.leaves→StartKeys.ValidKey g (StartKeys.originalKey w a))
    (hg : t.Good (StartKeys.text w fallback)) (hn : t.leaves≠[])
    (hv : ∀a,a∈t.leaves→StartKeys.ValidKey g (StartKeys.originalKey w a))
    (p : Nat) (hp : p≤t.depth) (hcover : Covered w fallback whole t p)
    (beta : Fin B.stateCount)
    (hbeta : ∀b,b∈t.leaves→∀j,b.record=.target j→beta=B.run B.initial (slice w j.val (j.val+p)))
    (incoming : StartCuts.Row E) (hprev : Previous A B C E w fallback g whole t p incoming) :
    Sound A B C E w g whole
      (StartPass.go B C E (StartCuts.build B C E w) (Range.build B w) (Range.build C w) (Range.build E w)
        (StartSummary.build A C w (Range.build A w) (Range.build C w) t).1 p beta incoming).1 := by
  induction t generalizing p beta incoming with
  | empty => exact False.elim (hn rfl)
  | leaf key =>
    have hroot:=root_sound A B C E w fallback g whole (.leaf key) hwhole hg hn hv p hp hcover beta hbeta incoming hprev
    cases ht : key.record <;> simp only [StartSummary.build,ht,StartPass.go,Sound] at hroot ⊢ <;> exact hroot
  | node stem d l r ihl ihr =>
    have hpd : p≤d := hp
    let t:StartKeys.TrieFor w:=.node stem d l r
    let row:=StartSummary.root (StartSummary.build A C w (Range.build A w) (Range.build C w) t).1
    let e:=StartLocal.entry B C E w t p beta incoming row
    let bottom:=StartStep.advance B C E (StartCuts.build B C E w) (Range.build B w)
      (Range.build C w) (Range.build E w) e
    have hroot:=root_sound A B C E w fallback g whole t hwhole hg hn hv p hp hcover beta hbeta incoming hprev
    have hvl : ∀a,a∈l.leaves→StartKeys.ValidKey g (StartKeys.originalKey w a) :=
      fun a ha=>hv a (List.mem_append_left _ ha)
    have hvr : ∀a,a∈r.leaves→StartKeys.ValidKey g (StartKeys.originalKey w a) :=
      fun a ha=>hv a (List.mem_append_right _ ha)
    have hd:=BoundaryTrie.Tree.edge_depths (StartKeys.text w fallback) stem d l r hg
    have hrow : ∀q,row.get q=true ↔ StartSummary.Source A C w g t q :=
      StartSummary.build_root A C w fallback g t hg hn hv
    have hbound:=StartKeys.representative_bound w fallback t hg hn
    have hbottom (b : StartKeys.KeyFor w) (hb : b∈t.leaves) (j : Fin (w.length+1))
        (ht : b.record=.target j) (q : Fin E.stateCount) :
        bottom.states.get q=true ↔ Hits A B C E w fallback g whole b j d d q :=
      query_hits A B C E w fallback g whole t hg hv b hb j ht p d hp (Nat.le_refl _) hcover
        beta (hbeta b hb j ht) incoming hprev row hrow q
    have hbeta' (b : StartKeys.KeyFor w) (hb : b∈t.leaves) (j : Fin (w.length+1))
        (ht : b.record=.target j) : bottom.beta=B.run B.initial (slice w j.val (j.val+d)) := by
      rw [StartStep.advance_beta B C E w e hp hbound]
      change B.run beta (StartKeys.edgeWord w (StartKeys.representative w t).start p d)=_
      rw [StartLocal.target_segment w fallback g t hg b hb j (hv b hb) ht p d hp (Nat.le_refl _),
        hbeta b hb j ht,← DFA.run_append,← OuterColumn.slice_split w j.val (j.val+p) (j.val+d) (by omega) (by omega)]
    have hl:=ihl hg.1 hg.2.2.1 hvl d hd.1 (covered_left w fallback whole stem d l r p hg hp hcover)
      bottom.beta (fun b hb j ht=>hbeta' b (List.mem_append_left _ hb) j ht) bottom.states
      (Or.inr (fun b hb j ht q=>hbottom b (List.mem_append_left _ hb) j ht q))
    have hr:=ihr hg.2.1 hg.2.2.2.1 hvr d hd.2 (covered_right w fallback whole stem d l r p hg hp hcover)
      bottom.beta (fun b hb j ht=>hbeta' b (List.mem_append_right _ hb) j ht) bottom.states
      (Or.inr (fun b hb j ht q=>hbottom b (List.mem_append_right _ hb) j ht q))
    exact ⟨hroot,hl,hr⟩

end REWB.BoundaryApplication.StartSound
