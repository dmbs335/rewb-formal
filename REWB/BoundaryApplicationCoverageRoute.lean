import REWB.BoundaryApplicationCoverageImport

/-! Coverage along the source route selected by the actual direct
address table. The induction separates a heavy descent, which retains
the imported light targets, from a light descent, whose parent is an
explicit query entry. -/
namespace REWB.BoundaryApplication.Coverage
open REWB.BoundaryIndex
open REWB.BoundaryIndex.Merge
variable {σ : Nat}

theorem route_source {A D E : DFA (Fin σ)} {n : Nat} (p : Fin (n+1))
    (t : Heavy.Saved A D E n) (es : List (Heavy.Entry A D E n))
    (hr : Address.SourceRoute p t es) : Address.HasSource p t := by
  induction hr with
  | leaf _ _ he => exact he
  | left _ _ _ _ _ _ ih => exact Or.inl ih
  | right _ _ _ _ _ _ ih => exact Or.inr ih

theorem saved_route_source (A B D E : DFA (Fin σ)) (w : Word (Fin σ))
    (base : BoundaryIndex.Tree (Subset.count A) E.stateCount (height w.length))
    (normalBase : BoundaryIndex.Tree D.stateCount E.stateCount (height w.length))
    (t : TrieFor w) (incoming : Merge.State (Subset.count A) E.stateCount (height w.length))
    (source : Fin (w.length+1)) (es : List (Heavy.Entry A D E w.length))
    (hr : Address.SourceRoute source (saved A B D E w base normalBase t incoming) es) :
    ∃a,a∈t.leaves ∧ a.record=.source source :=
  (Address.go_source A B D E w _ _ base t _ incoming source).mp (route_source source _ es hr)

theorem cross_targets_right (A B D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g : Nat) (stem : KeyFor w) (d : Nat) (l r : TrieFor w)
    (hg : (BoundaryTrie.Tree.node stem d l r).Good (reverseText w fallback))
    (hv : ∀a,a∈(l.leaves++r.leaves)→ValidKey g (originalKey w a))
    (a : KeyFor w) (source : Fin (w.length+1)) (ha : a∈l.leaves) (hs : a.record=.source source)
    (right : Nat) :
    Targets A B D E w g source right r ↔ Within A B D E w g source right d r := by
  constructor
  · rintro ⟨b,hb,target,ht,hr,hE,L,hcut⟩
    refine ⟨b,hb,target,ht,hr,hE,L,?_,hcut⟩
    exact lca_cut_bound A B D w fallback g (.node stem d l r) hg a b source target d L
      (hv a (List.mem_append_left _ ha)) hs (hv b (List.mem_append_right _ hb)) ht (.cross ha hb) hcut
  · exact within_targets A B D E w g source right d r

theorem cross_targets_left (A B D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g : Nat) (stem : KeyFor w) (d : Nat) (l r : TrieFor w)
    (hg : (BoundaryTrie.Tree.node stem d l r).Good (reverseText w fallback))
    (hv : ∀a,a∈(l.leaves++r.leaves)→ValidKey g (originalKey w a))
    (a : KeyFor w) (source : Fin (w.length+1)) (ha : a∈r.leaves) (hs : a.record=.source source)
    (right : Nat) :
    Targets A B D E w g source right l ↔ Within A B D E w g source right d l := by
  constructor
  · rintro ⟨b,hb,target,ht,hr,hE,L,hcut⟩
    refine ⟨b,hb,target,ht,hr,hE,L,?_,hcut⟩
    exact lca_cut_bound A B D w fallback g (.node stem d l r) hg a b source target d L
      (hv a (List.mem_append_right _ ha)) hs (hv b (List.mem_append_left _ hb)) ht (.crossRev ha hb) hcut
  · exact within_targets A B D E w g source right d l

def Hits (A D E : DFA (Fin σ)) (w : Word (Fin σ)) (source : Fin (w.length+1))
    (right : Nat) (es : List (Heavy.Entry A D E w.length)) : Prop :=
  ∃e,e∈es ∧ HeavyIndex.LocalEntry A D E w source right e

theorem hits_append (A D E : DFA (Fin σ)) (w : Word (Fin σ)) (source : Fin (w.length+1))
    (right : Nat) (es : List (Heavy.Entry A D E w.length)) (e : Heavy.Entry A D E w.length) :
    Hits A D E w source right (es++[e]) ↔ Hits A D E w source right es ∨ HeavyIndex.LocalEntry A D E w source right e := by
  simp only [Hits,List.mem_append,List.mem_singleton]
  constructor
  · rintro ⟨v,hv|hv,h⟩
    · exact Or.inl ⟨v,hv,h⟩
    · exact Or.inr (hv ▸ h)
  · rintro (⟨v,hv,h⟩|h)
    · exact ⟨v,Or.inl hv,h⟩
    · exact ⟨e,Or.inr rfl,h⟩

theorem saved_node_false (A B D E : DFA (Fin σ)) (w : Word (Fin σ))
    (base : BoundaryIndex.Tree (Subset.count A) E.stateCount (height w.length))
    (normalBase : BoundaryIndex.Tree D.stateCount E.stateCount (height w.length))
    (stem : KeyFor w) (d : Nat) (l r : TrieFor w)
    (incoming : Merge.State (Subset.count A) E.stateCount (height w.length))
    (hb : Heavy.heavyRight (snapshot D E w normalBase (.node stem d l r))=false) :
    saved A B D E w base normalBase (.node stem d l r) incoming =
      .node (Heavy.root (saved A B D E w base normalBase (.node stem d l r) incoming)) false
        (saved A B D E w base normalBase l
          (Heavy.advance A E w (Range.build A w) d l
            (Heavy.root (saved A B D E w base normalBase (.node stem d l r) incoming)).subsets).1)
        (saved A B D E w base normalBase r (Heavy.blank base)) := by
  simp only [saved,Heavy.go,hb,Bool.false_eq_true,if_false,Heavy.root]
  rfl

theorem saved_node_true (A B D E : DFA (Fin σ)) (w : Word (Fin σ))
    (base : BoundaryIndex.Tree (Subset.count A) E.stateCount (height w.length))
    (normalBase : BoundaryIndex.Tree D.stateCount E.stateCount (height w.length))
    (stem : KeyFor w) (d : Nat) (l r : TrieFor w)
    (incoming : Merge.State (Subset.count A) E.stateCount (height w.length))
    (hb : Heavy.heavyRight (snapshot D E w normalBase (.node stem d l r))=true) :
    saved A B D E w base normalBase (.node stem d l r) incoming =
      .node (Heavy.root (saved A B D E w base normalBase (.node stem d l r) incoming)) true
        (saved A B D E w base normalBase l (Heavy.blank base))
        (saved A B D E w base normalBase r
          (Heavy.advance A E w (Range.build A w) d r
            (Heavy.root (saved A B D E w base normalBase (.node stem d l r) incoming)).subsets).1) := by
  simp only [saved,Heavy.go,hb,if_true,Heavy.root]
  rfl

/-- Every source route selected by the concrete address construction is
complete. Its accumulated incoming state covers earlier heavy ancestors;
its own target predicate covers all descendants, including zero-length
refinement edges and empty repeated words. -/
theorem route_iff (A B D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat)
    (base : BoundaryIndex.Tree (Subset.count A) E.stateCount (height w.length))
    (hbb : MergeSchedule.Blank base)
    (normalBase : BoundaryIndex.Tree D.stateCount E.stateCount (height w.length))
    (hng : Tree.Good normalBase) (hnb : MergeSchedule.Blank normalBase)
    (t : TrieFor w) (hg : t.Good (reverseText w fallback)) (hn : t.leaves≠[])
    (hv : ∀a,a∈t.leaves→ValidKey g (originalKey w a))
    (incoming : Merge.State (Subset.count A) E.stateCount (height w.length))
    (source : Fin (w.length+1)) (right : Nat) (es : List (Heavy.Entry A D E w.length))
    (hr : Address.SourceRoute source (saved A B D E w base normalBase t incoming) es) :
    Hits A D E w source right es ↔
      Incoming A E w t.depth incoming source right ∨ Targets A B D E w g source right t := by
  induction t generalizing incoming es with
  | empty => exact False.elim (hn rfl)
  | leaf key =>
    obtain ⟨a,ha,hs⟩:=saved_route_source A B D E w base normalBase (.leaf key) incoming source es hr
    have hak : a=key := List.mem_singleton.mp ha
    subst a
    have ht : ¬Targets A B D E w g source right (.leaf key) := by
      rintro ⟨b,hb,target,hbt,_⟩
      have hbk : b=key := List.mem_singleton.mp hb
      subst b
      rw [hs] at hbt
      cases hbt
    have hwithin : ¬Within A B D E w g source right key.length (.leaf key) :=
      fun h=>ht (within_targets A B D E w g source right key.length (.leaf key) h)
    have hlocal:=root_local_iff A B D E w fallback g base normalBase hng hnb (.leaf key) hg hn hv
      key source (List.mem_singleton_self _) hs incoming right
    change Address.SourceRoute source (.leaf (Heavy.root (saved A B D E w base normalBase (.leaf key) incoming))
      (some key.record)) es at hr
    cases hr
    simpa only [Hits,List.mem_singleton,exists_eq_left,BoundaryTrie.Tree.depth,hwithin,ht,or_false] using hlocal
  | node stem d l r ihl ihr =>
    have hlv : ∀a,a∈l.leaves→ValidKey g (originalKey w a) :=
      fun a ha=>hv a (List.mem_append_left _ ha)
    have hrv : ∀a,a∈r.leaves→ValidKey g (originalKey w a) :=
      fun a ha=>hv a (List.mem_append_right _ ha)
    have hd:=BoundaryTrie.Tree.edge_depths (reverseText w fallback) stem d l r hg
    cases hb : Heavy.heavyRight (snapshot D E w normalBase (.node stem d l r)) with
    | false =>
      rw [saved_node_false A B D E w base normalBase stem d l r incoming hb] at hr
      cases hr with
      | left _ _ _ _ cs hc =>
        simp only [Bool.false_eq_true,if_false,if_true]
        obtain ⟨a,ha,hs⟩:=saved_route_source A B D E w base normalBase l _ source cs hc
        have hh:=ihl (hg:=hg.1) (hn:=hg.2.2.1) (hv:=hlv) (incoming:=_) (es:=cs) hc
        have hroot:=root_incoming_iff A B D E w fallback g base normalBase hng hnb (.node stem d l r) hg hn hv
          a source (List.mem_append_left _ ha) hs incoming right
        simp only [BoundaryTrie.Tree.depth] at hroot
        rw [hh,incoming_advance A E w fallback g d l a source hg.1 ha (hlv a ha) hs hd.1,hroot]
        simp only [lightTrie,hb,Bool.false_eq_true,if_false]
        rw [←cross_targets_right A B D E w fallback g stem d l r hg hv a source ha hs right,
          targets_node]
        constructor
        · rintro ((hi | hr) | hl)
          · exact Or.inl hi
          · exact Or.inr (Or.inr hr)
          · exact Or.inr (Or.inl hl)
        · rintro (hi | hl | hr)
          · exact Or.inl (Or.inl hi)
          · exact Or.inr hl
          · exact Or.inl (Or.inr hr)
      | right _ _ _ _ cs hc =>
        simp only [Bool.false_eq_true,if_false,if_true]
        obtain ⟨a,ha,hs⟩:=saved_route_source A B D E w base normalBase r _ source cs hc
        have hh:=ihr (hg:=hg.2.1) (hn:=hg.2.2.2.1) (hv:=hrv) (incoming:=Heavy.blank base) (es:=cs) hc
        rw [hits_append,hh]
        simp only [incoming_blank A E w base hbb,false_or]
        rw [root_local_iff A B D E w fallback g base normalBase hng hnb (.node stem d l r) hg hn hv
          a source (List.mem_append_right _ ha) hs,targets_node]
        constructor
        · rintro (hr | hi | hw)
          · exact Or.inr (Or.inr hr)
          · exact Or.inl hi
          · exact Or.inr ((targets_node A B D E w g source right stem d l r).mp
              (within_targets A B D E w g source right d (.node stem d l r) hw))
        · rintro (hi | hl | hr)
          · exact Or.inr (Or.inl hi)
          · exact Or.inr (Or.inr (within_embed A B D E w g source right d l (.node stem d l r)
              (fun b hb=>List.mem_append_left _ hb)
              ((cross_targets_left A B D E w fallback g stem d l r hg hv a source ha hs right).mp hl)))
          · exact Or.inl hr
    | true =>
      rw [saved_node_true A B D E w base normalBase stem d l r incoming hb] at hr
      cases hr with
      | left _ _ _ _ cs hc =>
        simp only [Bool.false_eq_true,if_false,if_true]
        obtain ⟨a,ha,hs⟩:=saved_route_source A B D E w base normalBase l _ source cs hc
        have hh:=ihl (hg:=hg.1) (hn:=hg.2.2.1) (hv:=hlv) (incoming:=Heavy.blank base) (es:=cs) hc
        rw [hits_append,hh]
        simp only [incoming_blank A E w base hbb,false_or]
        rw [root_local_iff A B D E w fallback g base normalBase hng hnb (.node stem d l r) hg hn hv
          a source (List.mem_append_left _ ha) hs,targets_node]
        constructor
        · rintro (hl | hi | hw)
          · exact Or.inr (Or.inl hl)
          · exact Or.inl hi
          · exact Or.inr ((targets_node A B D E w g source right stem d l r).mp
              (within_targets A B D E w g source right d (.node stem d l r) hw))
        · rintro (hi | hl | hr)
          · exact Or.inr (Or.inl hi)
          · exact Or.inl hl
          · exact Or.inr (Or.inr (within_embed A B D E w g source right d r (.node stem d l r)
              (fun b hb=>List.mem_append_right _ hb)
              ((cross_targets_right A B D E w fallback g stem d l r hg hv a source ha hs right).mp hr)))
      | right _ _ _ _ cs hc =>
        simp only [Bool.false_eq_true,if_false,if_true]
        obtain ⟨a,ha,hs⟩:=saved_route_source A B D E w base normalBase r _ source cs hc
        have hh:=ihr (hg:=hg.2.1) (hn:=hg.2.2.2.1) (hv:=hrv) (incoming:=_) (es:=cs) hc
        have hroot:=root_incoming_iff A B D E w fallback g base normalBase hng hnb (.node stem d l r) hg hn hv
          a source (List.mem_append_right _ ha) hs incoming right
        simp only [BoundaryTrie.Tree.depth] at hroot
        rw [hh,incoming_advance A E w fallback g d r a source hg.2.1 ha (hrv a ha) hs hd.2,hroot]
        simp only [lightTrie,hb,if_true]
        rw [←cross_targets_left A B D E w fallback g stem d l r hg hv a source ha hs right,
          targets_node]
        constructor
        · rintro ((hi | hl) | hr)
          · exact Or.inl hi
          · exact Or.inr (Or.inl hl)
          · exact Or.inr (Or.inr hr)
        · rintro (hi | hl | hr)
          · exact Or.inl (Or.inl hi)
          · exact Or.inl (Or.inr hl)
          · exact Or.inr hr

end REWB.BoundaryApplication.Coverage
