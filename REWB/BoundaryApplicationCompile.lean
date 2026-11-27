import REWB.BoundaryApplicationKeys

/-! Compile the constructed reversed-prefix trie into executable mixed
source/target operations. Every edge color map is queried from one shared
forward-text DFA map index. Source leaves are silent; target leaves start
at the initial D color and initial E suffix state. -/
namespace REWB.BoundaryApplication
open REWB.BoundaryTrie
open REWB.Spec (slice)
variable {σ : Nat}

abbrev KeyFor (w : Word (Fin σ)) := Key (reversed w).size (Endpoint w.length)
abbrev TrieFor (w : Word (Fin σ)) := BoundaryTrie.Tree (reversed w).size (Endpoint w.length)

def height (n : Nat) : Nat := BoundaryIndex.Tree.heightFor (n+1)

def position {n : Nat} (p : Fin (n+1)) : BoundaryIndex.Merge.Position (height n) :=
  ⟨p.val,Nat.lt_of_lt_of_le p.isLt (BoundaryIndex.Tree.capacity (n+1))⟩

def representative (w : Word (Fin σ)) : TrieFor w→KeyFor w
  | .empty => ⟨0,0,by omega,.source 0⟩
  | .leaf a => a
  | .node a _ _ _ => a

theorem representative_mem (w : Word (Fin σ)) (fallback : Fin σ) (t : TrieFor w)
    (hg : t.Good (reverseText w fallback)) (hn : t.leaves≠[]) :
    representative w t∈t.leaves := by
  cases t with
  | empty => exact False.elim (hn rfl)
  | leaf a => simp only [representative,BoundaryTrie.Tree.leaves,List.mem_singleton]
  | node a d l r => exact List.mem_append_left _ hg.2.2.2.2.1

theorem representative_common (w : Word (Fin σ)) (fallback : Fin σ) (t : TrieFor w)
    (hg : t.Good (reverseText w fallback)) (a : KeyFor w) (ha : a∈t.leaves) :
    Key.Common (reverseText w fallback) (representative w t) a t.depth := by
  cases t with
  | empty => cases ha
  | leaf b =>
    simp only [BoundaryTrie.Tree.leaves,List.mem_singleton] at ha
    subst a
    exact ⟨Nat.le_refl _,Nat.le_refl _,rfl⟩
  | node b d l r => exact hg.2.2.2.2.2.1 a ha

def edge (D : DFA (Fin σ)) (w : Word (Fin σ)) (idx : Range.Index D)
    (parent : Nat) (child : TrieFor w) : Range.Result D.stateCount :=
  Range.query D idx (idx.length-(representative w child).start-child.depth)
    (idx.length-(representative w child).start-parent)

def color (D : DFA (Fin σ)) (w : Word (Fin σ)) (g : Nat) (t : Fin (w.length+1)) (d : Nat) :
    Fin D.stateCount := D.run D.initial (slice w g (t.val-d))

theorem edge_color (D : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g parent : Nat) (child : TrieFor w) (a : KeyFor w) (t : Fin (w.length+1))
    (hg : child.Good (reverseText w fallback)) (ha : a∈child.leaves)
    (hv : ValidKey g (originalKey w a)) (ht : a.record=.target t)
    (hp : parent≤child.depth) :
    (edge D w (Range.build D w) parent child).map.get (color D w g t child.depth)=
      color D w g t parent := by
  have hc:=representative_common w fallback child hg a ha
  have hedge:=target_edge w fallback g (representative w child) a t hv ht parent child.depth hp hc
  simp only [ValidKey,originalKey] at hv
  rw [ht] at hv
  have htc : child.depth≤t.val-g := by have hh:=hc.2.1; rw [hv.2.2] at hh; exact hh
  have htbound : t.val≤w.length := by have hh:=t.isLt; omega
  simp only [edge,Range.build_length]
  rw [Range.query_correct D w _ _ (by omega) (by omega)]
  change D.run (color D w g t child.depth) (edgeWord w (representative w child).start parent child.depth)=_
  rw [hedge]
  unfold color
  rw [← DFA.run_append,← OuterColumn.slice_split w g (t.val-child.depth) (t.val-parent)
    (by have hh:=hv.1; omega) (by omega)]

theorem leaf_color (D : DFA (Fin σ)) (w : Word (Fin σ)) (g : Nat)
    (a : KeyFor w) (t : Fin (w.length+1))
    (hv : ValidKey g (originalKey w a)) (ht : a.record=.target t) :
    color D w g t a.length=D.initial := by
  simp only [ValidKey,originalKey] at hv
  rw [ht] at hv
  unfold color
  rw [hv.2.2,show t.val-(t.val-g)=g by have hh:=hv.1; omega]
  simp only [slice,Nat.sub_self,List.take_zero,DFA.run]

def compile (D E : DFA (Fin σ)) (w : Word (Fin σ)) (idx : Range.Index D) :
    TrieFor w→BoundaryIndex.Mixed.Program D.stateCount E.stateCount (height w.length)×Nat
  | .empty => (.source (position (0 : Fin (w.length+1))),1)
  | .leaf a =>
    match a.record with
    | .source p => (.source (position p),2)
    | .target p => (.target (position p) D.initial E.initial,3)
  | .node _ d l r =>
    let a:=compile D E w idx l
    let b:=compile D E w idx r
    let el:=edge D w idx d l
    let er:=edge D w idx d r
    (.node el.map er.map a.1 b.1,a.2+b.2+el.work+er.work+5)

def Target (D E : DFA (Fin σ)) (w : Word (Fin σ)) (g : Nat) (trie : TrieFor w)
    (i : BoundaryIndex.Merge.Position (height w.length)) (c : Fin D.stateCount)
    (q : Fin E.stateCount) : Prop :=
  ∃a,a∈trie.leaves ∧ ∃t,a.record=.target t ∧ i=position t ∧
    c=color D w g t trie.depth ∧ q=E.initial

theorem compile_active (D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g : Nat) (trie : TrieFor w) (hg : trie.Good (reverseText w fallback))
    (hn : trie.leaves≠[]) (hv : ∀a,a∈trie.leaves→ValidKey g (originalKey w a))
    (i : BoundaryIndex.Merge.Position (height w.length)) (c : Fin D.stateCount)
    (q : Fin E.stateCount) :
    BoundaryIndex.Mixed.Active (compile D E w (Range.build D w) trie).1 i c q ↔
      Target D E w g trie i c q := by
  induction trie generalizing c with
  | empty => exact False.elim (hn rfl)
  | leaf a =>
    have hva:=hv a (by simp only [BoundaryTrie.Tree.leaves,List.mem_singleton])
    cases hr : a.record with
    | source p =>
      simp only [compile,hr,BoundaryIndex.Mixed.Active,Target,BoundaryTrie.Tree.leaves,
        List.mem_singleton,exists_eq_left,Endpoint.noConfusion,reduceCtorEq,false_and,exists_false]
    | target p =>
      have hc:=leaf_color D w g a p hva hr
      simp only [compile,hr,BoundaryIndex.Mixed.Active,Target,BoundaryTrie.Tree.leaves,
        BoundaryTrie.Tree.depth,List.mem_singleton,exists_eq_left,Endpoint.target.injEq,
        exists_eq_left',hc]
  | node stem d l r ihl ihr =>
    have hvl : ∀a,a∈l.leaves→ValidKey g (originalKey w a) :=
      fun a ha=>hv a (List.mem_append_left _ ha)
    have hvr : ∀a,a∈r.leaves→ValidKey g (originalKey w a) :=
      fun a ha=>hv a (List.mem_append_right _ ha)
    have hdepth:=BoundaryTrie.Tree.edge_depths (reverseText w fallback) stem d l r hg
    change ((∃old,(edge D w (Range.build D w) d l).map.get old=c ∧
        BoundaryIndex.Mixed.Active (compile D E w (Range.build D w) l).1 i old q) ∨
      (∃old,(edge D w (Range.build D w) d r).map.get old=c ∧
        BoundaryIndex.Mixed.Active (compile D E w (Range.build D w) r).1 i old q)) ↔ _
    constructor
    · rintro (⟨old,he,ha⟩ | ⟨old,he,ha⟩)
      · obtain ⟨a,ham,t,ht,hi,hc,hq⟩:=(ihl hg.1 hg.2.2.1 hvl old).mp ha
        refine ⟨a,List.mem_append_left _ ham,t,ht,hi,?_,hq⟩
        change c=color D w g t d
        rw [← he,hc]
        exact edge_color D w fallback g d l a t hg.1 ham (hvl a ham) ht hdepth.1
      · obtain ⟨a,ham,t,ht,hi,hc,hq⟩:=(ihr hg.2.1 hg.2.2.2.1 hvr old).mp ha
        refine ⟨a,List.mem_append_right _ ham,t,ht,hi,?_,hq⟩
        change c=color D w g t d
        rw [← he,hc]
        exact edge_color D w fallback g d r a t hg.2.1 ham (hvr a ham) ht hdepth.2
    · rintro ⟨a,ha,t,ht,hi,hc,hq⟩
      change c=color D w g t d at hc
      rcases List.mem_append.mp ha with hal | har
      · left
        refine ⟨color D w g t l.depth,?_,(ihl hg.1 hg.2.2.1 hvl _).mpr ?_⟩
        · rw [edge_color D w fallback g d l a t hg.1 hal (hvl a hal) ht hdepth.1,← hc]
        · exact ⟨a,hal,t,ht,hi,rfl,hq⟩
      · right
        refine ⟨color D w g t r.depth,?_,(ihr hg.2.1 hg.2.2.2.1 hvr _).mpr ?_⟩
        · rw [edge_color D w fallback g d r a t hg.2.1 har (hvr a har) ht hdepth.2,← hc]
        · exact ⟨a,har,t,ht,hi,rfl,hq⟩

theorem compile_mass (D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (idx : Range.Index D) (trie : TrieFor w)
    (hg : trie.Good (reverseText w fallback)) (hn : trie.leaves≠[]) :
    MaskedEventBudget.size (BoundaryIndex.Mixed.shape (compile D E w idx trie).1)=trie.leaves.length := by
  induction trie with
  | empty => exact False.elim (hn rfl)
  | leaf a => cases hr : a.record <;> simp only [compile,hr,BoundaryIndex.Mixed.shape,
      MaskedEventBudget.size,BoundaryTrie.Tree.leaves,List.length_cons,List.length_nil]
  | node stem d l r ihl ihr =>
    simp only [compile,BoundaryIndex.Mixed.shape,MaskedEventBudget.size,
      BoundaryTrie.Tree.leaves,List.length_append,ihl hg.1 hg.2.2.1,ihr hg.2.1 hg.2.2.2.1]

theorem edge_work (D : DFA (Fin σ)) (w : Word (Fin σ)) (parent : Nat) (child : TrieFor w)
    (hp : parent≤child.depth) :
    (edge D w (Range.build D w) parent child).work≤D.stateCount+8*(w.length.log2+2)+1 := by
  simp only [edge,Range.build_length]
  exact Range.query_work D w _ _ (by omega) (by omega)

theorem compile_work (D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (trie : TrieFor w) (hg : trie.Good (reverseText w fallback)) (hn : trie.leaves≠[]) :
    (compile D E w (Range.build D w) trie).2≤
      trie.nodes*(2*(D.stateCount+8*(w.length.log2+2)+1)+5) := by
  induction trie with
  | empty => exact False.elim (hn rfl)
  | leaf a =>
    cases hr : a.record <;> simp only [compile,hr,BoundaryTrie.Tree.nodes,Nat.one_mul] <;> omega
  | node stem d l r ihl ihr =>
    have hl:=ihl hg.1 hg.2.2.1
    have hr:=ihr hg.2.1 hg.2.2.2.1
    have hd:=BoundaryTrie.Tree.edge_depths (reverseText w fallback) stem d l r hg
    have he₁:=edge_work D w d l hd.1
    have he₂:=edge_work D w d r hd.2
    simp only [compile,BoundaryTrie.Tree.nodes,Nat.add_mul,Nat.one_mul]
    omega

end REWB.BoundaryApplication
