import REWB.BoundaryApplicationSeparatedKeys

/-! Source A colors for separated boundaries. Every source terminal is
filtered by one actual C range query and starts with A.initial. Shared
forward edge maps push the finite color subsets toward the root; OR
coalescence handles noninjective maps without rescanning source leaves. -/
namespace REWB.BoundaryApplication.Separated.Summary
open REWB.BoundaryTrie
open REWB.BoundaryIndex
open REWB.Spec (slice)
variable {σ : Nat}

def build (A C : DFA (Fin σ)) (w : Word (Fin σ)) (g0 : Nat) (aranges : Range.Index A)
    (cranges : Range.Index C) : TrieFor w→StartSummary.Saved A.stateCount (reversed w).size (Endpoint w.length)×Nat
  | .empty => (.empty,1)
  | .leaf a =>
    match a.record with
    | .source p =>
      let check:=Range.query C cranges p.val g0
      let row:=Vector.ofFn (fun q=>C.final (check.map.get C.initial) && decide (q=A.initial))
      (.leaf a row,check.work+A.stateCount+3)
    | .target _ => (.leaf a (Vector.ofFn (fun _=>false)),A.stateCount+2)
  | .node a d l r =>
    let left:=build A C w g0 aranges cranges l
    let right:=build A C w g0 aranges cranges r
    let el:=edge A w aranges d l
    let er:=edge A w aranges d r
    let vl:=StartStep.image (StartSummary.root left.1) el.map
    let vr:=StartStep.image (StartSummary.root right.1) er.map
    let row:=Vector.ofFn (fun q=>vl.1.get q || vr.1.get q)
    (.node a d row left.1 right.1,left.2+right.2+el.work+er.work+vl.2+vr.2+A.stateCount+5)

theorem build_shape (A C : DFA (Fin σ)) (w : Word (Fin σ)) (g0 : Nat) (aranges : Range.Index A)
    (cranges : Range.Index C) (t : TrieFor w) : StartSummary.shape (build A C w g0 aranges cranges t).1=t := by
  induction t with
  | empty => rfl
  | leaf a => cases ht : a.record <;> simp only [build,ht,StartSummary.shape]
  | node a d l r ihl ihr => simp only [build,StartSummary.shape,ihl,ihr]

def Source (A C : DFA (Fin σ)) (w : Word (Fin σ)) (g0 : Nat) (t : TrieFor w)
    (q : Fin A.stateCount) : Prop :=
  ∃a,a∈t.leaves ∧ ∃p,a.record=.source p ∧ C.accepts (slice w p.val g0) ∧
    q=Coverage.alpha A w p.val t.depth

theorem build_root (A C : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (g0 g1 : Nat)
    (h0 : g0≤w.length) (t : TrieFor w) (hg : t.Good (reverseText w fallback)) (hn : t.leaves≠[])
    (hv : ∀a,a∈t.leaves→ValidKey g1 (originalKey w a))
    (hsource : ∀a,a∈t.leaves→∀p,a.record=.source p→p.val≤g0) (q : Fin A.stateCount) :
    (StartSummary.root (build A C w g0 (Range.build A w) (Range.build C w) t).1).get q=true ↔ Source A C w g0 t q := by
  induction t generalizing q with
  | empty => exact False.elim (hn rfl)
  | leaf a =>
    have ha : a∈(BoundaryTrie.Tree.leaf a).leaves := by simp only [BoundaryTrie.Tree.leaves,List.mem_singleton]
    cases ht : a.record with
    | source p =>
      have hd:=Coverage.source_data w g1 a p (hv a ha) ht
      have hp:=hsource a ha p ht
      simp only [build,ht,StartSummary.root,Table.get_ofFn,Range.query_correct C w p.val g0 hp h0,
        Source,BoundaryTrie.Tree.leaves,BoundaryTrie.Tree.depth,List.mem_singleton,exists_eq_left,
        Endpoint.source.injEq,exists_eq_left',Coverage.alpha,hd.2.2,Nat.sub_self,slice,List.take_zero,DFA.run,
        Bool.and_eq_true,decide_eq_true_eq,DFA.accepts]
    | target p =>
      simp only [build,ht,StartSummary.root,Table.get_ofFn,Source,BoundaryTrie.Tree.leaves,
        List.mem_singleton,exists_eq_left,Endpoint.noConfusion,reduceCtorEq,false_and,exists_false]
  | node stem d l r ihl ihr =>
    have hvl : ∀a,a∈l.leaves→ValidKey g1 (originalKey w a) := fun a ha=>hv a (List.mem_append_left _ ha)
    have hvr : ∀a,a∈r.leaves→ValidKey g1 (originalKey w a) := fun a ha=>hv a (List.mem_append_right _ ha)
    have hsl : ∀a,a∈l.leaves→∀p,a.record=.source p→p.val≤g0 := fun a ha=>hsource a (List.mem_append_left _ ha)
    have hsr : ∀a,a∈r.leaves→∀p,a.record=.source p→p.val≤g0 := fun a ha=>hsource a (List.mem_append_right _ ha)
    have hd:=BoundaryTrie.Tree.edge_depths (reverseText w fallback) stem d l r hg
    change ((Vector.ofFn fun q=>
      (StartStep.image (StartSummary.root (build A C w g0 (Range.build A w) (Range.build C w) l).1)
        (edge A w (Range.build A w) d l).map).1.get q ||
      (StartStep.image (StartSummary.root (build A C w g0 (Range.build A w) (Range.build C w) r).1)
        (edge A w (Range.build A w) d r).map).1.get q).get q=true) ↔ _
    simp only [Table.get_ofFn,Bool.or_eq_true,StartStep.image_get,
      ihl hg.1 hg.2.2.1 hvl hsl,ihr hg.2.1 hg.2.2.2.1 hvr hsr]
    constructor
    · rintro (⟨old,⟨a,ha,p,ht,hC,ho⟩,he⟩ | ⟨old,⟨a,ha,p,ht,hC,ho⟩,he⟩)
      · refine ⟨a,List.mem_append_left _ ha,p,ht,hC,?_⟩
        rw [ho,Coverage.source_edge A w fallback g1 d l a p hg.1 ha (hvl a ha) ht hd.1] at he
        exact he.symm
      · refine ⟨a,List.mem_append_right _ ha,p,ht,hC,?_⟩
        rw [ho,Coverage.source_edge A w fallback g1 d r a p hg.2.1 ha (hvr a ha) ht hd.2] at he
        exact he.symm
    · rintro ⟨a,ha,p,ht,hC,hq⟩
      rcases List.mem_append.mp ha with hal | har
      · exact Or.inl ⟨Coverage.alpha A w p.val l.depth,⟨a,hal,p,ht,hC,rfl⟩,
          (Coverage.source_edge A w fallback g1 d l a p hg.1 hal (hvl a hal) ht hd.1).trans hq.symm⟩
      · exact Or.inr ⟨Coverage.alpha A w p.val r.depth,⟨a,har,p,ht,hC,rfl⟩,
          (Coverage.source_edge A w fallback g1 d r a p hg.2.1 har (hvr a har) ht hd.2).trans hq.symm⟩

def budget (A C : DFA (Fin σ)) (n : Nat) : Nat :=
  2*(A.stateCount+8*(n.log2+2)+1)+2*(A.stateCount*(A.stateCount+1))+
    (C.stateCount+8*(n.log2+2)+1)+A.stateCount+6

theorem build_work (A C : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (g0 : Nat)
    (h0 : g0≤w.length) (t : TrieFor w) (hg : t.Good (reverseText w fallback)) (hn : t.leaves≠[])
    (hsource : ∀a,a∈t.leaves→∀p,a.record=.source p→p.val≤g0) :
    (build A C w g0 (Range.build A w) (Range.build C w) t).2≤t.nodes*budget A C w.length := by
  induction t with
  | empty => exact False.elim (hn rfl)
  | leaf a =>
    cases ht : a.record with
    | source p =>
      have hp:=hsource a (by simp only [BoundaryTrie.Tree.leaves,List.mem_singleton]) p ht
      have hh:=Range.query_work C w p.val g0 hp h0
      simp only [build,ht,BoundaryTrie.Tree.nodes,Nat.one_mul,budget]
      omega
    | target p => simp only [build,ht,BoundaryTrie.Tree.nodes,Nat.one_mul,budget]; omega
  | node stem d l r ihl ihr =>
    have hl:=ihl hg.1 hg.2.2.1 (fun a ha=>hsource a (List.mem_append_left _ ha))
    have hr:=ihr hg.2.1 hg.2.2.2.1 (fun a ha=>hsource a (List.mem_append_right _ ha))
    have hd:=BoundaryTrie.Tree.edge_depths (reverseText w fallback) stem d l r hg
    have he₁:=edge_work A w d l hd.1
    have he₂:=edge_work A w d r hd.2
    simp only [build,StartStep.image_steps,BoundaryTrie.Tree.nodes,Nat.add_mul,Nat.one_mul]
    unfold budget at *
    omega

end REWB.BoundaryApplication.Separated.Summary
