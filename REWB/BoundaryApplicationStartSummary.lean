import REWB.BoundaryApplicationStartKeys

/-! One bottom-up pass stores the exact C continuation condition at
every actual forward-trie node. A source contributes only when its
actual A-prefix query accepts. Its C row is pulled through each shared
range edge and OR-coalesced with the sibling row. No source list is
rescanned and no transition is inverted. -/
namespace REWB.BoundaryApplication.StartSummary
open REWB.BoundaryTrie
open REWB.BoundaryIndex
open REWB.Spec (slice)
open StartKeys
variable {σ k n : Nat} {ρ : Type}

inductive Saved (k n : Nat) (ρ : Type) where
  | empty : Saved k n ρ
  | leaf : Key n ρ→Vector Bool k→Saved k n ρ
  | node : Key n ρ→Nat→Vector Bool k→Saved k n ρ→Saved k n ρ→Saved k n ρ

def root : Saved k n ρ→Vector Bool k
  | .empty => Vector.ofFn (fun _=>false)
  | .leaf _ row => row
  | .node _ _ row _ _ => row

def shape : Saved k n ρ→BoundaryTrie.Tree n ρ
  | .empty => .empty
  | .leaf key _ => .leaf key
  | .node key d _ l r => .node key d (shape l) (shape r)

def build (A C : DFA (Fin σ)) (w : Word (Fin σ)) (aranges : Range.Index A) (cranges : Range.Index C) :
    StartKeys.TrieFor w→Saved C.stateCount w.toArray.size (Endpoint w.length)×Nat
  | .empty => (.empty,1)
  | .leaf key =>
    match key.record with
    | .source p =>
      let pre:=Range.query A aranges 0 p.val
      let row:=Vector.ofFn (fun q=>A.final (pre.map.get A.initial) && C.final q)
      (.leaf key row,pre.work+C.stateCount+4)
    | .target _ => (.leaf key (Vector.ofFn (fun _=>false)),C.stateCount+2)
  | .node key d l r =>
    let a:=build A C w aranges cranges l
    let b:=build A C w aranges cranges r
    let el:=StartKeys.edge C w cranges d l
    let er:=StartKeys.edge C w cranges d r
    let row:=Vector.ofFn (fun q=>(root a.1).get (el.map.get q) || (root b.1).get (er.map.get q))
    (.node key d row a.1 b.1,a.2+b.2+el.work+er.work+C.stateCount+5)

theorem build_shape (A C : DFA (Fin σ)) (w : Word (Fin σ)) (aranges : Range.Index A)
    (cranges : Range.Index C) (t : StartKeys.TrieFor w) :
    shape (build A C w aranges cranges t).1=t := by
  induction t with
  | empty => rfl
  | leaf key => cases hr : key.record <;> simp only [build,hr,shape]
  | node key d l r ihl ihr => simp only [build,shape,ihl,ihr]

def Source (A C : DFA (Fin σ)) (w : Word (Fin σ)) (g : Nat) (t : StartKeys.TrieFor w)
    (q : Fin C.stateCount) : Prop :=
  ∃a,a∈t.leaves ∧ ∃i,a.record=.source i ∧ A.accepts (slice w 0 i.val) ∧
    C.final (C.run q (slice w (i.val+t.depth) g))=true

theorem edge_source (C : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g p : Nat) (t : StartKeys.TrieFor w) (a : StartKeys.KeyFor w) (i : Fin (w.length+1))
    (hg : t.Good (StartKeys.text w fallback)) (ha : a∈t.leaves)
    (hv : StartKeys.ValidKey g (StartKeys.originalKey w a)) (ht : a.record=.source i)
    (hp : p≤t.depth) (q : Fin C.stateCount) :
    C.run ((StartKeys.edge C w (Range.build C w) p t).map.get q) (slice w (i.val+t.depth) g)=
      C.run q (slice w (i.val+p) g) := by
  have hc:=StartKeys.representative_common w fallback t hg a ha
  have hn : t.leaves≠[] := by intro h; rw [h] at ha; cases ha
  rw [StartKeys.edge_run C w fallback p t hg hn hp,
    StartKeys.source_edge w fallback g _ a i hv ht p t.depth hp hc]
  simp only [StartKeys.ValidKey,StartKeys.originalKey] at hv
  rw [ht] at hv
  have hd:=hc.2.1
  rw [hv.2.2] at hd
  rw [← DFA.run_append,← OuterColumn.slice_split w (i.val+p) (i.val+t.depth) g (by omega) (by omega)]

theorem build_root (A C : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (g : Nat)
    (t : StartKeys.TrieFor w) (hg : t.Good (StartKeys.text w fallback)) (hn : t.leaves≠[])
    (hv : ∀a,a∈t.leaves→StartKeys.ValidKey g (StartKeys.originalKey w a)) (q : Fin C.stateCount) :
    (root (build A C w (Range.build A w) (Range.build C w) t).1).get q=true ↔ Source A C w g t q := by
  induction t generalizing q with
  | empty => exact False.elim (hn rfl)
  | leaf a =>
    have hva:=hv a (by simp only [BoundaryTrie.Tree.leaves,List.mem_singleton])
    cases ht : a.record with
    | source i =>
      simp only [StartKeys.ValidKey,StartKeys.originalKey] at hva
      rw [ht] at hva
      have he : i.val+a.length=g := by omega
      simp only [build,ht,root,Table.get_ofFn,Range.query_correct A w 0 i.val (by omega)
        (by have hh:=i.isLt; omega),Source,BoundaryTrie.Tree.leaves,BoundaryTrie.Tree.depth,
        List.mem_singleton,exists_eq_left,Endpoint.source.injEq,exists_eq_left',he,
        slice,Nat.sub_self,List.take_zero,DFA.run,Bool.and_eq_true,DFA.accepts]
    | target i =>
      simp only [build,ht,root,Table.get_ofFn,Source,BoundaryTrie.Tree.leaves,
        List.mem_singleton,exists_eq_left,Endpoint.noConfusion,reduceCtorEq,false_and,exists_false]
  | node stem d l r ihl ihr =>
    have hvl : ∀a,a∈l.leaves→StartKeys.ValidKey g (StartKeys.originalKey w a) :=
      fun a ha=>hv a (List.mem_append_left _ ha)
    have hvr : ∀a,a∈r.leaves→StartKeys.ValidKey g (StartKeys.originalKey w a) :=
      fun a ha=>hv a (List.mem_append_right _ ha)
    have hd:=BoundaryTrie.Tree.edge_depths (StartKeys.text w fallback) stem d l r hg
    simp only [build,root,Table.get_ofFn,Bool.or_eq_true]
    change ((root (build A C w (Range.build A w) (Range.build C w) l).1).get
      ((StartKeys.edge C w (Range.build C w) d l).map.get q)=true ∨
      (root (build A C w (Range.build A w) (Range.build C w) r).1).get
        ((StartKeys.edge C w (Range.build C w) d r).map.get q)=true) ↔ _
    rw [ihl hg.1 hg.2.2.1 hvl,ihr hg.2.1 hg.2.2.2.1 hvr]
    constructor
    · rintro (⟨a,ha,i,ht,ha',hc⟩ | ⟨a,ha,i,ht,ha',hc⟩)
      · refine ⟨a,List.mem_append_left _ ha,i,ht,ha',?_⟩
        rwa [edge_source C w fallback g d l a i hg.1 ha (hvl a ha) ht hd.1 q] at hc
      · refine ⟨a,List.mem_append_right _ ha,i,ht,ha',?_⟩
        rwa [edge_source C w fallback g d r a i hg.2.1 ha (hvr a ha) ht hd.2 q] at hc
    · rintro ⟨a,ha,i,ht,ha',hc⟩
      rcases List.mem_append.mp ha with hal | har
      · left
        refine ⟨a,hal,i,ht,ha',?_⟩
        rwa [edge_source C w fallback g d l a i hg.1 hal (hvl a hal) ht hd.1 q]
      · right
        refine ⟨a,har,i,ht,ha',?_⟩
        rwa [edge_source C w fallback g d r a i hg.2.1 har (hvr a har) ht hd.2 q]

def budget (A C : DFA (Fin σ)) (n : Nat) : Nat :=
  2*(C.stateCount+8*(n.log2+2)+1)+(A.stateCount+8*(n.log2+2)+1)+C.stateCount+8

theorem build_work (A C : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (t : StartKeys.TrieFor w) (hg : t.Good (StartKeys.text w fallback)) (hn : t.leaves≠[]) :
    (build A C w (Range.build A w) (Range.build C w) t).2≤t.nodes*budget A C w.length := by
  induction t with
  | empty => exact False.elim (hn rfl)
  | leaf a =>
    cases ht : a.record with
    | source i =>
      have hb:=Range.query_work A w 0 i.val (by omega) (by have hh:=i.isLt; omega)
      simp only [build,ht,BoundaryTrie.Tree.nodes,Nat.one_mul,budget]
      omega
    | target i => simp only [build,ht,BoundaryTrie.Tree.nodes,Nat.one_mul,budget]; omega
  | node stem d l r ihl ihr =>
    have hl:=ihl hg.1 hg.2.2.1
    have hr:=ihr hg.2.1 hg.2.2.2.1
    have hd:=BoundaryTrie.Tree.edge_depths (StartKeys.text w fallback) stem d l r hg
    have he₁:=StartKeys.edge_work C w fallback d l hg.1 hg.2.2.1 hd.1
    have he₂:=StartKeys.edge_work C w fallback d r hg.2.1 hg.2.2.2.1 hd.2
    simp only [build,BoundaryTrie.Tree.nodes,Nat.add_mul,Nat.one_mul]
    unfold budget at *
    omega

end REWB.BoundaryApplication.StartSummary
