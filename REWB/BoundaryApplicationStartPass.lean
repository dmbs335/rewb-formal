import REWB.BoundaryApplicationStartLocal
import REWB.BoundaryApplicationStartLocate

/-! A measured top-down pass over the actual source-summary tree. Each
node stores its incoming finite B/E state and source C row; child states
are computed once by the shared indexes. Terminal positions are retained
for the subsequent materialized depth-ancestor index. -/
namespace REWB.BoundaryApplication.StartPass
open REWB.BoundaryTrie
open REWB.BoundaryIndex
variable {α : Type} {σ n m : Nat}

def terminal {m : Nat} : Endpoint m→Option (Fin (m+1))
  | .source _ => none
  | .target j => some j

def makeEntry (B C E : DFA α) (s : StartSummary.Saved C.stateCount n (Endpoint m))
    (p : Nat) (beta : Fin B.stateCount) (incoming : StartCuts.Row E) : StartStep.Entry B C E :=
  match s with
  | .empty => ⟨0,0,p,beta,incoming,StartSummary.root s⟩
  | .leaf key row => ⟨key.start,key.length,p,beta,incoming,row⟩
  | .node key d row _ _ => ⟨key.start,d,p,beta,incoming,row⟩

def go (B C E : DFA α) (cuts : StartCuts.Index B C E) (branges : Range.Index B)
    (cranges : Range.Index C) (eranges : Range.Index E) :
    StartSummary.Saved C.stateCount n (Endpoint m)→Nat→Fin B.stateCount→StartCuts.Row E→
      StartLocate.Tree (StartStep.Entry B C E) (m+1)×Nat
  | .empty,p,beta,incoming =>
    (.leaf 0 ⟨0,0,p,beta,incoming,Vector.ofFn (fun _=>false)⟩ none,C.stateCount+6)
  | .leaf key row,p,beta,incoming =>
    (.leaf key.length ⟨key.start,key.length,p,beta,incoming,row⟩ (terminal key.record),6)
  | .node key d row l r,p,beta,incoming =>
    let e:StartStep.Entry B C E:=⟨key.start,d,p,beta,incoming,row⟩
    let bottom:=StartStep.advance B C E cuts branges cranges eranges e
    let a:=go B C E cuts branges cranges eranges l d bottom.beta bottom.states
    let b:=go B C E cuts branges cranges eranges r d bottom.beta bottom.states
    (.node d e a.1 b.1,a.2+b.2+bottom.work+8)

theorem go_depth (B C E : DFA α) (cuts : StartCuts.Index B C E) (branges : Range.Index B)
    (cranges : Range.Index C) (eranges : Range.Index E)
    (s : StartSummary.Saved C.stateCount n (Endpoint m)) (p : Nat) (beta : Fin B.stateCount)
    (incoming : StartCuts.Row E) :
    (go B C E cuts branges cranges eranges s p beta incoming).1.depth=(StartSummary.shape s).depth := by
  cases s <;> rfl

theorem go_payload (B C E : DFA α) (cuts : StartCuts.Index B C E) (branges : Range.Index B)
    (cranges : Range.Index C) (eranges : Range.Index E)
    (s : StartSummary.Saved C.stateCount n (Endpoint m)) (p : Nat) (beta : Fin B.stateCount)
    (incoming : StartCuts.Row E) :
    (go B C E cuts branges cranges eranges s p beta incoming).1.payload=makeEntry B C E s p beta incoming := by
  cases s <;> rfl

theorem makeEntry_shape (B C E : DFA (Fin σ)) (w : Word (Fin σ))
    (s : StartSummary.Saved C.stateCount w.toArray.size (Endpoint w.length))
    (p : Nat) (beta : Fin B.stateCount) (incoming : StartCuts.Row E) :
    makeEntry B C E s p beta incoming=
      StartLocal.entry B C E w (StartSummary.shape s) p beta incoming (StartSummary.root s) := by
  cases s <;> rfl

theorem go_good (B C E : DFA α) (cuts : StartCuts.Index B C E) (branges : Range.Index B)
    (cranges : Range.Index C) (eranges : Range.Index E) (f : Nat→Fin σ)
    (s : StartSummary.Saved C.stateCount n (Endpoint m))
    (hg : (StartSummary.shape s).Good f) (hn : (StartSummary.shape s).leaves≠[])
    (p : Nat) (beta : Fin B.stateCount) (incoming : StartCuts.Row E) :
    (go B C E cuts branges cranges eranges s p beta incoming).1.Good := by
  induction s generalizing p beta incoming with
  | empty => exact False.elim (hn rfl)
  | leaf key row => exact True.intro
  | node key d row l r ihl ihr =>
    have hd:=BoundaryTrie.Tree.edge_depths f key d (StartSummary.shape l) (StartSummary.shape r) hg
    change _ ∧ _ ∧ _ ∧ _
    refine ⟨ihl hg.1 hg.2.2.1 _ _ _,ihr hg.2.1 hg.2.2.2.1 _ _ _,?_,?_⟩
    · rw [go_depth]; exact hd.1
    · rw [go_depth]; exact hd.2

theorem go_nodes (B C E : DFA α) (cuts : StartCuts.Index B C E) (branges : Range.Index B)
    (cranges : Range.Index C) (eranges : Range.Index E) (f : Nat→Fin σ)
    (s : StartSummary.Saved C.stateCount n (Endpoint m))
    (hg : (StartSummary.shape s).Good f) (hn : (StartSummary.shape s).leaves≠[])
    (p : Nat) (beta : Fin B.stateCount) (incoming : StartCuts.Row E) :
    (go B C E cuts branges cranges eranges s p beta incoming).1.nodes=(StartSummary.shape s).nodes := by
  induction s generalizing p beta incoming with
  | empty => exact False.elim (hn rfl)
  | leaf key row => rfl
  | node key d row l r ihl ihr =>
    simp only [go,StartLocate.Tree.nodes,StartSummary.shape,BoundaryTrie.Tree.nodes,
      ihl hg.1 hg.2.2.1,ihr hg.2.1 hg.2.2.2.1]

def budget (B C E : DFA α) (n : Nat) : Nat := StartStep.budget B C E n+B.stateCount+8*(n.log2+2)+11

theorem go_work (B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (s : StartSummary.Saved C.stateCount w.toArray.size (Endpoint w.length))
    (hg : (StartSummary.shape s).Good (StartKeys.text w fallback))
    (hn : (StartSummary.shape s).leaves≠[]) (p : Nat) (hp : p≤(StartSummary.shape s).depth)
    (beta : Fin B.stateCount) (incoming : StartCuts.Row E) :
    (go B C E (StartCuts.build B C E w) (Range.build B w) (Range.build C w) (Range.build E w)
      s p beta incoming).2≤(StartSummary.shape s).nodes*budget B C E w.length := by
  induction s generalizing p beta incoming with
  | empty => exact False.elim (hn rfl)
  | leaf key row => simp only [go,StartSummary.shape,BoundaryTrie.Tree.nodes,Nat.one_mul,budget]; omega
  | node key d row l r ihl ihr =>
    have hd:=BoundaryTrie.Tree.edge_depths (StartKeys.text w fallback) key d (StartSummary.shape l) (StartSummary.shape r) hg
    have hbound:=StartKeys.representative_bound w fallback (StartSummary.shape (.node key d row l r)) hg hn
    change key.start+d≤w.length at hbound
    let e:StartStep.Entry B C E:=⟨key.start,d,p,beta,incoming,row⟩
    let bottom:=StartStep.advance B C E (StartCuts.build B C E w) (Range.build B w)
      (Range.build C w) (Range.build E w) e
    have hl:=ihl hg.1 hg.2.2.1 d hd.1 bottom.beta bottom.states
    have hr:=ihr hg.2.1 hg.2.2.2.1 d hd.2 bottom.beta bottom.states
    have hw:=StartStep.advance_work B C E w e hp hbound
    change bottom.work≤_ at hw
    change (go B C E (StartCuts.build B C E w) (Range.build B w) (Range.build C w) (Range.build E w)
      l d bottom.beta bottom.states).2+
      (go B C E (StartCuts.build B C E w) (Range.build B w) (Range.build C w) (Range.build E w)
        r d bottom.beta bottom.states).2+bottom.work+8≤_
    simp only [StartSummary.shape,BoundaryTrie.Tree.nodes,Nat.add_mul,Nat.one_mul]
    unfold budget at *
    omega

end REWB.BoundaryApplication.StartPass
