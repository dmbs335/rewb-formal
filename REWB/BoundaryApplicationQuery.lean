import REWB.BoundaryApplicationAggregate

/-! Query an actual saved fixed-end version at an exact right boundary.
The local color predicate is provided by the later accepted-cut stage;
the target positions, D colors, and E intervening-word acceptance are
computed by the concrete index here. Path lookup is measured separately
and is not claimed to be a heavy-path jump. -/
namespace REWB.BoundaryApplication.Versions
variable {k m h : Nat}

def getCounted : Snapshot k m h→List Bool→Option (Snapshot k m h)×Nat
  | s,[] => (some s,1)
  | .leaf _,_::_ => (none,1)
  | .node _ _ l r,b::path =>
    let out:=getCounted (if b then r else l) path
    (out.1,out.2+1)

theorem getCounted_value (s : Snapshot k m h) (path : List Bool) :
    (getCounted s path).1=get s path := by
  induction path generalizing s with
  | nil => cases s <;> rfl
  | cons b path ih =>
    cases s with
    | leaf _ => rfl
    | node root n l r => cases b <;> exact ih _

theorem getCounted_work (s : Snapshot k m h) (path : List Bool) :
    (getCounted s path).2≤path.length+1 := by
  induction path generalizing s with
  | nil => cases s <;> exact Nat.le_refl _
  | cons b path ih =>
    cases s with
    | leaf _ => simp only [getCounted,List.length_cons]; omega
    | node root n l r =>
      cases b <;> simp only [getCounted,Bool.false_eq_true,if_false,if_true,List.length_cons]
      · have hh:=ih l; omega
      · have hh:=ih r; omega

end REWB.BoundaryApplication.Versions

namespace REWB.BoundaryApplication.FixedEnd
open REWB.BoundaryIndex
open REWB.Spec (slice)
variable {σ : Nat}

def query (E : DFA (Fin σ)) {k h : Nat} (select : Fin k→Bool)
    (s : Versions.Snapshot k E.stateCount h) (r : Nat) : Bool×Nat :=
  TokenIndex.query E select (Versions.root s).state.tree (r+1)

def Predicate (D E : DFA (Fin σ)) (w : Word (Fin σ)) (g : Nat)
    (u : TrieFor w) (select : Fin D.stateCount→Bool) (r : Nat) : Prop :=
  ∃a,a∈u.leaves ∧ ∃t,a.record=.target t ∧ t.val≤r ∧
    select (color D w g t u.depth)=true ∧ E.accepts (slice w t.val r)

theorem query_version_correct (D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g : Nat) (hg : g≤w.length) (u : TrieFor w) (path : List Bool)
    (hs : subtree (trie w fallback g hg).tree path=some u)
    (select : Fin D.stateCount→Bool) (r : Nat) (hr : r≤w.length) :
    ∃s,Versions.get (build D E w fallback g hg).versions path=some s ∧
      ((query E select s r).1=true ↔ Predicate D E w g u select r) := by
  let base:=MergeBuild.prepare (k:=D.stateCount) (rows E w) (height w.length)
  let p:=(compile D E w (Range.build D w) u).1
  let s:=Versions.execute base.1 p
  have hu:=subtree_good w fallback _ u path (trie_good w fallback g hg) hs
  have hn:=subtree_nonempty w fallback _ u path (trie_good w fallback g hg) (trie_nonempty w fallback g hg) hs
  have hv : ∀a,a∈u.leaves→ValidKey g (originalKey w a) :=
    fun a ha=>trie_valid w fallback g hg a (subtree_mem w _ u path hs a ha)
  have hprog : Versions.programAt (compile D E w (Range.build D w) (trie w fallback g hg).tree).1 path=some p := by
    rw [compile_subtree,hs]
    rfl
  have hgTree : Tree.Good (Versions.root s).state.tree := by
    rw [Versions.execute_root]
    exact (Mixed.execute_valid base.1 (MergeBuild.prepare_good _ _) (MergeBuild.prepare_blank _ _) p).1
  have htrans : ∀i : Merge.Position (height w.length),(Merge.point (Versions.root s).state.tree i).trans=
      ((rows E w)[i.val]?.getD (Vector.ofFn id)).get := by
    intro i
    rw [Versions.execute_root,Mixed.execute_trans]
    exact MergeBuild.prepare_trans _ _ i
  have hactive : ∀i c q,(Merge.point (Versions.root s).state.tree i).active c q=true ↔ Target D E w g u i c q := by
    intro i c q
    rw [Versions.execute_root,Mixed.execute_active base.1 (MergeBuild.prepare_good _ _) (MergeBuild.prepare_blank _ _)]
    exact compile_active D E w fallback g u hu hn hv i c q
  refine ⟨s,?_,?_⟩
  · change Versions.get (Versions.execute base.1
      (compile D E w (Range.build D w) (trie w fallback g hg).tree).1) path=some s
    rw [Versions.execute_get,hprog]
    rfl
  · rw [query,Aggregate.query_correct E w _ hgTree (Tree.capacity (w.length+1)) htrans select r hr]
    constructor
    · rintro ⟨i,hi,c,q,hc,hq,hf⟩
      obtain ⟨a,ha,t,ht,hip,hcol,hstate⟩:=(hactive i c q).mp hq
      refine ⟨a,ha,t,ht,?_,?_,?_⟩
      · rw [hip] at hi
        exact hi
      · rwa [← hcol]
      · unfold DFA.accepts
        rw [hstate,hip] at hf
        exact hf
    · rintro ⟨a,ha,t,ht,hir,hsel,hE⟩
      refine ⟨position t,hir,color D w g t u.depth,E.initial,hsel,
        (hactive _ _ _).mpr ⟨a,ha,t,ht,rfl,rfl,rfl⟩,hE⟩

theorem query_steps (E : DFA (Fin σ)) {k h : Nat} (select : Fin k→Bool)
    (s : Versions.Snapshot k E.stateCount h) (r : Nat) :
    (query E select s r).2≤(h+1)*Tree.queryBudget k E.stateCount+k+k*E.stateCount :=
  TokenIndex.query_steps E select (Versions.root s).state.tree (r+1)

def queryPath (D E : DFA (Fin σ)) (w : Word (Fin σ)) (idx : Index D E w)
    (path : List Bool) (select : Fin D.stateCount→Bool) (r : Nat) : Option Bool×Nat :=
  let s:=Versions.getCounted idx.versions path
  match s.1 with
  | none => (none,s.2)
  | some v => let a:=query E select v r; (some a.1,s.2+a.2)

theorem queryPath_correct (D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g : Nat) (hg : g≤w.length) (u : TrieFor w) (path : List Bool)
    (hs : subtree (trie w fallback g hg).tree path=some u)
    (select : Fin D.stateCount→Bool) (r : Nat) (hr : r≤w.length) :
    (queryPath D E w (build D E w fallback g hg) path select r).1=some true ↔
      Predicate D E w g u select r := by
  obtain ⟨s,hget,hq⟩:=query_version_correct D E w fallback g hg u path hs select r hr
  simp only [queryPath,Versions.getCounted_value,hget,Option.some.injEq]
  exact hq

theorem queryPath_work (D E : DFA (Fin σ)) (w : Word (Fin σ)) (idx : Index D E w)
    (path : List Bool) (select : Fin D.stateCount→Bool) (r : Nat) :
    (queryPath D E w idx path select r).2≤path.length+1+
      (height w.length+1)*Tree.queryBudget D.stateCount E.stateCount+D.stateCount+D.stateCount*E.stateCount := by
  have hg:=Versions.getCounted_work idx.versions path
  simp only [queryPath]
  split
  · omega
  next v he =>
    have hq:=query_steps E select v r
    dsimp only
    omega

end REWB.BoundaryApplication.FixedEnd
