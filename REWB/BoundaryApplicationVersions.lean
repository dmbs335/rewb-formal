import REWB.BoundaryApplicationCompile

/-! Save every persistent node version during one postorder execution.
Each child is evaluated once. Parent recoloring and light imports use the
child roots while the original child snapshots remain available. -/
namespace REWB.BoundaryApplication.Versions
open REWB.BoundaryIndex
variable {k m h : Nat}

inductive Snapshot (k m h : Nat) where
  | leaf : Mixed.Result k m h→Snapshot k m h
  | node : Mixed.Result k m h→Nat→Snapshot k m h→Snapshot k m h→Snapshot k m h

def root : Snapshot k m h→Mixed.Result k m h
  | .leaf r => r
  | .node r _ _ _ => r

def allocated : Snapshot k m h→Nat
  | .leaf _ => 1
  | .node _ n _ _ => n

theorem root_node (r : Mixed.Result k m h) (n : Nat) (a b : Snapshot k m h) :
    root (.node r n a b)=r := rfl
theorem allocated_node (r : Mixed.Result k m h) (n : Nat) (a b : Snapshot k m h) :
    allocated (.node r n a b)=n := rfl

def execute (base : BoundaryIndex.Tree k m h) : Mixed.Program k m h→Snapshot k m h
  | .source p => .leaf (Mixed.execute base (.source p))
  | .target p c q => .leaf (Mixed.execute base (.target p c q))
  | .node g f p q =>
    let a:=execute base p
    let b:=execute base q
    let aa:=root a
    let bb:=root b
    let l:=Merge.recolor g aa.state
    let r:=Merge.recolor f bb.state
    let out:=Mixed.combine l.1 r.1 aa.totalMass bb.totalMass
    let result : Mixed.Result k m h:=
      ⟨out.1,aa.totalMass+bb.totalMass,aa.steps+bb.steps+l.2+r.2+out.2+1,
        aa.transfers+bb.transfers+Mixed.imported l.1 r.1 aa.totalMass bb.totalMass⟩
    .node result (allocated a+allocated b+1) a b

theorem execute_root (base : BoundaryIndex.Tree k m h) (p : Mixed.Program k m h) :
    root (execute base p)=Mixed.execute base p := by
  induction p with
  | source _ => rfl
  | target _ _ _ => rfl
  | node g f p q ihp ihq => simp only [execute,root_node,ihp,ihq,Mixed.execute]

theorem execute_allocated (base : BoundaryIndex.Tree k m h) (p : Mixed.Program k m h) :
    allocated (execute base p)+1=2*MaskedEventBudget.size (Mixed.shape p) := by
  induction p with
  | source _ => rfl
  | target _ _ _ => rfl
  | node g f p q ihp ihq =>
    simp only [execute,allocated_node,Mixed.shape,MaskedEventBudget.size]
    omega

def work (s : Snapshot k m h) : Nat := (root s).steps+4*allocated s

def programAt : Mixed.Program k m h→List Bool→Option (Mixed.Program k m h)
  | p,[] => some p
  | .node _ _ p q,b::path => programAt (if b then q else p) path
  | _,_::_ => none

def get : Snapshot k m h→List Bool→Option (Snapshot k m h)
  | s,[] => some s
  | .node _ _ p q,b::path => get (if b then q else p) path
  | .leaf _,_::_ => none

theorem programAt_nil (p : Mixed.Program k m h) : programAt p []=some p := by cases p <;> rfl
theorem get_nil (s : Snapshot k m h) : get s []=some s := by cases s <;> rfl

theorem execute_get (base : BoundaryIndex.Tree k m h) (p : Mixed.Program k m h) (path : List Bool) :
    get (execute base p) path=(programAt p path).map (execute base) := by
  induction path generalizing p with
  | nil => rw [get_nil,programAt_nil]; rfl
  | cons b path ih =>
    cases p with
    | source _ => rfl
    | target _ _ _ => rfl
    | node g f p q => cases b <;> exact ih _

theorem get_root (base : BoundaryIndex.Tree k m h) (p q : Mixed.Program k m h)
    (path : List Bool) (hp : programAt p path=some q) :
    (get (execute base p) path).map root=some (Mixed.execute base q) := by
  rw [execute_get,hp]
  change some (root (execute base q))=some (Mixed.execute base q)
  rw [execute_root]

end REWB.BoundaryApplication.Versions

namespace REWB.BoundaryApplication
open REWB.BoundaryTrie
variable {σ : Nat}

def subtree {w : Word (Fin σ)} : TrieFor w→List Bool→Option (TrieFor w)
  | t,[] => some t
  | .node _ _ l r,b::path => subtree (if b then r else l) path
  | _,_::_ => none

theorem subtree_nil (w : Word (Fin σ)) (t : TrieFor w) : subtree t []=some t := by cases t <;> rfl

theorem subtree_good (w : Word (Fin σ)) (fallback : Fin σ) (t u : TrieFor w)
    (path : List Bool) (hg : t.Good (reverseText w fallback)) (hs : subtree t path=some u) :
    u.Good (reverseText w fallback) := by
  induction path generalizing t with
  | nil => rw [subtree_nil] at hs; have he : t=u := Option.some.inj hs; rwa [← he]
  | cons b path ih =>
    cases t with
    | empty => cases hs
    | leaf _ => cases hs
    | node a d l r =>
      cases b with
      | false => exact ih l hg.1 hs
      | true => exact ih r hg.2.1 hs

theorem subtree_nonempty (w : Word (Fin σ)) (fallback : Fin σ) (t u : TrieFor w)
    (path : List Bool) (hg : t.Good (reverseText w fallback))
    (hn : t.leaves≠[]) (hs : subtree t path=some u) : u.leaves≠[] := by
  induction path generalizing t with
  | nil => rw [subtree_nil] at hs; have he : t=u := Option.some.inj hs; rwa [← he]
  | cons b path ih =>
    cases t with
    | empty => cases hs
    | leaf _ => cases hs
    | node a d l r =>
      cases b with
      | false => exact ih l hg.1 hg.2.2.1 hs
      | true => exact ih r hg.2.1 hg.2.2.2.1 hs

theorem subtree_mem (w : Word (Fin σ)) (t u : TrieFor w) (path : List Bool)
    (hs : subtree t path=some u) (a : KeyFor w) (ha : a∈u.leaves) : a∈t.leaves := by
  induction path generalizing t with
  | nil => rw [subtree_nil] at hs; have he : t=u := Option.some.inj hs; rwa [he]
  | cons b path ih =>
    cases t with
    | empty => cases hs
    | leaf _ => cases hs
    | node a d l r =>
      cases b with
      | false => exact List.mem_append_left _ (ih l hs)
      | true => exact List.mem_append_right _ (ih r hs)

theorem compile_subtree (D E : DFA (Fin σ)) (w : Word (Fin σ)) (idx : Range.Index D)
    (t : TrieFor w) (path : List Bool) :
    Versions.programAt (compile D E w idx t).1 path=
      (subtree t path).map (fun u=>(compile D E w idx u).1) := by
  induction path generalizing t with
  | nil => rw [Versions.programAt_nil,subtree_nil]; rfl
  | cons b path ih =>
    cases t with
    | empty => rfl
    | leaf a => cases hr : a.record <;> simp only [compile,hr,Versions.programAt,subtree,Option.map] <;> rfl
    | node a d l r => cases b <;> exact ih _

/-- Every saved local version has the color invariant at its own depth,
including snapshots retained before an ancestor recolors a heavy child. -/
theorem version_active (D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g : Nat) (t u : TrieFor w) (path : List Bool)
    (base : BoundaryIndex.Tree D.stateCount E.stateCount (height w.length))
    (hbase : BoundaryIndex.Tree.Good base) (hblank : BoundaryIndex.MergeSchedule.Blank base)
    (hg : t.Good (reverseText w fallback)) (hn : t.leaves≠[])
    (hv : ∀a,a∈t.leaves→ValidKey g (originalKey w a)) (hs : subtree t path=some u)
    (i : BoundaryIndex.Merge.Position (height w.length)) (c : Fin D.stateCount) (q : Fin E.stateCount) :
    ∃s,Versions.get (Versions.execute base (compile D E w (Range.build D w) t).1) path=some s ∧
      ((BoundaryIndex.Merge.point (Versions.root s).state.tree i).active c q=true ↔
        Target D E w g u i c q) := by
  let p:=(compile D E w (Range.build D w) u).1
  have hprog : Versions.programAt (compile D E w (Range.build D w) t).1 path=some p := by
    rw [compile_subtree,hs]
    rfl
  refine ⟨Versions.execute base p,?_,?_⟩
  · rw [Versions.execute_get,hprog]
    rfl
  · rw [Versions.execute_root,BoundaryIndex.Mixed.execute_active base hbase hblank]
    exact compile_active D E w fallback g u (subtree_good w fallback t u path hg hs)
      (subtree_nonempty w fallback t u path hg hn hs)
      (fun a ha=>hv a (subtree_mem w t u path hs a ha)) i c q

end REWB.BoundaryApplication
