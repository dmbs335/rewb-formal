import REWB.BoundaryApplicationHeavyCost

/-! Every immutable heavy-path snapshot preserves the shared endpoint
transition layout and the exact live-position list invariant. This covers
all stored nodes, including snapshots retained before a descendant's
lazy preimage recoloring. -/
namespace REWB.BoundaryApplication.Heavy
open REWB.BoundaryIndex
open REWB.BoundaryIndex.Merge
variable {σ : Nat}

def StateGood {k m h : Nat} (base : BoundaryIndex.Tree k m h) (s : Merge.State k m h) : Prop :=
  Valid s ∧ ∀i,(point s.tree i).trans=(point base i).trans

def EntryGood (A D E : DFA (Fin σ)) (n : Nat)
    (normalBase : BoundaryIndex.Tree D.stateCount E.stateCount (height n))
    (base : BoundaryIndex.Tree (Subset.count A) E.stateCount (height n)) (e : Entry A D E n) : Prop :=
  StateGood normalBase e.normal.state ∧ StateGood base e.subsets

def All {A D E : DFA (Fin σ)} {n : Nat} (P : Entry A D E n→Prop) : Saved A D E n→Prop
  | .leaf e _ => P e
  | .node e _ l r => P e ∧ All P l ∧ All P r

theorem blank_good {k m h : Nat} (base : BoundaryIndex.Tree k m h)
    (hg : Tree.Good base) (hb : MergeSchedule.Blank base) : StateGood base (blank base) :=
  ⟨blank_valid base hg hb,fun _=>rfl⟩

theorem advance_good (A E : DFA (Fin σ)) (w : Word (Fin σ)) (ranges : Range.Index A)
    (base : BoundaryIndex.Tree (Subset.count A) E.stateCount (height w.length))
    (parent : Nat) (child : TrieFor w)
    (s : Merge.State (Subset.count A) E.stateCount (height w.length)) (hs : StateGood base s) :
    StateGood base (advance A E w ranges parent child s).1 := by
  refine ⟨advance_valid A E w ranges parent child s hs.1,?_⟩
  intro i
  rw [advance_trans,hs.2]

theorem root_good (A B D E : DFA (Fin σ)) (w : Word (Fin σ)) (rows : RTable.Shared A B D)
    (ranges : Range.Index A) (idx : Range.Index D)
    (base : BoundaryIndex.Tree (Subset.count A) E.stateCount (height w.length))
    (normalBase : BoundaryIndex.Tree D.stateCount E.stateCount (height w.length))
    (hng : Tree.Good normalBase) (hnb : MergeSchedule.Blank normalBase)
    (t : TrieFor w) (incoming : Merge.State (Subset.count A) E.stateCount (height w.length))
    (hi : StateGood base incoming) :
    EntryGood A D E w.length normalBase base (root (go A B D E w rows ranges base t
      (Versions.execute normalBase (compile D E w idx t).1) incoming).saved) := by
  constructor
  · rw [root_normal,Versions.execute_root]
    exact ⟨Mixed.execute_valid normalBase hng hnb _,Mixed.execute_trans normalBase _⟩
  · refine ⟨root_valid A B D E w rows ranges idx base normalBase hng hnb t incoming hi.1,?_⟩
    intro i
    rw [root_trans,hi.2]

theorem go_all (A B D E : DFA (Fin σ)) (w : Word (Fin σ)) (rows : RTable.Shared A B D)
    (ranges : Range.Index A) (idx : Range.Index D)
    (base : BoundaryIndex.Tree (Subset.count A) E.stateCount (height w.length))
    (hbg : Tree.Good base) (hbb : MergeSchedule.Blank base)
    (normalBase : BoundaryIndex.Tree D.stateCount E.stateCount (height w.length))
    (hng : Tree.Good normalBase) (hnb : MergeSchedule.Blank normalBase)
    (t : TrieFor w) (incoming : Merge.State (Subset.count A) E.stateCount (height w.length))
    (hi : StateGood base incoming) :
    All (EntryGood A D E w.length normalBase base) (go A B D E w rows ranges base t
      (Versions.execute normalBase (compile D E w idx t).1) incoming).saved := by
  induction t generalizing incoming with
  | empty => exact root_good A B D E w rows ranges idx base normalBase hng hnb .empty incoming hi
  | leaf key => exact root_good A B D E w rows ranges idx base normalBase hng hnb (.leaf key) incoming hi
  | node key depth l r ihl ihr =>
    let t : TrieFor w:=.node key depth l r
    let s:=Versions.execute normalBase (compile D E w idx t).1
    let rr:=RTable.node A B D w rows t
    let out:=Lift.importMany rr.map (Versions.root s).state.tree (lightState s).positions incoming
    let next:=advance A E w ranges depth (if heavyRight s then r else l) out.1
    let il:=if heavyRight s then blank base else next.1
    let ir:=if heavyRight s then next.1 else blank base
    have hroot:=root_good A B D E w rows ranges idx base normalBase hng hnb t incoming hi
    have hout : StateGood base out.1 := hroot.2
    have hnext : StateGood base next.1 := advance_good A E w ranges base depth _ out.1 hout
    have hb:=blank_good base hbg hbb
    have hil : StateGood base il := by unfold il; split <;> assumption
    have hir : StateGood base ir := by unfold ir; split <;> assumption
    exact ⟨hroot,ihl il hil,ihr ir hir⟩

def get {A D E : DFA (Fin σ)} {n : Nat} : Saved A D E n→List Bool→Option (Saved A D E n)
  | s,[] => some s
  | .node _ _ l r,b::path => get (if b then r else l) path
  | .leaf _ _,_::_ => none

theorem all_root {A D E : DFA (Fin σ)} {n : Nat} (P : Entry A D E n→Prop)
    (s : Saved A D E n) (hs : All P s) : P (root s) := by
  cases s with
  | leaf _ _ => exact hs
  | node _ _ _ _ => exact hs.1

theorem all_get {A D E : DFA (Fin σ)} {n : Nat} (P : Entry A D E n→Prop)
    (s u : Saved A D E n) (hs : All P s) (path : List Bool) (hu : get s path=some u) : P (root u) := by
  induction path generalizing s with
  | nil =>
    have he : s=u := by cases s <;> exact Option.some.inj hu
    rw [← he]
    exact all_root P s hs
  | cons b path ih =>
    cases s with
    | leaf _ _ => cases hu
    | node _ _ l r =>
      cases b with
      | false => exact ih l hs.2.1 hu
      | true => exact ih r hs.2.2 hu

end REWB.BoundaryApplication.Heavy
