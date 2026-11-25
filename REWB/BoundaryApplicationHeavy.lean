import REWB.BoundaryApplicationSubset

/-! Construct the fixed-end heavy-path subset versions in one preorder
pass over the actual compressed trie and its saved D-color versions.
Cached source-plus-target mass chooses the heavy child. Only the light
child's maintained target list is imported; a terminal imports its own
list once. Heavy endpoints are never enumerated by this construction.

An imported endpoint is read from the parent's D version, whose color is
already at the parent depth. The retained subset version is pulled back
through one materialized A edge map before descending into the heavy
child. The light child starts from the shared static blank index. -/
namespace REWB.BoundaryApplication.Heavy
open REWB.BoundaryIndex
open REWB.BoundaryIndex.Merge
variable {σ : Nat}

def blank {k m h : Nat} (base : BoundaryIndex.Tree k m h) : Merge.State k m h :=
  ⟨base,[],0⟩

def left {k m h : Nat} : Versions.Snapshot k m h→Versions.Snapshot k m h
  | .leaf r => .leaf r
  | .node _ _ l _ => l

def right {k m h : Nat} : Versions.Snapshot k m h→Versions.Snapshot k m h
  | .leaf r => .leaf r
  | .node _ _ _ r => r

def heavyRight {k m h : Nat} (s : Versions.Snapshot k m h) : Bool :=
  decide ((Versions.root (left s)).totalMass≤(Versions.root (right s)).totalMass)

def lightState {k m h : Nat} (s : Versions.Snapshot k m h) : Merge.State k m h :=
  if heavyRight s then (Versions.root (left s)).state else (Versions.root (right s)).state

structure EntryAt (A D E : DFA (Fin σ)) (h : Nat) where
  normal : Mixed.Result D.stateCount E.stateCount h
  subsets : Merge.State (Subset.count A) E.stateCount h
  rows : Vector (Colors.Color A) D.stateCount
  depth : Nat
  endpoint : Nat

inductive SavedAt (A D E : DFA (Fin σ)) (n h : Nat) where
  | leaf : EntryAt A D E h→Option (Endpoint n)→SavedAt A D E n h
  | node : EntryAt A D E h→Bool→SavedAt A D E n h→SavedAt A D E n h→SavedAt A D E n h

abbrev Entry (A D E : DFA (Fin σ)) (n : Nat) := EntryAt A D E (height n)
abbrev Saved (A D E : DFA (Fin σ)) (n : Nat) := SavedAt A D E n (height n)

def root {A D E : DFA (Fin σ)} {n h : Nat} : SavedAt A D E n h→EntryAt A D E h
  | .leaf e _ => e
  | .node e _ _ _ => e

structure ResultAt (A D E : DFA (Fin σ)) (n h : Nat) where
  saved : SavedAt A D E n h
  allocated : Nat
  imports : Nat
  work : Nat

abbrev Result (A D E : DFA (Fin σ)) (n : Nat) := ResultAt A D E n (height n)

def advance (A E : DFA (Fin σ)) (w : Word (Fin σ)) (ranges : Range.Index A) {h : Nat}
    (parent : Nat) (child : TrieFor w)
    (s : Merge.State (Subset.count A) E.stateCount h) :
    Merge.State (Subset.count A) E.stateCount h×Nat :=
  let e:=edge A w ranges parent child
  let out:=Merge.recolor (Colors.preimageMap A e.map) s
  (out.1,e.work+Subset.count A+out.2+1)

def go (A B D E : DFA (Fin σ)) (w : Word (Fin σ)) (rows : RTable.Shared A B D)
    (ranges : Range.Index A) {h : Nat} (base : BoundaryIndex.Tree (Subset.count A) E.stateCount h) :
    TrieFor w→Versions.Snapshot D.stateCount E.stateCount h→
      Merge.State (Subset.count A) E.stateCount h→ResultAt A D E w.length h
  | .empty,s,incoming =>
    let rr:=RTable.node A B D w rows .empty
    let normal:=Versions.root s
    let out:=Lift.importMany rr.map normal.state.tree normal.state.positions incoming
    let entry : EntryAt A D E h:=⟨normal,out.1,rr.map,0,
      rows.length-(representative w .empty).start⟩
    ⟨.leaf entry none,1,normal.state.cachedSize,out.2+rr.work A D+8⟩
  | .leaf key,s,incoming =>
    let rr:=RTable.node A B D w rows (.leaf key)
    let normal:=Versions.root s
    let out:=Lift.importMany rr.map normal.state.tree normal.state.positions incoming
    let entry : EntryAt A D E h:=⟨normal,out.1,rr.map,key.length,
      rows.length-key.start⟩
    ⟨.leaf entry (some key.record),1,normal.state.cachedSize,out.2+rr.work A D+8⟩
  | .node stem depth l r,s,incoming =>
    let rr:=RTable.node A B D w rows (.node stem depth l r)
    let normal:=Versions.root s
    let chooseRight:=heavyRight s
    let light:=lightState s
    let out:=Lift.importMany rr.map normal.state.tree light.positions incoming
    let entry : EntryAt A D E h:=⟨normal,out.1,rr.map,depth,
      rows.length-stem.start⟩
    let next:=advance A E w ranges depth (if chooseRight then r else l) out.1
    let a:=go A B D E w rows ranges base l (left s) (if chooseRight then blank base else next.1)
    let b:=go A B D E w rows ranges base r (right s) (if chooseRight then next.1 else blank base)
    ⟨.node entry chooseRight a.saved b.saved,a.allocated+b.allocated+1,
      a.imports+b.imports+light.cachedSize,a.work+b.work+out.2+rr.work A D+next.2+14⟩

theorem root_normal (A B D E : DFA (Fin σ)) (w : Word (Fin σ)) (rows : RTable.Shared A B D)
    (ranges : Range.Index A) (base : BoundaryIndex.Tree (Subset.count A) E.stateCount (height w.length))
    (t : TrieFor w) (s : Versions.Snapshot D.stateCount E.stateCount (height w.length))
    (incoming : Merge.State (Subset.count A) E.stateCount (height w.length)) :
    (root (go A B D E w rows ranges base t s incoming).saved).normal=Versions.root s := by
  cases t <;> rfl

theorem root_rows (A B D E : DFA (Fin σ)) (w : Word (Fin σ)) (rows : RTable.Shared A B D)
    (ranges : Range.Index A) (base : BoundaryIndex.Tree (Subset.count A) E.stateCount (height w.length))
    (t : TrieFor w) (s : Versions.Snapshot D.stateCount E.stateCount (height w.length))
    (incoming : Merge.State (Subset.count A) E.stateCount (height w.length)) :
    (root (go A B D E w rows ranges base t s incoming).saved).rows=(RTable.node A B D w rows t).map := by
  cases t <;> rfl

theorem root_depth (A B D E : DFA (Fin σ)) (w : Word (Fin σ)) (rows : RTable.Shared A B D)
    (ranges : Range.Index A) (base : BoundaryIndex.Tree (Subset.count A) E.stateCount (height w.length))
    (t : TrieFor w) (s : Versions.Snapshot D.stateCount E.stateCount (height w.length))
    (incoming : Merge.State (Subset.count A) E.stateCount (height w.length)) :
    (root (go A B D E w rows ranges base t s incoming).saved).depth=t.depth := by
  cases t <;> rfl

/-- The selected source list is either one terminal's list or the light
child's list. This definition is a constant-time selector, not a scan. -/
def batch (w : Word (Fin σ)) {k m : Nat} (t : TrieFor w)
    (s : Versions.Snapshot k m (height w.length)) : Merge.State k m (height w.length) :=
  match t with
  | .node _ _ _ _ => lightState s
  | _ => (Versions.root s).state

theorem root_subsets (A B D E : DFA (Fin σ)) (w : Word (Fin σ)) (rows : RTable.Shared A B D)
    (ranges : Range.Index A) (base : BoundaryIndex.Tree (Subset.count A) E.stateCount (height w.length))
    (t : TrieFor w) (s : Versions.Snapshot D.stateCount E.stateCount (height w.length))
    (incoming : Merge.State (Subset.count A) E.stateCount (height w.length)) :
    (root (go A B D E w rows ranges base t s incoming).saved).subsets=
      (Lift.importMany (RTable.node A B D w rows t).map (Versions.root s).state.tree
        (batch w t s).positions incoming).1 := by
  cases t <;> rfl

theorem allocated (A B D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (rows : RTable.Shared A B D)
    (ranges : Range.Index A) (base : BoundaryIndex.Tree (Subset.count A) E.stateCount (height w.length))
    (t : TrieFor w) (s : Versions.Snapshot D.stateCount E.stateCount (height w.length))
    (incoming : Merge.State (Subset.count A) E.stateCount (height w.length))
    (hg : t.Good (reverseText w fallback)) (hn : t.leaves≠[]) :
    (go A B D E w rows ranges base t s incoming).allocated=t.nodes := by
  induction t generalizing s incoming with
  | empty => exact False.elim (hn rfl)
  | leaf _ => rfl
  | node key depth l r ihl ihr =>
    simp only [go,BoundaryTrie.Tree.nodes]
    have hl:=ihl (left s) (if heavyRight s then blank base else
      (advance A E w ranges depth (if heavyRight s then r else l)
        (Lift.importMany (RTable.node A B D w rows (.node key depth l r)).map
          (Versions.root s).state.tree (lightState s).positions incoming).1).1) hg.1 hg.2.2.1
    have hr:=ihr (right s) (if heavyRight s then
      (advance A E w ranges depth (if heavyRight s then r else l)
        (Lift.importMany (RTable.node A B D w rows (.node key depth l r)).map
          (Versions.root s).state.tree (lightState s).positions incoming).1).1 else blank base) hg.2.1 hg.2.2.2.1
    omega

theorem blank_valid {k m h : Nat} (base : BoundaryIndex.Tree k m h)
    (hg : Tree.Good base) (hb : MergeSchedule.Blank base) : Valid (blank base) := by
  refine ⟨hg,rfl,?_⟩
  intro i
  constructor
  · intro hi
    exact False.elim (List.not_mem_nil hi)
  · rintro ⟨c,q,hc⟩
    change (point base i).active c q=true at hc
    rw [hb i c q] at hc
    cases hc

theorem advance_valid (A E : DFA (Fin σ)) (w : Word (Fin σ)) (ranges : Range.Index A)
    (parent : Nat) (child : TrieFor w)
    (s : Merge.State (Subset.count A) E.stateCount (height w.length)) (hs : Valid s) :
    Valid (advance A E w ranges parent child s).1 := Merge.recolor_valid _ _ hs

theorem advance_trans (A E : DFA (Fin σ)) (w : Word (Fin σ)) (ranges : Range.Index A)
    (parent : Nat) (child : TrieFor w)
    (s : Merge.State (Subset.count A) E.stateCount (height w.length))
    (i : Position (height w.length)) :
    (point (advance A E w ranges parent child s).1.tree i).trans=(point s.tree i).trans := by
  change (point (Tree.recolor _ s.tree).1 i).trans=_
  rw [point_recolor]
  rfl

theorem advance_selected (A E : DFA (Fin σ)) (w : Word (Fin σ)) (ranges : Range.Index A)
    (parent : Nat) (child : TrieFor w)
    (s : Merge.State (Subset.count A) E.stateCount (height w.length))
    (i : Position (height w.length)) (alpha : Fin A.stateCount) (q : Fin E.stateCount) :
    Subset.Selected A (advance A E w ranges parent child s).1.tree i alpha q ↔
      Subset.Selected A s.tree i ((edge A w ranges parent child).map.get alpha) q :=
  Subset.recolored_selected A _ _ _ _ _

theorem execute_left {k m h : Nat} (base : BoundaryIndex.Tree k m h)
    (g f : Vector (Fin k) k) (p q : Mixed.Program k m h) :
    left (Versions.execute base (.node g f p q))=Versions.execute base p := rfl

theorem execute_right {k m h : Nat} (base : BoundaryIndex.Tree k m h)
    (g f : Vector (Fin k) k) (p q : Mixed.Program k m h) :
    right (Versions.execute base (.node g f p q))=Versions.execute base q := rfl

theorem batch_subset (D E : DFA (Fin σ)) (w : Word (Fin σ)) (idx : Range.Index D)
    (base : BoundaryIndex.Tree D.stateCount E.stateCount (height w.length))
    (t : TrieFor w) (i : Position (height w.length)) :
    i∈(batch w t (Versions.execute base (compile D E w idx t).1)).positions →
      i∈(Versions.root (Versions.execute base (compile D E w idx t).1)).state.positions := by
  cases t with
  | empty => exact id
  | leaf _ => exact id
  | node key depth l r =>
    rw [Versions.execute_root]
    intro hi
    apply (Mixed.execute_perm base _).mem_iff.mpr
    change i∈Mixed.targetPositions (compile D E w idx l).1++Mixed.targetPositions (compile D E w idx r).1
    change i∈(lightState (Versions.execute base (.node _ _ _ _))).positions at hi
    unfold lightState at hi
    split at hi
    · simp only [execute_left,Versions.execute_root] at hi
      exact List.mem_append_left _ ((Mixed.execute_perm base _).mem_iff.mp hi)
    · simp only [execute_right,Versions.execute_root] at hi
      exact List.mem_append_right _ ((Mixed.execute_perm base _).mem_iff.mp hi)

theorem batch_live (D E : DFA (Fin σ)) (w : Word (Fin σ)) (idx : Range.Index D)
    (base : BoundaryIndex.Tree D.stateCount E.stateCount (height w.length))
    (hg : Tree.Good base) (hb : MergeSchedule.Blank base) (t : TrieFor w)
    (i : Position (height w.length)) (hi : i∈(batch w t (Versions.execute base (compile D E w idx t).1)).positions) :
    ∃c q,(point (Versions.root (Versions.execute base (compile D E w idx t).1)).state.tree i).active c q=true := by
  have hmem:=batch_subset D E w idx base t i hi
  rw [Versions.execute_root] at hmem ⊢
  exact ((Mixed.execute_valid base hg hb _).2.2 i).mp hmem

theorem root_valid (A B D E : DFA (Fin σ)) (w : Word (Fin σ)) (rows : RTable.Shared A B D)
    (ranges : Range.Index A) (idx : Range.Index D)
    (base : BoundaryIndex.Tree (Subset.count A) E.stateCount (height w.length))
    (normalBase : BoundaryIndex.Tree D.stateCount E.stateCount (height w.length))
    (hng : Tree.Good normalBase) (hnb : MergeSchedule.Blank normalBase)
    (t : TrieFor w) (incoming : Merge.State (Subset.count A) E.stateCount (height w.length))
    (hi : Valid incoming) :
    Valid (root (go A B D E w rows ranges base t
      (Versions.execute normalBase (compile D E w idx t).1) incoming).saved).subsets := by
  rw [root_subsets]
  exact Lift.importMany_valid_of_live _ _ _ _ hi (batch_live D E w idx normalBase hng hnb t)

theorem root_trans (A B D E : DFA (Fin σ)) (w : Word (Fin σ)) (rows : RTable.Shared A B D)
    (ranges : Range.Index A) (base : BoundaryIndex.Tree (Subset.count A) E.stateCount (height w.length))
    (t : TrieFor w) (s : Versions.Snapshot D.stateCount E.stateCount (height w.length))
    (incoming : Merge.State (Subset.count A) E.stateCount (height w.length))
    (i : Position (height w.length)) :
    (point (root (go A B D E w rows ranges base t s incoming).saved).subsets.tree i).trans=
      (point incoming.tree i).trans := by
  rw [root_subsets]
  exact Lift.importMany_trans _ _ _ _ _

/-- Exact local selected-endpoint recurrence, with rows computed from
the shared bounded-cut index and D colors computed from the trie. -/
theorem root_selected (A B D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g : Nat) (base : BoundaryIndex.Tree (Subset.count A) E.stateCount (height w.length))
    (normalBase : BoundaryIndex.Tree D.stateCount E.stateCount (height w.length))
    (hng : Tree.Good normalBase) (hnb : MergeSchedule.Blank normalBase)
    (t : TrieFor w) (hg : t.Good (reverseText w fallback)) (hn : t.leaves≠[])
    (hv : ∀a,a∈t.leaves→ValidKey g (originalKey w a))
    (incoming : Merge.State (Subset.count A) E.stateCount (height w.length))
    (i : Position (height w.length)) (alpha : Fin A.stateCount) (q : Fin E.stateCount) :
    Subset.Selected A (root (go A B D E w (RTable.prepare A B D w) (Range.build A w) base t
      (Versions.execute normalBase (compile D E w (Range.build D w) t).1) incoming).saved).subsets.tree i alpha q ↔
    Subset.Selected A incoming.tree i alpha q ∨
      (i∈(batch w t (Versions.execute normalBase (compile D E w (Range.build D w) t).1)).positions ∧
        ∃delta,BoundaryIndex.FixedEnd.Predicate A B D w (w.length-(representative w t).start)
          t.depth 0 t.depth alpha delta ∧ Target D E w g t i delta q) := by
  rw [root_subsets,Subset.node_import_selected A B D w fallback t hg hn]
  simp only [Versions.execute_root,Mixed.execute_active normalBase hng hnb,
    compile_active D E w fallback g t hg hn hv]

end REWB.BoundaryApplication.Heavy
