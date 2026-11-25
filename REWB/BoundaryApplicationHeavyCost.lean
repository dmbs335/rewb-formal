import REWB.BoundaryApplicationHeavy

/-! Actual heavy-path construction counters. The heterogeneous imports
are exactly the existing mixed construction's light imports plus one
import for every target terminal. All masses and list sizes used by the
executable pass are cached fields of already constructed D versions. -/
namespace REWB.BoundaryApplication.Heavy
open REWB.BoundaryIndex
open REWB.BoundaryIndex.Merge
variable {σ : Nat}

theorem compile_node (D E : DFA (Fin σ)) (w : Word (Fin σ)) (idx : Range.Index D)
    (key : KeyFor w) (depth : Nat) (l r : TrieFor w) :
    (compile D E w idx (.node key depth l r)).1=
      .node (edge D w idx depth l).map (edge D w idx depth r).map
        (compile D E w idx l).1 (compile D E w idx r).1 := rfl

theorem heavyRight_execute {k m h : Nat} (base : BoundaryIndex.Tree k m h)
    (g f : Vector (Fin k) k) (p q : Mixed.Program k m h) :
    heavyRight (Versions.execute base (.node g f p q))=
      decide ((Mixed.execute base p).totalMass≤(Mixed.execute base q).totalMass) := by
  simp only [heavyRight,execute_left,execute_right,Versions.execute_root]

theorem lightState_execute {k m h : Nat} (base : BoundaryIndex.Tree k m h)
    (g f : Vector (Fin k) k) (p q : Mixed.Program k m h) :
    lightState (Versions.execute base (.node g f p q))=
      if (Mixed.execute base p).totalMass≤(Mixed.execute base q).totalMass then
        (Mixed.execute base p).state else (Mixed.execute base q).state := by
  simp only [lightState,heavyRight_execute,execute_left,execute_right,Versions.execute_root,
    decide_eq_true_eq]

theorem node_imports {k m h : Nat} (base : BoundaryIndex.Tree k m h)
    (g f : Vector (Fin k) k) (p q : Mixed.Program k m h) :
    (Mixed.execute base (.node g f p q)).transfers=
      (Mixed.execute base p).transfers+(Mixed.execute base q).transfers+
        (lightState (Versions.execute base (.node g f p q))).cachedSize := by
  simp only [Mixed.execute,lightState_execute,Mixed.imported,Merge.recolor]
  split <;> rfl

theorem node_size {k m h : Nat} (base : BoundaryIndex.Tree k m h)
    (g f : Vector (Fin k) k) (p q : Mixed.Program k m h) :
    (Mixed.execute base (.node g f p q)).state.cachedSize=
      (Mixed.execute base p).state.cachedSize+(Mixed.execute base q).state.cachedSize := by
  simp only [Mixed.execute_size,Mixed.targetPositions,List.length_append]

theorem go_imports (A B D E : DFA (Fin σ)) (w : Word (Fin σ)) (rows : RTable.Shared A B D)
    (ranges : Range.Index A) (idx : Range.Index D)
    (base : BoundaryIndex.Tree (Subset.count A) E.stateCount (height w.length))
    (normalBase : BoundaryIndex.Tree D.stateCount E.stateCount (height w.length))
    (t : TrieFor w) (incoming : Merge.State (Subset.count A) E.stateCount (height w.length)) :
    (go A B D E w rows ranges base t
      (Versions.execute normalBase (compile D E w idx t).1) incoming).imports=
      (Mixed.execute normalBase (compile D E w idx t).1).transfers+
        (Mixed.execute normalBase (compile D E w idx t).1).state.cachedSize := by
  induction t generalizing incoming with
  | empty => rfl
  | leaf key => cases hr : key.record <;> simp only [go,compile,hr,Versions.execute_root,Mixed.execute,Nat.zero_add]
  | node key depth l r ihl ihr =>
    simp only [go,compile_node,execute_left,execute_right,ihl,ihr]
    have ht:=node_imports normalBase (edge D w idx depth l).map (edge D w idx depth r).map
      (compile D E w idx l).1 (compile D E w idx r).1
    have hs:=node_size normalBase (edge D w idx depth l).map (edge D w idx depth r).map
      (compile D E w idx l).1 (compile D E w idx r).1
    rw [ht,hs]
    omega

theorem imports_bound (A B D E : DFA (Fin σ)) (w : Word (Fin σ)) (rows : RTable.Shared A B D)
    (ranges : Range.Index A) (idx : Range.Index D)
    (base : BoundaryIndex.Tree (Subset.count A) E.stateCount (height w.length))
    (normalBase : BoundaryIndex.Tree D.stateCount E.stateCount (height w.length))
    (fallback : Fin σ) (t : TrieFor w) (hg : t.Good (reverseText w fallback)) (hn : t.leaves≠[])
    (incoming : Merge.State (Subset.count A) E.stateCount (height w.length)) :
    (go A B D E w rows ranges base t (Versions.execute normalBase (compile D E w idx t).1) incoming).imports≤
      t.leaves.length*t.leaves.length.log2+t.leaves.length := by
  rw [go_imports]
  have ht:=Mixed.transfers_bound normalBase (compile D E w idx t).1
  have hs:=Mixed.execute_targets_le_mass normalBase (compile D E w idx t).1
  rw [Mixed.execute_mass] at hs
  rw [compile_mass D E w fallback idx t hg hn] at ht hs
  omega

def rowBudget (A _B D : DFA (Fin σ)) (n : Nat) : Nat :=
  D.stateCount*(A.stateCount*6)+8*(D.stateCount*(A.stateCount*(3*(n.log2+2))))+D.stateCount

def advanceBudget (A E : DFA (Fin σ)) (n : Nat) : Nat :=
  A.stateCount+8*(n.log2+2)+1+Subset.count A+Tree.recolorBudget (Subset.count A) E.stateCount+2

def nodeBudget (A B D E : DFA (Fin σ)) (n : Nat) : Nat :=
  rowBudget A B D n+advanceBudget A E n+14

theorem advance_steps (A E : DFA (Fin σ)) (w : Word (Fin σ)) (parent : Nat) (child : TrieFor w)
    (hp : parent≤child.depth) (s : Merge.State (Subset.count A) E.stateCount (height w.length)) :
    (advance A E w (Range.build A w) parent child s).2≤advanceBudget A E w.length := by
  have he:=edge_work A w parent child hp
  have hr:=Merge.recolor_steps (Colors.preimageMap A (edge A w (Range.build A w) parent child).map) s
  change (Merge.recolor (Colors.preimageMap A (edge A w (Range.build A w) parent child).map) s).2≤
    Tree.recolorBudget (Subset.count A) E.stateCount+1 at hr
  simp only [advance,advanceBudget]
  omega

theorem batch_size (D E : DFA (Fin σ)) (w : Word (Fin σ)) (idx : Range.Index D)
    (base : BoundaryIndex.Tree D.stateCount E.stateCount (height w.length)) (t : TrieFor w) :
    (batch w t (Versions.execute base (compile D E w idx t).1)).cachedSize=
      (batch w t (Versions.execute base (compile D E w idx t).1)).positions.length := by
  cases t with
  | empty => rfl
  | leaf key =>
    simp only [batch,Versions.execute_root,Mixed.execute_size,Mixed.execute_length]
  | node key depth l r =>
    simp only [batch,compile_node,lightState_execute]
    split <;> simp only [Mixed.execute_size,Mixed.execute_length]

theorem go_steps (A B D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (idx : Range.Index D)
    (base : BoundaryIndex.Tree (Subset.count A) E.stateCount (height w.length))
    (normalBase : BoundaryIndex.Tree D.stateCount E.stateCount (height w.length))
    (t : TrieFor w) (hg : t.Good (reverseText w fallback)) (hn : t.leaves≠[])
    (incoming : Merge.State (Subset.count A) E.stateCount (height w.length)) :
    (go A B D E w (RTable.prepare A B D w) (Range.build A w) base t
      (Versions.execute normalBase (compile D E w idx t).1) incoming).work≤
    t.nodes*nodeBudget A B D E w.length+
      (go A B D E w (RTable.prepare A B D w) (Range.build A w) base t
        (Versions.execute normalBase (compile D E w idx t).1) incoming).imports*
        Lift.budget D.stateCount (Subset.count A) E.stateCount (height w.length) := by
  induction t generalizing incoming with
  | empty => exact False.elim (hn rfl)
  | leaf key =>
    have hr:=RTable.node_work A B D w fallback (.leaf key) hg hn
    have hi:=Lift.importMany_steps (RTable.node A B D w (RTable.prepare A B D w) (.leaf key)).map
      (Versions.root (Versions.execute normalBase (compile D E w idx (.leaf key)).1)).state.tree
      (Versions.root (Versions.execute normalBase (compile D E w idx (.leaf key)).1)).state.positions incoming
    have hs:=batch_size D E w idx normalBase (.leaf key)
    change (Versions.root (Versions.execute normalBase (compile D E w idx (.leaf key)).1)).state.cachedSize=
      (Versions.root (Versions.execute normalBase (compile D E w idx (.leaf key)).1)).state.positions.length at hs
    rw [← hs] at hi
    simp only [go,BoundaryTrie.Tree.nodes,Nat.one_mul,nodeBudget,rowBudget]
    simp only [Subset.count] at hi ⊢
    omega
  | node key depth l r ihl ihr =>
    let t : TrieFor w:=.node key depth l r
    let s:=Versions.execute normalBase (compile D E w idx t).1
    let rr:=RTable.node A B D w (RTable.prepare A B D w) t
    let out:=Lift.importMany rr.map (Versions.root s).state.tree (lightState s).positions incoming
    let next:=advance A E w (Range.build A w) depth (if heavyRight s then r else l) out.1
    let il:=if heavyRight s then blank base else next.1
    let ir:=if heavyRight s then next.1 else blank base
    let a:=go A B D E w (RTable.prepare A B D w) (Range.build A w) base l (left s) il
    let b:=go A B D E w (RTable.prepare A B D w) (Range.build A w) base r (right s) ir
    have hl:=ihl hg.1 hg.2.2.1 il
    have hh:=ihr hg.2.1 hg.2.2.2.1 ir
    change a.work≤l.nodes*nodeBudget A B D E w.length+
      a.imports*Lift.budget D.stateCount (Subset.count A) E.stateCount (height w.length) at hl
    change b.work≤r.nodes*nodeBudget A B D E w.length+
      b.imports*Lift.budget D.stateCount (Subset.count A) E.stateCount (height w.length) at hh
    have hrow:=RTable.node_work A B D w fallback t hg hn
    change rr.work A D≤rowBudget A B D w.length at hrow
    have hi:=Lift.importMany_steps rr.map (Versions.root s).state.tree (lightState s).positions incoming
    have hs:=batch_size D E w idx normalBase t
    change (lightState s).cachedSize=(lightState s).positions.length at hs
    rw [← hs] at hi
    change out.2≤(lightState s).cachedSize*Lift.budget D.stateCount (Subset.count A) E.stateCount (height w.length) at hi
    have hd:=BoundaryTrie.Tree.edge_depths (reverseText w fallback) key depth l r hg
    have he:=advance_steps A E w depth (if heavyRight s then r else l)
      (by split <;> first | exact hd.2 | exact hd.1) out.1
    change next.2≤advanceBudget A E w.length at he
    change a.work+b.work+out.2+rr.work A D+next.2+14≤
      (l.nodes+r.nodes+1)*nodeBudget A B D E w.length+
        (a.imports+b.imports+(lightState s).cachedSize)*Lift.budget D.stateCount (Subset.count A) E.stateCount (height w.length)
    simp only [Nat.add_mul,Nat.one_mul]
    have hnode : rr.work A D+next.2+14≤nodeBudget A B D E w.length := by
      unfold nodeBudget
      omega
    omega

theorem work_bound (A B D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (idx : Range.Index D)
    (base : BoundaryIndex.Tree (Subset.count A) E.stateCount (height w.length))
    (normalBase : BoundaryIndex.Tree D.stateCount E.stateCount (height w.length))
    (t : TrieFor w) (hg : t.Good (reverseText w fallback)) (hn : t.leaves≠[])
    (incoming : Merge.State (Subset.count A) E.stateCount (height w.length)) :
    (go A B D E w (RTable.prepare A B D w) (Range.build A w) base t
      (Versions.execute normalBase (compile D E w idx t).1) incoming).work≤
      t.nodes*nodeBudget A B D E w.length+
        (t.leaves.length*t.leaves.length.log2+t.leaves.length)*
          Lift.budget D.stateCount (Subset.count A) E.stateCount (height w.length) := by
  have hw:=go_steps A B D E w fallback idx base normalBase t hg hn incoming
  have hi:=Nat.mul_le_mul_right (Lift.budget D.stateCount (Subset.count A) E.stateCount (height w.length))
    (imports_bound A B D E w (RTable.prepare A B D w) (Range.build A w) idx base normalBase fallback t hg hn incoming)
  omega

/-- Specification of the saved heavy choices; it is not evaluated by
the construction or by address-based queries. -/
def lightHeight {A D E : DFA (Fin σ)} {n : Nat} : Saved A D E n→Nat
  | .leaf _ _ => 0
  | .node _ chooseRight l r =>
    if chooseRight then max (lightHeight l+1) (lightHeight r)
      else max (lightHeight l) (lightHeight r+1)

theorem go_lightHeight (A B D E : DFA (Fin σ)) (w : Word (Fin σ)) (rows : RTable.Shared A B D)
    (ranges : Range.Index A) (idx : Range.Index D)
    (base : BoundaryIndex.Tree (Subset.count A) E.stateCount (height w.length))
    (normalBase : BoundaryIndex.Tree D.stateCount E.stateCount (height w.length))
    (t : TrieFor w) (incoming : Merge.State (Subset.count A) E.stateCount (height w.length)) :
    lightHeight (go A B D E w rows ranges base t
      (Versions.execute normalBase (compile D E w idx t).1) incoming).saved=
      Mixed.lightHeight (compile D E w idx t).1 := by
  induction t generalizing incoming with
  | empty => rfl
  | leaf key => cases hr : key.record <;> simp only [go,compile,hr,lightHeight,Mixed.lightHeight]
  | node key depth l r ihl ihr =>
    simp only [go,compile_node,lightHeight,execute_left,execute_right,ihl,ihr,
      heavyRight_execute,Mixed.execute_mass,decide_eq_true_eq,Mixed.lightHeight]

theorem lightHeight_bound (A B D E : DFA (Fin σ)) (w : Word (Fin σ)) (rows : RTable.Shared A B D)
    (ranges : Range.Index A) (idx : Range.Index D)
    (base : BoundaryIndex.Tree (Subset.count A) E.stateCount (height w.length))
    (normalBase : BoundaryIndex.Tree D.stateCount E.stateCount (height w.length))
    (fallback : Fin σ) (t : TrieFor w) (hg : t.Good (reverseText w fallback)) (hn : t.leaves≠[])
    (incoming : Merge.State (Subset.count A) E.stateCount (height w.length)) :
    lightHeight (go A B D E w rows ranges base t
      (Versions.execute normalBase (compile D E w idx t).1) incoming).saved≤t.leaves.length.log2 := by
  rw [go_lightHeight]
  have hh:=Mixed.lightHeight_bound (compile D E w idx t).1
  rw [compile_mass D E w fallback idx t hg hn] at hh
  exact hh

end REWB.BoundaryApplication.Heavy
