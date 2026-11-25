import REWB.BoundaryIndexMergeSchedule

/-! One-time materialized static-text preparation for the persistent merge
schedule. All leaf versions share the same prepared base. The executable
run has no supplied live-position list, semantic answer oracle, or supplied
cost function. Constructing the input merge program is a separate task. -/
namespace REWB.BoundaryIndex.MergeBuild
open REWB.BoundaryIndex.Merge
open REWB.BoundaryIndex.MergeSchedule
variable {k m h : Nat}

/-- A static cell has its actual text transition and no active endpoint. -/
def staticCell (tr : Vector (Fin m) m) : Table k m :=
  ⟨tr,Vector.ofFn (fun _=>Vector.ofFn (fun _=>false))⟩

/-- Build the balanced text tree once, charging input-cell materialization
as well as the tree's own table/position preparation. -/
def prepare (rows : Array (Vector (Fin m) m)) (h : Nat) : Tree k m h×Nat :=
  let out := Tree.build (rows.map (staticCell (k:=k))) h 0
  (out.1,rows.size*(k*m+1)+out.2)

theorem point_build (cells : Array (Table k m)) (h : Nat) (i : Position h) :
    point (Tree.build cells h 0).1 i=(cells[i.val]?.getD Table.one).view := by
  have hh := Tree.get_correct (Tree.build cells h 0).1 i.val i.isLt
  rw [Tree.build_leaves,Tree.cells,List.getElem?_map,List.getElem?_range' i.isLt] at hh
  simpa only [Nat.one_mul,Nat.zero_add,Option.map,Option.some.injEq,point] using hh.symm

theorem prepare_good (rows : Array (Vector (Fin m) m)) (h : Nat) :
    Tree.Good (prepare (k:=k) rows h).1 := Tree.build_good _ _ _

theorem prepare_blank (rows : Array (Vector (Fin m) m)) (h : Nat) :
    Blank (prepare (k:=k) rows h).1 := by
  intro i c q
  change (point (Tree.build (rows.map (staticCell (k:=k))) h 0).1 i).active c q=false
  rw [point_build,Array.getElem?_map]
  cases he : rows[i.val]? with
  | none => simp only [Option.map,Option.getD,Table.view_one,View.one]
  | some tr => simp only [Option.map,Option.getD,staticCell,Table.view,Table.get_ofFn]

theorem prepare_trans (rows : Array (Vector (Fin m) m)) (h : Nat) (i : Position h) :
    (point (prepare (k:=k) rows h).1 i).trans=(rows[i.val]?.getD (Vector.ofFn id)).get := by
  change (point (Tree.build (rows.map (staticCell (k:=k))) h 0).1 i).trans=_
  rw [point_build,Array.getElem?_map]
  cases he : rows[i.val]? with
  | none =>
    simp only [Option.map,Option.getD,Table.view_one,View.one]
    funext q
    simp only [Table.get_ofFn,id_eq]
  | some tr => rfl

theorem prepare_steps (rows : Array (Vector (Fin m) m)) (h : Nat) :
    (prepare (k:=k) rows h).2+Tree.joinBudget k m=
      rows.size*(k*m+1)+2^h*(Tree.joinBudget k m+Tree.leafBudget k m) := by
  have hh := Tree.build_steps (rows.map (staticCell (k:=k))) h 0
  change rows.size*(k*m+1)+(Tree.build _ h 0).2+Tree.joinBudget k m=_
  rw [Nat.add_assoc,hh]

/-- Execute the actual decorated merge schedule over a single shared base. -/
def run (rows : Array (Vector (Fin m) m)) (p : Program k m h) : Result k m h :=
  let base := prepare rows h
  let out := execute base.1 p
  {out with steps:=base.2+out.steps}

theorem run_valid (rows : Array (Vector (Fin m) m)) (p : Program k m h) :
    Valid (run rows p).state := execute_valid _ (prepare_good _ _) (prepare_blank _ _) _

theorem run_active (rows : Array (Vector (Fin m) m)) (p : Program k m h)
    (i : Position h) (c : Fin k) (q : Fin m) :
    (point (run rows p).state.tree i).active c q=true ↔ MergeSchedule.Active p i c q :=
  execute_active _ (prepare_good _ _) (prepare_blank _ _) _ _ _ _

theorem run_trans (rows : Array (Vector (Fin m) m)) (p : Program k m h) (i : Position h) :
    (point (run rows p).state.tree i).trans=(rows[i.val]?.getD (Vector.ofFn id)).get := by
  change (point (execute (prepare rows h).1 p).state.tree i).trans=_
  rw [execute_trans,prepare_trans]

theorem run_perm (rows : Array (Vector (Fin m) m)) (p : Program k m h) :
    (run rows p).state.positions.Perm (positions p) := execute_perm _ _

theorem run_nodup (rows : Array (Vector (Fin m) m)) (p : Program k m h) (hp : (positions p).Nodup) :
    (run rows p).state.positions.Nodup := execute_nodup _ _ hp

theorem run_transfers (rows : Array (Vector (Fin m) m)) (p : Program k m h) :
    (run rows p).transfers=MaskedEventBudget.lightVolume (shape p) := execute_transfers _ _

theorem run_steps (rows : Array (Vector (Fin m) m)) (p : Program k m h) :
    (run rows p).steps≤rows.size*(k*m+1)+2^h*(Tree.joinBudget k m+Tree.leafBudget k m)+
      MaskedEventBudget.size (shape p)*(seedBudget k m h+nodeBudget k m)+
      (MaskedEventBudget.size (shape p)*Nat.log2 (MaskedEventBudget.size (shape p)))*importBudget k m h := by
  have hp := prepare_steps (k:=k) rows h
  have hh := execute_bound (prepare rows h).1 p
  change (prepare rows h).2+(execute (prepare rows h).1 p).steps≤_
  omega

/-- At the automatic text height, static preparation is linear in the
array size and the schedule's import factor is logarithmic in that size. -/
theorem run_auto_steps (rows : Array (Vector (Fin m) m))
    (p : Program k m (Tree.heightFor rows.size)) :
    (run rows p).steps≤rows.size*(k*m+1)+2*(rows.size+1)*(Tree.joinBudget k m+Tree.leafBudget k m)+
      MaskedEventBudget.size (shape p)*(seedBudget k m (Tree.heightFor rows.size)+nodeBudget k m)+
      (MaskedEventBudget.size (shape p)*Nat.log2 (MaskedEventBudget.size (shape p)))*
        importBudget k m (Tree.heightFor rows.size) := by
  have hh := run_steps rows p
  have hc := Nat.mul_le_mul_right (Tree.joinBudget k m+Tree.leafBudget k m) (Tree.capacity_upper rows.size)
  omega

end REWB.BoundaryIndex.MergeBuild
