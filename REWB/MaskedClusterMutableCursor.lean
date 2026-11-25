import REWB.MaskedClusterMutableCell

/-! Concrete mutable-source cursor rows and their materialized blocks.
    A source-index snapshot is explicit in every executable routine.
    Ghost arrays occur only in the answer-equivalence lemmas, never in
    a row, matrix or block constructor.
-/
namespace REWB.MaskedCluster.Mutable
open REWB.MaskedFiniteAction
variable {α : Type}

def rowCell (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (ctx : Option (RowContext C E)) (tail : Replay C E) (idx : Index)
    (target : Array Bool) (targetCounts : Array Nat) (window : SourceWindow) (outMode : Bool)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount) : Answer :=
  match ctx with
  | none => ⟨false,1⟩
  | some ctx =>
    if outMode then
      match ctx.over with
      | none => ⟨false,1⟩
      | some maps => pointCell C E maps tail idx target ctx.last window input output
    else
      let pass:=ofStatic (passCell C E ctx.pass input output)
      match ctx.normal with
      | none => pass
      | some maps => either pass (cell C E prepared maps tail ctx.lo ctx.hi idx targetCounts ctx.step ctx.start window input output)

def pointRowCell (C E : DFA α) (ctx : Option (RowContext C E)) (tail : Replay C E)
    (idx : Index) (target : Array Bool) (window : SourceWindow) (outMode : Bool)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount) : Answer :=
  match ctx with
  | none => ⟨false,1⟩
  | some ctx =>
    if outMode then
      match ctx.over with
      | none => ⟨false,1⟩
      | some maps => pointCell C E maps tail idx target ctx.last window input output
    else
      let pass:=ofStatic (passCell C E ctx.pass input output)
      match ctx.normal with
      | none => pass
      | some maps => either pass (pointCell C E maps tail idx target ctx.last window input output)

theorem rowCell_snapshot (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (ctx : Option (RowContext C E)) (tail : Replay C E) (idx : Index) (hv : idx.Valid)
    (target : Array Bool) (targetCounts : Array Nat) (window : SourceWindow) (outMode : Bool)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount)
    (hctx : ∀ row,ctx=some row→0<row.step ∧ idx.step=prepared.K*row.step) :
    (rowCell C E prepared ctx tail idx target targetCounts window outMode input output).answer=
      (REWB.MaskedCluster.rowCell C E prepared ctx tail (snapshot idx) target
        (MaskedProgression.build (snapshot idx) idx.base idx.len idx.step).counts targetCounts idx.base window
        outMode input output).answer := by
  cases ctx with
  | none => rfl
  | some ctx =>
    have hh:=hctx ctx rfl
    cases outMode with
    | true =>
      cases ho : ctx.over <;>
        simp only [rowCell,REWB.MaskedCluster.rowCell,if_true,ho,pointCell_snapshot]
    | false =>
      cases hn : ctx.normal with
      | none => simp only [rowCell,REWB.MaskedCluster.rowCell,Bool.false_eq_true,if_false,hn,ofStatic]
      | some maps =>
        have hc:=cell_snapshot C E prepared maps tail ctx.lo ctx.hi idx hv targetCounts ctx.step ctx.start
          window input output hh.1 hh.2
        rw [←hh.2] at hc
        simpa only [rowCell,REWB.MaskedCluster.rowCell,Bool.false_eq_true,if_false,hn,either,
          REWB.MaskedCluster.either,ofStatic,hc]

theorem pointRowCell_snapshot (C E : DFA α) (ctx : Option (RowContext C E)) (tail : Replay C E)
    (idx : Index) (target : Array Bool) (window : SourceWindow) (outMode : Bool)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount) :
    (pointRowCell C E ctx tail idx target window outMode input output).answer=
      (REWB.MaskedCluster.pointRowCell C E ctx tail (snapshot idx) target window outMode input output).answer := by
  cases ctx with
  | none => rfl
  | some ctx =>
    cases outMode with
    | true => cases ho : ctx.over <;>
        simp only [pointRowCell,REWB.MaskedCluster.pointRowCell,if_true,ho,pointCell_snapshot]
    | false => cases hn : ctx.normal <;>
        simp only [pointRowCell,REWB.MaskedCluster.pointRowCell,Bool.false_eq_true,if_false,hn,either,
          REWB.MaskedCluster.either,ofStatic,pointCell_snapshot]

theorem prepareRow_step (C E : DFA α) (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (s q m H next incoming : Nat) (enabled mode : Bool) (row : RowContext C E)
    (h : (prepareRow C E ci ei s q m H next incoming enabled mode).1=some row) : row.step=q := by
  unfold prepareRow at h
  split at h
  · have he:=Option.some.inj h
    exact congrArg RowContext.step he.symm
  · cases h

def materialize {m : Nat} (f : Fin m→Fin m→Answer) : MatrixResult m :=
  let results:=Vector.ofFn fun i=>Vector.ofFn fun j=>let out:=f i j; (out.answer,out.work)
  ⟨Vector.ofFn (fun i=>Vector.ofFn (fun j=>((results.get i).get j).1)),
    (List.ofFn (fun i=>BoundaryIndex.Counted.rowWork (results.get i))).sum⟩

theorem materialize_get {m : Nat} (f : Fin m→Fin m→Answer) (i j : Fin m) :
    (((materialize f).cells.get i).get j)=(f i j).answer := by
  simp only [materialize,BoundaryIndex.Table.get_ofFn]

theorem materialize_work {m : Nat} (f : Fin m→Fin m→Answer) (budget : Nat)
    (h : ∀ i j,(f i j).work≤budget) : (materialize f).work≤m*(m*(budget+1)) := by
  apply sum_ofFn_le
  intro i
  apply rowWork_le
  intro j
  simpa only [BoundaryIndex.Table.get_ofFn] using h i j

def rowMatrix (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (ctx : Option (RowContext C E)) (tail : Replay C E) (idx : Index)
    (target : Array Bool) (targetCounts : Array Nat) (window : SourceWindow) :
    CursorRow (MaskedClusterStage.dfa C E).stateCount :=
  ⟨materialize (fun i j=>rowCell C E prepared ctx tail idx target targetCounts window false
      (MaskedClusterStage.decode C E i) (MaskedClusterStage.decode C E j)),
    materialize (fun i j=>rowCell C E prepared ctx tail idx target targetCounts window true
      (MaskedClusterStage.decode C E i) (MaskedClusterStage.decode C E j))⟩

def pointRowMatrix (C E : DFA α) (ctx : Option (RowContext C E)) (tail : Replay C E)
    (idx : Index) (target : Array Bool) (window : SourceWindow) :
    CursorRow (MaskedClusterStage.dfa C E).stateCount :=
  ⟨materialize (fun i j=>pointRowCell C E ctx tail idx target window false
      (MaskedClusterStage.decode C E i) (MaskedClusterStage.decode C E j)),
    materialize (fun i j=>pointRowCell C E ctx tail idx target window true
      (MaskedClusterStage.decode C E i) (MaskedClusterStage.decode C E j))⟩

theorem rowMatrix_get (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (ctx : Option (RowContext C E)) (tail : Replay C E) (idx : Index)
    (target : Array Bool) (targetCounts : Array Nat) (window : SourceWindow) (mode : Bool)
    (i j : Fin (MaskedClusterStage.dfa C E).stateCount) :
    ((((rowMatrix C E prepared ctx tail idx target targetCounts window).get mode).cells.get i).get j)=
      (rowCell C E prepared ctx tail idx target targetCounts window mode
        (MaskedClusterStage.decode C E i) (MaskedClusterStage.decode C E j)).answer := by
  cases mode <;> exact materialize_get _ _ _

theorem pointRowMatrix_get (C E : DFA α) (ctx : Option (RowContext C E)) (tail : Replay C E)
    (idx : Index) (target : Array Bool) (window : SourceWindow) (mode : Bool)
    (i j : Fin (MaskedClusterStage.dfa C E).stateCount) :
    ((((pointRowMatrix C E ctx tail idx target window).get mode).cells.get i).get j)=
      (pointRowCell C E ctx tail idx target window mode
        (MaskedClusterStage.decode C E i) (MaskedClusterStage.decode C E j)).answer := by
  cases mode <;> exact materialize_get _ _ _

def blocks (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (rows : Option (RowContext C E)×Option (RowContext C E)) (tail : Replay C E) (idx : Index)
    (target : Array Bool) (targetCounts : Array Nat) (window : SourceWindow) :
    CursorBlocks (MaskedClusterStage.dfa C E).stateCount :=
  ⟨rowMatrix C E prepared rows.1 tail idx target targetCounts window,
    rowMatrix C E prepared rows.2 tail idx target targetCounts window⟩

def pointBlocks (C E : DFA α) (rows : Option (RowContext C E)×Option (RowContext C E)) (tail : Replay C E)
    (idx : Index) (target : Array Bool) (window : SourceWindow) :
    CursorBlocks (MaskedClusterStage.dfa C E).stateCount :=
  ⟨pointRowMatrix C E rows.1 tail idx target window,pointRowMatrix C E rows.2 tail idx target window⟩

theorem blocks_snapshot (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (rows : Option (RowContext C E)×Option (RowContext C E)) (tail : Replay C E) (idx : Index) (hv : idx.Valid)
    (target : Array Bool) (targetCounts : Array Nat) (window : SourceWindow) (input output : Bool)
    (i j : Fin (MaskedClusterStage.dfa C E).stateCount)
    (ha : ∀ row,rows.1=some row→0<row.step ∧ idx.step=prepared.K*row.step)
    (hb : ∀ row,rows.2=some row→0<row.step ∧ idx.step=prepared.K*row.step) :
    ((((blocks C E prepared rows tail idx target targetCounts window).get input output).cells.get i).get j)=
      ((((REWB.MaskedCluster.blocks C E prepared rows tail (snapshot idx) target
        (MaskedProgression.build (snapshot idx) idx.base idx.len idx.step).counts targetCounts idx.base window).get input output).cells.get i).get j) := by
  cases input <;>
    simp only [blocks,REWB.MaskedCluster.blocks,CursorBlocks.get,Bool.false_eq_true,if_false,if_true,
      rowMatrix_get,REWB.MaskedCluster.rowMatrix_get] <;>
    apply rowCell_snapshot <;> assumption

theorem pointBlocks_snapshot (C E : DFA α) (rows : Option (RowContext C E)×Option (RowContext C E)) (tail : Replay C E)
    (idx : Index) (target : Array Bool) (window : SourceWindow) (input output : Bool)
    (i j : Fin (MaskedClusterStage.dfa C E).stateCount) :
    ((((pointBlocks C E rows tail idx target window).get input output).cells.get i).get j)=
      ((((REWB.MaskedCluster.pointBlocks C E rows tail (snapshot idx) target window).get input output).cells.get i).get j) := by
  cases input <;>
    simp only [pointBlocks,REWB.MaskedCluster.pointBlocks,CursorBlocks.get,Bool.false_eq_true,if_false,if_true,
      pointRowMatrix_get,REWB.MaskedCluster.pointRowMatrix_get] <;> exact pointRowCell_snapshot _ _ _ _ _ _ _ _ _ _

end REWB.MaskedCluster.Mutable
