import REWB.MaskedClusterPointCursor

/-! Four concrete cursor/stage blocks, their flat finite-state matrix,
    and actual materialized Boolean composition. Flattening uses two
    contiguous copies of the stage codes; no mode or state is omitted.
-/
namespace REWB.MaskedCluster
open REWB.MaskedFiniteAction
variable {α : Type} {m : Nat}

structure CursorBlocks (m : Nat) where
  normal : CursorRow m
  over : CursorRow m

def CursorBlocks.get (blocks : CursorBlocks m) (input output : Bool) : MatrixResult m :=
  (if input then blocks.over else blocks.normal).get output

def prepareRows (C E : DFA α) (ci : BoundaryApplication.Range.Index C)
    (ei : BoundaryApplication.Range.Index E) (s q m H next incoming : Nat) (enabled : Bool) :
    (Option (RowContext C E)×Option (RowContext C E))×Nat :=
  let a:=prepareRow C E ci ei s q m H next incoming enabled false
  let b:=prepareRow C E ci ei s q m H next incoming enabled true
  ((a.1,b.1),a.2+b.2)

def preparePointRows (C E : DFA α) (ci : BoundaryApplication.Range.Index C)
    (ei : BoundaryApplication.Range.Index E) (s H next incoming : Nat) (enabled : Bool) :
    (Option (RowContext C E)×Option (RowContext C E))×Nat :=
  let a:=preparePointRow C E ci ei s H next incoming enabled false
  let b:=preparePointRow C E ci ei s H next incoming enabled true
  ((a.1,b.1),a.2+b.2)

def blocks (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (rows : Option (RowContext C E)×Option (RowContext C E)) (tail : Replay C E)
    (source target : Array Bool) (sourceCounts targetCounts : Array Nat)
    (base : Nat) (window : SourceWindow) : CursorBlocks (MaskedClusterStage.dfa C E).stateCount :=
  ⟨rowMatrix C E prepared rows.1 tail source target sourceCounts targetCounts base window,
    rowMatrix C E prepared rows.2 tail source target sourceCounts targetCounts base window⟩

def pointBlocks (C E : DFA α) (rows : Option (RowContext C E)×Option (RowContext C E))
    (tail : Replay C E) (source target : Array Bool) (window : SourceWindow) :
    CursorBlocks (MaskedClusterStage.dfa C E).stateCount :=
  ⟨pointRowMatrix C E rows.1 tail source target window,pointRowMatrix C E rows.2 tail source target window⟩

def code (m : Nat) (mode : Bool) (state : Fin m) : Fin (2*m) :=
  ⟨if mode then m+state.val else state.val,by have h:=state.isLt; split <;> omega⟩

def codeMode (m : Nat) (i : Fin (2*m)) : Bool := decide (m≤i.val)

def codeState (m : Nat) (i : Fin (2*m)) : Fin m :=
  if h : m≤i.val then ⟨i.val-m,by have hi:=i.isLt; omega⟩
  else ⟨i.val,by omega⟩

theorem codeMode_code (mode : Bool) (state : Fin m) : codeMode m (code m mode state)=mode := by
  have hs:=state.isLt
  cases mode <;> simp only [codeMode,code,Bool.false_eq_true,if_false,if_true]
  · have hh : ¬m≤state.val := by omega
    simp only [hh,decide_false]
  · have hh : m≤m+state.val := by omega
    simp only [hh,decide_true]

theorem codeState_code (mode : Bool) (state : Fin m) : codeState m (code m mode state)=state := by
  apply Fin.ext
  have hs:=state.isLt
  cases mode <;> simp only [codeState,code,Bool.false_eq_true,if_false,if_true]
  · have hh : ¬m≤state.val := by omega
    simp [hh]
  · have hh : m≤m+state.val := by omega
    simp only [hh,dif_pos,Nat.add_sub_cancel_left]

theorem code_decode (i : Fin (2*m)) : code m (codeMode m i) (codeState m i)=i := by
  apply Fin.ext
  by_cases h : m≤i.val
  · simp only [code,codeMode,codeState,h,decide_true,if_true,dif_pos]
    omega
  · simp [code,codeMode,codeState,h]

/-- Each copied cell charges two indexed reads and eight fixed index/
    mode operations. `materialize` also charges the output-cell write. -/
def flattenResult (blocks : CursorBlocks m) : MatrixResult (2*m) :=
  materialize fun i j=>
    ⟨(((blocks.get (codeMode m i) (codeMode m j)).cells.get (codeState m i)).get (codeState m j)),2,8⟩

def flatten (blocks : CursorBlocks m) : Matrix (2*m) := (flattenResult blocks).cells

theorem flattenResult_work (blocks : CursorBlocks m) :
    (flattenResult blocks).work=(2*m)*((2*m)*11) := by
  simp only [flattenResult,materialize,BoundaryIndex.Counted.rowWork,BoundaryIndex.Table.get_ofFn]
  simp only [BoundaryIndex.Counted.sum_ofFn_const]

theorem flatten_get (blocks : CursorBlocks m) (input output : Bool) (i j : Fin m) :
    (((flatten blocks).get (code m input i)).get (code m output j))=
      (((blocks.get input output).cells.get i).get j) := by
  simp only [flatten,flattenResult,materialize_get,codeMode_code,codeState_code]

def blockTable (blocks : CursorBlocks m) : Table 1 (2*m) :=
  ⟨Vector.ofFn (fun _=>flatten blocks)⟩

theorem blockTable_get (blocks : CursorBlocks m) (input output : Bool) (i j : Fin m) :
    (blockTable blocks).view 0 (code m input i) (code m output j)=
      (((blocks.get input output).cells.get i).get j) := by
  simp only [blockTable,Table.view,BoundaryIndex.Table.get_ofFn,flatten_get]

/-- This calls the already counted, materialized finite-state matrix
    multiplication, rather than returning a deferred composition. -/
def composeBlocks (a b : CursorBlocks m) : Table 1 (2*m)×Nat :=
  let fa:=flattenResult a
  let fb:=flattenResult b
  let out:=Counted.mul ⟨Vector.ofFn (fun _=>fa.cells)⟩ ⟨Vector.ofFn (fun _=>fb.cells)⟩
  (out.1,fa.work+fb.work+out.2+2)

theorem composeBlocks_correct (a b : CursorBlocks m) (input output : Bool) (i j : Fin m) :
    (composeBlocks a b).1.view 0 (code m input i) (code m output j)=true ↔
      ∃ midMode midState,(((a.get input midMode).cells.get i).get midState)=true ∧
        (((b.get midMode output).cells.get midState).get j)=true := by
  change (Counted.mul (blockTable a) (blockTable b)).1.view 0
    (code m input i) (code m output j)=true ↔ _
  rw [Counted.mul_view]
  change FiniteRelation.comp (FiniteRelation.finEnum (2*m)) (blockTable a |>.view 0)
    (blockTable b |>.view 0) (code m input i) (code m output j)=true ↔ _
  rw [FiniteRelation.comp_true]
  constructor
  · rintro ⟨mid,ha,hb⟩
    rw [←code_decode mid] at ha hb
    rw [blockTable_get] at ha hb
    exact ⟨codeMode m mid,codeState m mid,ha,hb⟩
  · rintro ⟨mode,state,ha,hb⟩
    exact ⟨code m mode state,by rwa [blockTable_get],by rwa [blockTable_get]⟩

theorem composeBlocks_work (a b : CursorBlocks m) :
    (composeBlocks a b).2=2*((2*m)*((2*m)*11))+(2*m)*((2*m)*(2*m+1))+2 := by
  simp only [composeBlocks,flattenResult_work,Counted.mul_steps,Nat.one_mul]
  omega

end REWB.MaskedCluster
