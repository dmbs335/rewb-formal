import REWB.PeriodicConstructionClusterCell

/-! Materialize each actual counted compiler result once. The first
component retains the frozen matrix and its old ledger exactly; the
second component also counts the finite construction and table passes.
No second execution of a cell is used to recover its old cost. -/
namespace REWB.PeriodicConstruction.Cluster
open REWB.PeriodicConstruction REWB.MaskedCluster
variable {α : Type} {m : Nat}

theorem sum_le_sum_add (n : Nat) (f g : Fin n→Nat) (C : Nat)
    (h : ∀i,f i≤g i+C) : (List.ofFn f).sum≤(List.ofFn g).sum+n*C := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hh:=h 0
    have ht:=ih (fun i=>f i.succ) (fun i=>g i.succ) (fun i=>h i.succ)
    simp only [List.ofFn_succ,List.sum_cons,Nat.add_mul,Nat.one_mul]
    omega

def materialize (f : Fin m→Fin m→Result Mutable.Answer) : Result (MatrixResult m) :=
  let results:=Vector.ofFn (fun i=>Vector.ofFn (f i))
  let bits:=Vector.ofFn (fun i=>Vector.ofFn (fun j=>((results.get i).get j).1.answer))
  let oldWork:=(List.ofFn (fun i=>(List.ofFn (fun j=>((results.get i).get j).1.work+1)).sum)).sum
  let fullWork:=(List.ofFn (fun i=>(List.ofFn (fun j=>((results.get i).get j).2+8)).sum)).sum
  (⟨bits,oldWork⟩,fullWork+4*m+3)

theorem materialize_value (f : Fin m→Fin m→Result Mutable.Answer) :
    (materialize f).1=Mutable.materialize (fun i j=>(f i j).1) := by
  simp only [materialize,Mutable.materialize,BoundaryIndex.Counted.rowWork,BoundaryIndex.Table.get_ofFn]

def matrixExtra (m C : Nat) : Nat := m*(m*(C+8))+4*m+3

theorem materialize_extra (f : Fin m→Fin m→Result Mutable.Answer) (C : Nat)
    (h : ∀i j,(f i j).2≤(f i j).1.work+C) :
    (materialize f).2≤(Mutable.materialize (fun i j=>(f i j).1)).work+matrixExtra m C := by
  have hi (i : Fin m) :
      (List.ofFn (fun j=>(f i j).2+8)).sum≤
      (List.ofFn (fun j=>(f i j).1.work+1)).sum+m*(C+8) := by
    apply sum_le_sum_add
    intro j
    have hh:=h i j
    omega
  have hh:=sum_le_sum_add m _ _ (m*(C+8)) hi
  simp only [materialize,Mutable.materialize,BoundaryIndex.Counted.rowWork,
    BoundaryIndex.Table.get_ofFn,matrixExtra]
  omega

def rowMatrix (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (ctx : Option (RowContext C E)) (tail : Replay C E) (idx : Mutable.Index)
    (target : Array Bool) (targetCounts : Array Nat) (window : SourceWindow) :
    Result (CursorRow (MaskedClusterStage.dfa C E).stateCount) :=
  let a:=materialize (fun i j=>rowCell C E prepared ctx tail idx target targetCounts window false
    (MaskedClusterStage.decode C E i) (MaskedClusterStage.decode C E j))
  let b:=materialize (fun i j=>rowCell C E prepared ctx tail idx target targetCounts window true
    (MaskedClusterStage.decode C E i) (MaskedClusterStage.decode C E j))
  (⟨a.1,b.1⟩,a.2+b.2+3)

theorem rowMatrix_value (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (ctx : Option (RowContext C E)) (tail : Replay C E) (idx : Mutable.Index)
    (target : Array Bool) (targetCounts : Array Nat) (window : SourceWindow) :
    (rowMatrix C E prepared ctx tail idx target targetCounts window).1=
      Mutable.rowMatrix C E prepared ctx tail idx target targetCounts window := by
  simp only [rowMatrix,materialize_value,rowCell_value,Mutable.rowMatrix]

def rowExtra (c e K : Nat) : Nat :=
  2*matrixExtra (1+c+e) (cellCost c e K+8)+3

theorem rowMatrix_extra (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (ctx : Option (RowContext C E)) (tail : Replay C E) (idx : Mutable.Index)
    (target : Array Bool) (targetCounts : Array Nat) (window : SourceWindow) :
    (rowMatrix C E prepared ctx tail idx target targetCounts window).2≤
      (Mutable.rowMatrix C E prepared ctx tail idx target targetCounts window).normal.work+
      (Mutable.rowMatrix C E prepared ctx tail idx target targetCounts window).over.work+
      rowExtra C.stateCount E.stateCount prepared.K := by
  have ha:=materialize_extra (fun i j=>rowCell C E prepared ctx tail idx target targetCounts window false
    (MaskedClusterStage.decode C E i) (MaskedClusterStage.decode C E j))
    (cellCost C.stateCount E.stateCount prepared.K+8) (by
      intro i j
      rw [rowCell_value]
      simpa only [Nat.add_assoc] using rowCell_extra C E prepared ctx tail idx target targetCounts window false
        (MaskedClusterStage.decode C E i) (MaskedClusterStage.decode C E j))
  have hb:=materialize_extra (fun i j=>rowCell C E prepared ctx tail idx target targetCounts window true
    (MaskedClusterStage.decode C E i) (MaskedClusterStage.decode C E j))
    (cellCost C.stateCount E.stateCount prepared.K+8) (by
      intro i j
      rw [rowCell_value]
      simpa only [Nat.add_assoc] using rowCell_extra C E prepared ctx tail idx target targetCounts window true
        (MaskedClusterStage.decode C E i) (MaskedClusterStage.decode C E j))
  simp only [rowCell_value,MaskedClusterStage.dfa_size] at ha hb
  simp only [rowMatrix,Mutable.rowMatrix,rowExtra]
  omega

def blocks (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (rows : Option (RowContext C E)×Option (RowContext C E)) (tail : Replay C E) (idx : Mutable.Index)
    (target : Array Bool) (targetCounts : Array Nat) (window : SourceWindow) :
    Result (CursorBlocks (MaskedClusterStage.dfa C E).stateCount) :=
  let a:=rowMatrix C E prepared rows.1 tail idx target targetCounts window
  let b:=rowMatrix C E prepared rows.2 tail idx target targetCounts window
  (⟨a.1,b.1⟩,a.2+b.2+3)

theorem blocks_value (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (rows : Option (RowContext C E)×Option (RowContext C E)) (tail : Replay C E) (idx : Mutable.Index)
    (target : Array Bool) (targetCounts : Array Nat) (window : SourceWindow) :
    (blocks C E prepared rows tail idx target targetCounts window).1=
      Mutable.blocks C E prepared rows tail idx target targetCounts window := by
  simp only [blocks,rowMatrix_value,Mutable.blocks]

def blocksExtra (c e K : Nat) : Nat := 2*rowExtra c e K+3

theorem blocks_extra (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (rows : Option (RowContext C E)×Option (RowContext C E)) (tail : Replay C E) (idx : Mutable.Index)
    (target : Array Bool) (targetCounts : Array Nat) (window : SourceWindow) :
    (blocks C E prepared rows tail idx target targetCounts window).2≤
      (Mutable.blocks C E prepared rows tail idx target targetCounts window).work+
      blocksExtra C.stateCount E.stateCount prepared.K := by
  have ha:=rowMatrix_extra C E prepared rows.1 tail idx target targetCounts window
  have hb:=rowMatrix_extra C E prepared rows.2 tail idx target targetCounts window
  simp only [blocks,Mutable.blocks,CursorBlocks.work,blocksExtra]
  omega

end REWB.PeriodicConstruction.Cluster
