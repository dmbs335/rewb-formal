import REWB.MaskedClusterTransfer

/-! Materialize every one-jump cell into a fixed-size Boolean matrix.
    Each compiler invocation is performed once and its result is stored
    before matrix extraction. The recorded matrix work counts AP-query
    work and output cells; orbit/formula/window construction remains a
    separate component, as in `MaskedClusterAP`.
-/
namespace REWB.MaskedCluster
open REWB.MaskedPeriodic REWB.MaskedFiniteAction
open REWB.BoundaryIndex.Counted (rowWork)
variable {α : Type}

def cellBudget (C E : DFA α) (K : Nat) : Nat :=
  47*(K*(max C.stateCount E.stateCount*max C.stateCount E.stateCount))+1

theorem cell_work (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (maps : Context C E) (tail : Replay C E) (lo hi : Nat)
    (sourceCounts targetCounts : Array Nat) (base q s : Nat)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount) :
    (cell C E prepared maps tail lo hi sourceCounts targetCounts base q s input output).slots+
      (cell C E prepared maps tail lo hi sourceCounts targetCounts base q s input output).arithmetic≤
        cellBudget C E prepared.K := by
  have hCC:=Nat.mul_le_mul (Nat.le_max_left C.stateCount E.stateCount)
    (Nat.le_max_left C.stateCount E.stateCount)
  have hCE:=Nat.mul_le_mul (Nat.le_max_left C.stateCount E.stateCount)
    (Nat.le_max_right C.stateCount E.stateCount)
  have hCC':=Nat.mul_le_mul_left 47 (Nat.mul_le_mul_left prepared.K hCC)
  have hCE':=Nat.mul_le_mul_left 47 (Nat.mul_le_mul_left prepared.K hCE)
  cases input with
  | waiting =>
    cases output with
    | waiting => simp only [cell,cellBudget]; omega
    | gap output =>
      have h:=pairQuery_work (always C) (exitOrbit C maps.rightC tail.1 maps.afterC output)
        lo hi sourceCounts base q s prepared.K
      exact Nat.le_trans h (by unfold cellBudget; omega)
    | suffix output => simp only [cell,cellBudget]; omega
  | gap input =>
    cases output with
    | waiting => simp only [cell,cellBudget]; omega
    | gap output => simp only [cell,cellBudget]; omega
    | suffix output =>
      have h:=pairQuery_work (entryOrbit C E maps input) (exitOrbit E maps.rightE tail.2 maps.afterE output)
        lo hi targetCounts base q s prepared.K
      exact Nat.le_trans h (by unfold cellBudget; omega)
  | suffix input => cases output <;> simp only [cell,cellBudget] <;> omega

theorem sum_ofFn_le (n bound : Nat) (f : Fin n→Nat) (h : ∀ i,f i≤bound) :
    (List.ofFn f).sum≤n*bound := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ,List.sum_cons]
    have ht:=ih (fun i=>f i.succ) (fun i=>h i.succ)
    have hh:=h 0
    rw [Nat.add_mul,Nat.one_mul]
    omega

theorem rowWork_le {n : Nat} {β : Type} (v : Vector (β×Nat) n) (bound : Nat)
    (h : ∀ i,(v.get i).2≤bound) : rowWork v≤n*(bound+1) := by
  apply sum_ofFn_le
  intro i
  have hh:=h i
  omega

structure MatrixResult (m : Nat) where
  cells : Matrix m
  work : Nat

def matrix (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (maps : Context C E) (tail : Replay C E) (lo hi : Nat)
    (sourceCounts targetCounts : Array Nat) (base q s : Nat) :
    MatrixResult (MaskedClusterStage.dfa C E).stateCount :=
  let results := Vector.ofFn fun input=>Vector.ofFn fun output=>
    let a:=cell C E prepared maps tail lo hi sourceCounts targetCounts base q s
      (MaskedClusterStage.decode C E input) (MaskedClusterStage.decode C E output)
    (a.answer,a.slots+a.arithmetic)
  ⟨Vector.ofFn (fun input=>Vector.ofFn (fun output=>((results.get input).get output).1)),
    (List.ofFn (fun input=>rowWork (results.get input))).sum⟩

theorem matrix_get (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (maps : Context C E) (tail : Replay C E) (lo hi : Nat)
    (sourceCounts targetCounts : Array Nat) (base q s : Nat)
    (input output : Fin (MaskedClusterStage.dfa C E).stateCount) :
    (((matrix C E prepared maps tail lo hi sourceCounts targetCounts base q s).cells.get input).get output)=
      (cell C E prepared maps tail lo hi sourceCounts targetCounts base q s
        (MaskedClusterStage.decode C E input) (MaskedClusterStage.decode C E output)).answer := by
  simp only [matrix,BoundaryIndex.Table.get_ofFn]

theorem matrix_state (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (maps : Context C E) (tail : Replay C E) (lo hi : Nat)
    (sourceCounts targetCounts : Array Nat) (base q s : Nat)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount) :
    (((matrix C E prepared maps tail lo hi sourceCounts targetCounts base q s).cells.get
      (MaskedClusterStage.encode C E input)).get (MaskedClusterStage.encode C E output))=
      (cell C E prepared maps tail lo hi sourceCounts targetCounts base q s input output).answer := by
  rw [matrix_get,MaskedClusterStage.decode_encode,MaskedClusterStage.decode_encode]

theorem matrix_work (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (maps : Context C E) (tail : Replay C E) (lo hi : Nat)
    (sourceCounts targetCounts : Array Nat) (base q s : Nat) :
    (matrix C E prepared maps tail lo hi sourceCounts targetCounts base q s).work≤
      (1+C.stateCount+E.stateCount)*((1+C.stateCount+E.stateCount)*(cellBudget C E prepared.K+1)) := by
  rw [←MaskedClusterStage.dfa_size C E]
  apply sum_ofFn_le
  intro input
  apply rowWork_le
  intro output
  simp only [BoundaryIndex.Table.get_ofFn]
  exact cell_work C E prepared maps tail lo hi sourceCounts targetCounts base q s _ _

end REWB.MaskedCluster
