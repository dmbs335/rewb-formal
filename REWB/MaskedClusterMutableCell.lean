import REWB.MaskedClusterMutableAP

/-! One-jump cells with an actual persistent source index and immutable
    target counts. Only waiting→C uses the mutable AP procedure; C→E
    keeps the original target procedure. Point cells replace their source
    array read with one measured persistent membership query.
-/
namespace REWB.MaskedCluster.Mutable
variable {α : Type}

def cell (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (maps : Context C E) (tail : Replay C E) (lo hi : Nat) (idx : Index)
    (targetCounts : Array Nat) (q s : Nat) (window : SourceWindow) :
    MaskedClusterStage.State C.stateCount E.stateCount→
      MaskedClusterStage.State C.stateCount E.stateCount→Answer
  | .waiting,.gap output =>
    sourcePairQuery (always C) (exitOrbit C maps.rightC tail.1 maps.afterC output)
      lo hi idx q s prepared.K window
  | input,output => ofStatic (REWB.MaskedCluster.cell C E prepared maps tail lo hi #[] targetCounts idx.base q s input output)

theorem cell_target (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (maps : Context C E) (tail : Replay C E) (lo hi : Nat) (idx : Index)
    (targetCounts : Array Nat) (q s : Nat) (window : SourceWindow)
    (input : Fin C.stateCount) (output : MaskedClusterStage.State C.stateCount E.stateCount) :
    cell C E prepared maps tail lo hi idx targetCounts q s window (.gap input) output=
      ofStatic (REWB.MaskedCluster.cell C E prepared maps tail lo hi #[] targetCounts idx.base q s (.gap input) output) := rfl

theorem cell_snapshot (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (maps : Context C E) (tail : Replay C E) (lo hi : Nat) (idx : Index) (hv : idx.Valid)
    (targetCounts : Array Nat) (q s : Nat) (window : SourceWindow)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount)
    (hq : 0<q) (hstep : idx.step=prepared.K*q) :
    (cell C E prepared maps tail lo hi idx targetCounts q s window input output).answer=
      (filteredCell C E prepared maps tail lo hi
        (MaskedProgression.build (snapshot idx) idx.base idx.len (prepared.K*q)).counts
        targetCounts idx.base q s window input output).answer := by
  cases input with
  | waiting =>
    cases output with
    | gap output =>
      simp only [cell,filteredCell,prepared.exact,modulus]
      apply sourcePairQuery_snapshot _ _ _ _ idx hv q s (max C.stateCount E.stateCount) window hq
        (Nat.le_max_left _ _) (Nat.le_max_left _ _)
      simpa only [prepared.exact,modulus] using hstep
    | waiting => rfl
    | suffix _ => rfl
  | gap _ => cases output <;> rfl
  | suffix _ => cases output <;> rfl

def cellBudget (C E : DFA α) (K levels : Nat) : Nat :=
  (7*levels+73)*(K*(max C.stateCount E.stateCount*max C.stateCount E.stateCount))+1

theorem cell_work (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (maps : Context C E) (tail : Replay C E) (lo hi : Nat) (idx : Index)
    (targetCounts : Array Nat) (q s : Nat) (window : SourceWindow)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount) :
    (cell C E prepared maps tail lo hi idx targetCounts q s window input output).work≤
      cellBudget C E prepared.K idx.levels := by
  have hCC:=Nat.mul_le_mul (Nat.le_max_left C.stateCount E.stateCount) (Nat.le_max_left C.stateCount E.stateCount)
  have hCC':=Nat.mul_le_mul_left (7*idx.levels+73) (Nat.mul_le_mul_left prepared.K hCC)
  have hstatic:=Nat.mul_le_mul_right (prepared.K*(max C.stateCount E.stateCount*max C.stateCount E.stateCount))
    (show 47≤7*idx.levels+73 by omega)
  have hold:=REWB.MaskedCluster.cell_work C E prepared maps tail lo hi #[] targetCounts idx.base q s input output
  cases input with
  | waiting =>
    cases output with
    | gap output =>
      have h:=sourcePairQuery_work (always C) (exitOrbit C maps.rightC tail.1 maps.afterC output)
        lo hi idx q s prepared.K window
      exact Nat.le_trans h (by unfold cellBudget; omega)
    | waiting => simp only [cell,ofStatic,REWB.MaskedCluster.cell,cellBudget]; omega
    | suffix _ => simp only [cell,ofStatic,REWB.MaskedCluster.cell,cellBudget]; omega
  | gap _ =>
    change (REWB.MaskedCluster.cell C E prepared maps tail lo hi #[] targetCounts idx.base q s _ _).slots+
      (REWB.MaskedCluster.cell C E prepared maps tail lo hi #[] targetCounts idx.base q s _ _).arithmetic≤_
    exact Nat.le_trans hold (by unfold REWB.MaskedCluster.cellBudget cellBudget; omega)
  | suffix _ =>
    change (REWB.MaskedCluster.cell C E prepared maps tail lo hi #[] targetCounts idx.base q s _ _).slots+
      (REWB.MaskedCluster.cell C E prepared maps tail lo hi #[] targetCounts idx.base q s _ _).arithmetic≤_
    exact Nat.le_trans hold (by unfold REWB.MaskedCluster.cellBudget cellBudget; omega)

def pointCell (C E : DFA α) (maps : Context C E) (tail : Replay C E)
    (idx : Index) (target : Array Bool) (p : Nat) (window : SourceWindow)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount) : Answer :=
  let source:=MaskedMutableProgression.member idx p
  ⟨decide (point C E maps tail (window.allows p && source.1) (MaskedProgression.readMask target p) input=some output),
    source.2+15⟩

theorem pointCell_snapshot (C E : DFA α) (maps : Context C E) (tail : Replay C E)
    (idx : Index) (target : Array Bool) (p : Nat) (window : SourceWindow)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount) :
    (pointCell C E maps tail idx target p window input output).answer=
      (filteredPointCell C E maps tail (snapshot idx) target p window input output).answer := by
  simp only [pointCell,filteredPointCell,snapshot_read]

theorem pointCell_work (C E : DFA α) (maps : Context C E) (tail : Replay C E)
    (idx : Index) (target : Array Bool) (p : Nat) (window : SourceWindow)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount) :
    (pointCell C E maps tail idx target p window input output).work≤4*idx.levels+26 := by
  have h:=MaskedMutableProgression.member_work idx p
  simp only [pointCell]
  omega

theorem pointCell_target_erase (C E : DFA α) (maps : Context C E) (tail : Replay C E)
    (idx : Index) (target : Array Bool) (p deleted : Nat) (window : SourceWindow)
    (input : Fin C.stateCount) (output : MaskedClusterStage.State C.stateCount E.stateCount) :
    (pointCell C E maps tail (MaskedMutableProgression.erase idx deleted).index target p window (.gap input) output).answer=
      (pointCell C E maps tail idx target p window (.gap input) output).answer := rfl

theorem cell_direct_first (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (w : Word α) (fallback : α) (I s R q L H lo hi O : Nat) (idx : Index) (hv : idx.Valid)
    (target : Array Bool) (window : SourceWindow)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount)
    (hp : RunGeometry.OnPeriod (ArrayText.read w.toArray fallback) s R q)
    (hq : 0<q) (hH : q≤H) (hlo : lo≤hi) (hI : I≤s+lo*q)
    (hb : s+hi*q+H≤R) (hn : R≤w.length) (hO : s+hi*q+H≤O) (hOn : O≤w.length)
    (hLH : L≤H) (hstep : idx.step=prepared.K*q) :
    (cell C E prepared
      (contexts C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w) I s H q lo hi O).maps
      (replay C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w) s L H).maps
      lo hi idx (MaskedProgression.build target idx.base idx.len (prepared.K*q)).counts q s window input output).answer=true ↔
      ∃k,lo≤k ∧ k≤hi ∧ idx.base≤s+k*q ∧ s+k*q<idx.base+idx.len ∧
        MaskedClusterStage.direct C E w I (s+k*q) L O
          (window.allows (s+k*q) && (MaskedMutableProgression.member idx (s+k*q)).1)
          (MaskedProgression.readMask target (s+k*q)) input=some output := by
  rw [cell_snapshot C E prepared _ _ lo hi idx hv _ q s window input output hq hstep,
    filteredCell_direct_first C E prepared w fallback I s R q L H lo hi O (snapshot idx) target idx.base idx.len
      window input output hp hq hH hlo hI hb hn hO hOn hLH]
  simp only [snapshot_read]

end REWB.MaskedCluster.Mutable
