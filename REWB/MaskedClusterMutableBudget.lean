import REWB.MaskedClusterMutableCorrect

/-! Counters of actual rebuilt mutable-source rows/banks. All source
    tree operations are included. Fixed-pattern compiler/catalog/action
    construction and choosing which cached banks to repair after a global
    erase remain separate; no automatic cache update is asserted.
-/
namespace REWB.MaskedCluster.Mutable
open REWB.MaskedPeriodic
variable {α : Type}

def rowBudget (C E : DFA α) (K levels : Nat) : Nat :=
  max (cellBudget C E K levels+4) (4*levels+26)

theorem rowCell_work (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (ctx : Option (RowContext C E)) (tail : Replay C E) (idx : Index)
    (target : Array Bool) (targetCounts : Array Nat) (window : SourceWindow) (outMode : Bool)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount) :
    (rowCell C E prepared ctx tail idx target targetCounts window outMode input output).work≤
      rowBudget C E prepared.K idx.levels := by
  have hlo:=Nat.le_max_left (cellBudget C E prepared.K idx.levels+4) (4*idx.levels+26)
  have hhi:=Nat.le_max_right (cellBudget C E prepared.K idx.levels+4) (4*idx.levels+26)
  cases ctx with
  | none => simp only [rowCell,rowBudget]; omega
  | some ctx =>
    cases outMode with
    | true =>
      cases ho : ctx.over with
      | none => simp only [rowCell,if_true,ho,rowBudget]; omega
      | some maps =>
        have hh:=pointCell_work C E maps tail idx target ctx.last window input output
        simp only [rowCell,if_true,ho,rowBudget]
        omega
    | false =>
      cases hn : ctx.normal with
      | none => simp only [rowCell,Bool.false_eq_true,if_false,hn,ofStatic,passCell,rowBudget]; omega
      | some maps =>
        have hh:=cell_work C E prepared maps tail ctx.lo ctx.hi idx targetCounts ctx.step ctx.start window input output
        simp only [rowCell,Bool.false_eq_true,if_false,hn,either,ofStatic,passCell,rowBudget]
        omega

theorem pointRowCell_work (C E : DFA α) (ctx : Option (RowContext C E)) (tail : Replay C E)
    (idx : Index) (target : Array Bool) (window : SourceWindow) (outMode : Bool)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount) :
    (pointRowCell C E ctx tail idx target window outMode input output).work≤4*idx.levels+30 := by
  cases ctx with
  | none => simp only [pointRowCell]; omega
  | some ctx =>
    cases outMode with
    | true =>
      cases ho : ctx.over with
      | none => simp only [pointRowCell,if_true,ho]; omega
      | some maps =>
        have hh:=pointCell_work C E maps tail idx target ctx.last window input output
        simp only [pointRowCell,if_true,ho]
        omega
    | false =>
      cases hn : ctx.normal with
      | none => simp only [pointRowCell,Bool.false_eq_true,if_false,hn,ofStatic,passCell]; omega
      | some maps =>
        have hh:=pointCell_work C E maps tail idx target ctx.last window input output
        simp only [pointRowCell,Bool.false_eq_true,if_false,hn,either,ofStatic,passCell]
        omega

theorem rowMatrix_work (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (ctx : Option (RowContext C E)) (tail : Replay C E) (idx : Index)
    (target : Array Bool) (targetCounts : Array Nat) (window : SourceWindow) (mode : Bool) :
    ((rowMatrix C E prepared ctx tail idx target targetCounts window).get mode).work≤
      (1+C.stateCount+E.stateCount)*((1+C.stateCount+E.stateCount)*(rowBudget C E prepared.K idx.levels+1)) := by
  rw [←MaskedClusterStage.dfa_size C E]
  cases mode <;> apply materialize_work <;> intro i j <;>
    exact rowCell_work C E prepared ctx tail idx target targetCounts window _ _ _

theorem pointRowMatrix_work (C E : DFA α) (ctx : Option (RowContext C E)) (tail : Replay C E)
    (idx : Index) (target : Array Bool) (window : SourceWindow) (mode : Bool) :
    ((pointRowMatrix C E ctx tail idx target window).get mode).work≤
      (1+C.stateCount+E.stateCount)*((1+C.stateCount+E.stateCount)*(4*idx.levels+31)) := by
  rw [←MaskedClusterStage.dfa_size C E]
  cases mode <;> apply materialize_work <;> intro i j <;>
    exact pointRowCell_work C E ctx tail idx target window _ _ _

theorem blocks_work (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (rows : Option (RowContext C E)×Option (RowContext C E)) (tail : Replay C E) (idx : Index)
    (target : Array Bool) (targetCounts : Array Nat) (window : SourceWindow) :
    (blocks C E prepared rows tail idx target targetCounts window).work≤
      4*((1+C.stateCount+E.stateCount)*((1+C.stateCount+E.stateCount)*(rowBudget C E prepared.K idx.levels+1))) := by
  have a:=rowMatrix_work C E prepared rows.1 tail idx target targetCounts window false
  have b:=rowMatrix_work C E prepared rows.1 tail idx target targetCounts window true
  have c:=rowMatrix_work C E prepared rows.2 tail idx target targetCounts window false
  have d:=rowMatrix_work C E prepared rows.2 tail idx target targetCounts window true
  simp only [CursorRow.get,Bool.false_eq_true,if_false,if_true] at a b c d
  simp only [blocks,CursorBlocks.work]
  omega

theorem pointBlocks_work (C E : DFA α) (rows : Option (RowContext C E)×Option (RowContext C E)) (tail : Replay C E)
    (idx : Index) (target : Array Bool) (window : SourceWindow) :
    (pointBlocks C E rows tail idx target window).work≤
      4*((1+C.stateCount+E.stateCount)*((1+C.stateCount+E.stateCount)*(4*idx.levels+31))) := by
  have a:=pointRowMatrix_work C E rows.1 tail idx target window false
  have b:=pointRowMatrix_work C E rows.1 tail idx target window true
  have c:=pointRowMatrix_work C E rows.2 tail idx target window false
  have d:=pointRowMatrix_work C E rows.2 tail idx target window true
  simp only [CursorRow.get,Bool.false_eq_true,if_false,if_true] at a b c d
  simp only [pointBlocks,CursorBlocks.work]
  omega

def denseBankBudget (C E : DFA α) (K levels : Nat) : Nat :=
  (2*ReplayMaps.count C.stateCount E.stateCount)*
    (C.stateCount+E.stateCount+
      4*((1+C.stateCount+E.stateCount)*((1+C.stateCount+E.stateCount)*(rowBudget C E K levels+1)))+
      (2*(1+C.stateCount+E.stateCount))*((2*(1+C.stateCount+E.stateCount))*11)+7)

def pointBankBudget (C E : DFA α) (levels : Nat) : Nat :=
  (2*ReplayMaps.count C.stateCount E.stateCount)*
    (C.stateCount+E.stateCount+4*((1+C.stateCount+E.stateCount)*((1+C.stateCount+E.stateCount)*(4*levels+31)))+
      (2*(1+C.stateCount+E.stateCount))*((2*(1+C.stateCount+E.stateCount))*11)+7)

theorem denseBank_work (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount) (rows : Option (RowContext C E)×Option (RowContext C E))
    (tail : Replay C E) (idx : Index) (target : Array Bool) (targetCounts : Array Nat) (window : SourceWindow) :
    (denseBank C E book prepared rows tail idx target targetCounts window).2≤denseBankBudget C E prepared.K idx.levels := by
  unfold denseBankBudget
  rw [←MaskedClusterStage.dfa_size C E]
  apply tabulate_work
  intro enabled value
  conv => rhs; rw [MaskedClusterStage.dfa_size C E]
  exact blocks_work C E prepared rows value idx target targetCounts (window.gate enabled)

theorem pointBank_work (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (rows : Option (RowContext C E)×Option (RowContext C E)) (tail : Replay C E)
    (idx : Index) (target : Array Bool) (window : SourceWindow) :
    (pointBank C E book rows tail idx target window).2≤pointBankBudget C E idx.levels := by
  unfold pointBankBudget
  rw [←MaskedClusterStage.dfa_size C E]
  apply tabulate_work
  intro enabled value
  conv => rhs; rw [MaskedClusterStage.dfa_size C E]
  exact pointBlocks_work C E rows value idx target (window.gate enabled)

theorem compileDenseBank_work (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount) (w : Word α)
    (s q m L H next incoming : Nat) (enabled : Bool) (idx : Index)
    (target : Array Bool) (targetCounts : Array Nat) (window : SourceWindow)
    (hq : q≤H) (hm : 0<m) (hLH : L≤H) (hpen : s+(m-1)*q+H≤next)
    (hsep : s+m*q<next) (hnext : next≤w.length) (hbound : s+m*q+H≤w.length)
    (hin : enabled=true→s<incoming ∧ incoming≤s+q) :
    (compileDenseBank C E book prepared (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
      s q m L H next incoming enabled idx target targetCounts window).2≤
        2*denseRowPrepBudget C E w.length+(C.stateCount+E.stateCount+16*(Nat.log2 w.length+2)+6)+
          denseBankBudget C E prepared.K idx.levels+3 := by
  have a:=prepareRows_work C E w s q m H next incoming enabled hq hm hpen hsep hnext hbound hin
  have b:=(replay_bounds C E w s L H hLH (by omega)).2.2
  have c:=denseBank_work C E book prepared
    (prepareRows C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
      s q m H next incoming enabled).1
    (replay C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w) s L H).maps
    idx target targetCounts window
  simp only [compileDenseBank]
  omega

theorem compilePointBank_work (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount) (w : Word α)
    (s L H next incoming : Nat) (enabled : Bool) (idx : Index) (target : Array Bool) (window : SourceWindow)
    (hLH : L≤H) (hsep : s<next) (hnext : next≤w.length) (hbound : s+H≤w.length)
    (hin : enabled=true→s<incoming ∧ incoming≤next) :
    (compilePointBank C E book (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
      s L H next incoming enabled idx target window).2≤
        2*pointRowPrepBudget C E w.length+(C.stateCount+E.stateCount+16*(Nat.log2 w.length+2)+6)+
          pointBankBudget C E idx.levels+3 := by
  have a:=preparePointRows_work C E w s H next incoming enabled hsep hnext hbound hin
  have b:=(replay_bounds C E w s L H hLH hbound).2.2
  have c:=pointBank_work C E book
    (preparePointRows C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
      s H next incoming enabled).1
    (replay C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w) s L H).maps
    idx target window
  simp only [compilePointBank]
  omega

theorem sourcePairQuery_log_work {m n : Nat} (before : OrbitData m) (after : OrbitData n) (lo hi : Nat)
    (idx : Index) (hh : idx.LogSized) (q s K : Nat) (window : SourceWindow) :
    (sourcePairQuery before after lo hi idx q s K window).work≤
      (87*(K*(m*n))+1)*((idx.len+1).log2+1) := by
  have hw:=sourcePairQuery_work before after lo hi idx q s K window
  have hL : 1≤(idx.len+1).log2+1 := by omega
  have hc : 7*idx.levels+73≤87*((idx.len+1).log2+1) := by
    rw [hh]
    unfold MaskedMutableProgression.height
    omega
  have hm:=Nat.mul_le_mul_right (K*(m*n)) hc
  have he : (87*((idx.len+1).log2+1))*(K*(m*n))=(87*(K*(m*n)))*((idx.len+1).log2+1) := by ac_rfl
  rw [he] at hm
  rw [Nat.add_mul,Nat.one_mul]
  omega

end REWB.MaskedCluster.Mutable
