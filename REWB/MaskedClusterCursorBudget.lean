import REWB.MaskedClusterBlocksCorrect

/-! Bounds for the actual context lookups and the four materialized
    cursor blocks. These are bounds for the counters already returned by
    the executable routines: range-map queries, AP mask queries, fixed
    scalar operations, and output cells. They do not charge the separate
    finite-orbit/formula compiler, mask-array preparation, the shared
    text-index build, or the global repair/report schedule.
-/
namespace REWB.MaskedCluster
variable {α : Type}

def denseRowPrepBudget (C E : DFA α) (n : Nat) : Nat :=
  7*C.stateCount+4*E.stateCount+88*(Nat.log2 n+2)+39

def pointRowPrepBudget (C E : DFA α) (n : Nat) : Nat :=
  3*C.stateCount+2*E.stateCount+40*(Nat.log2 n+2)+17

theorem prepareRow_work (C E : DFA α) (w : Word α)
    (s q m H next incoming : Nat) (enabled mode : Bool)
    (hq : q≤H) (hm : 0<m) (hpen : s+(m-1)*q+H≤next)
    (hsep : s+m*q<next) (hnext : next≤w.length) (hbound : s+m*q+H≤w.length)
    (hin : enabled=true→s<incoming ∧ incoming≤s+q) :
    (prepareRow C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
      s q m H next incoming enabled mode).2≤denseRowPrepBudget C E w.length := by
  by_cases ha : modeAllowed enabled mode=true
  · have hlow:=cursor_before_lower s q incoming enabled mode ha hin
    have hlast:=cursor_before_last s q m incoming enabled mode hm ha hin
    have hcursor:=cursor_before_next s q m next incoming enabled mode hm hsep ha hin
    have huend:=normalHi_end s q m H next hpen
    have hp:=passContext_work C E w (cursor s incoming mode) next hcursor hnext
    have ho:=(pointContexts_bounds C E w (cursor s incoming mode) (s+m*q) H (s+m*q+H)
      hlast (Nat.le_refl _) hbound).2.2
    by_cases hc : lower mode≤normalHi s q m H next
    · have hn:=contexts_work C E w (cursor s incoming mode) s H q (lower mode)
        (normalHi s q m H next) next hq hc hlow huend hnext
      by_cases hover : overMode s q m H next=true <;>
        simp only [prepareRow,ha,hc,hover,Bool.false_eq_true,if_true,if_false,denseRowPrepBudget] <;> omega
    · by_cases hover : overMode s q m H next=true <;>
        simp only [prepareRow,ha,hc,hover,Bool.false_eq_true,if_true,if_false,denseRowPrepBudget] <;> omega
  · simp only [prepareRow,ha,Bool.false_eq_true,if_false,denseRowPrepBudget]
    omega

theorem prepareRows_work (C E : DFA α) (w : Word α)
    (s q m H next incoming : Nat) (enabled : Bool)
    (hq : q≤H) (hm : 0<m) (hpen : s+(m-1)*q+H≤next)
    (hsep : s+m*q<next) (hnext : next≤w.length) (hbound : s+m*q+H≤w.length)
    (hin : enabled=true→s<incoming ∧ incoming≤s+q) :
    (prepareRows C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
      s q m H next incoming enabled).2≤2*denseRowPrepBudget C E w.length := by
  have a:=prepareRow_work C E w s q m H next incoming enabled false hq hm hpen hsep hnext hbound hin
  have b:=prepareRow_work C E w s q m H next incoming enabled true hq hm hpen hsep hnext hbound hin
  simp only [prepareRows]
  omega

theorem preparePointRow_work (C E : DFA α) (w : Word α)
    (s H next incoming : Nat) (enabled mode : Bool)
    (hsep : s<next) (hnext : next≤w.length) (hbound : s+H≤w.length)
    (hin : enabled=true→s<incoming ∧ incoming≤next) :
    (preparePointRow C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
      s H next incoming enabled mode).2≤pointRowPrepBudget C E w.length := by
  by_cases ha : modeAllowed enabled mode=true
  · cases mode with
    | true =>
      have he:=((modeAllowed_iff enabled true).mp ha) rfl
      have hp:=passContext_work C E w incoming next (hin he).2 hnext
      simp only [preparePointRow,ha,if_true,cursor,Bool.not_true,Bool.false_and,
        Bool.false_eq_true,if_false,pointRowPrepBudget]
      omega
    | false =>
      have hp:=passContext_work C E w s next (Nat.le_of_lt hsep) hnext
      by_cases ho : next<s+H
      · have hov : overMode s 1 0 H next=true := by
          simp only [overMode,Nat.zero_mul,Nat.add_zero,ho,decide_true]
        have hc:=(pointContexts_bounds C E w s s H (s+H) (Nat.le_refl _) (Nat.le_refl _) hbound).2.2
        simp only [preparePointRow,ha,if_true,cursor,Bool.false_eq_true,if_false,Bool.not_false,
          hov,Bool.not_true,Bool.true_and,pointRowPrepBudget]
        omega
      · have hO : s+H≤next := by omega
        have hov : overMode s 1 0 H next=false := by
          simp only [overMode,Nat.zero_mul,Nat.add_zero,ho,decide_false]
        have hc:=(pointContexts_bounds C E w s s H next (Nat.le_refl _) hO hnext).2.2
        simp only [preparePointRow,ha,if_true,cursor,Bool.false_eq_true,if_false,Bool.not_false,
          hov,Bool.true_and,pointRowPrepBudget]
        omega
  · simp only [preparePointRow,ha,Bool.false_eq_true,if_false,pointRowPrepBudget]
    omega

theorem preparePointRows_work (C E : DFA α) (w : Word α)
    (s H next incoming : Nat) (enabled : Bool)
    (hsep : s<next) (hnext : next≤w.length) (hbound : s+H≤w.length)
    (hin : enabled=true→s<incoming ∧ incoming≤next) :
    (preparePointRows C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
      s H next incoming enabled).2≤2*pointRowPrepBudget C E w.length := by
  have a:=preparePointRow_work C E w s H next incoming enabled false hsep hnext hbound hin
  have b:=preparePointRow_work C E w s H next incoming enabled true hsep hnext hbound hin
  simp only [preparePointRows]
  omega

theorem pointRowCell_work (C E : DFA α) (ctx : Option (RowContext C E)) (tail : Replay C E)
    (source target : Array Bool) (window : SourceWindow) (outMode : Bool)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount) :
    (pointRowCell C E ctx tail source target window outMode input output).slots+
      (pointRowCell C E ctx tail source target window outMode input output).arithmetic≤20 := by
  cases ctx with
  | none => simp only [pointRowCell]; decide
  | some ctx =>
    cases outMode with
    | true => cases ho : ctx.over <;> simp only [pointRowCell,if_true,ho,filteredPointCell] <;> decide
    | false => cases hn : ctx.normal <;>
        simp only [pointRowCell,Bool.false_eq_true,if_false,hn,either,passCell,filteredPointCell] <;> decide

theorem pointRowMatrix_work (C E : DFA α) (ctx : Option (RowContext C E)) (tail : Replay C E)
    (source target : Array Bool) (window : SourceWindow) (mode : Bool) :
    ((pointRowMatrix C E ctx tail source target window).get mode).work≤
      (1+C.stateCount+E.stateCount)*((1+C.stateCount+E.stateCount)*21) := by
  rw [←MaskedClusterStage.dfa_size C E]
  cases mode <;> apply materialize_work <;> intro i j <;>
    exact pointRowCell_work C E ctx tail source target window _ _ _

theorem blocks_work (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (rows : Option (RowContext C E)×Option (RowContext C E)) (tail : Replay C E)
    (source target : Array Bool) (sourceCounts targetCounts : Array Nat)
    (base : Nat) (window : SourceWindow) :
    (blocks C E prepared rows tail source target sourceCounts targetCounts base window).work≤
      4*((1+C.stateCount+E.stateCount)*((1+C.stateCount+E.stateCount)*(rowBudget C E prepared.K+1))) := by
  have a:=rowMatrix_work C E prepared rows.1 tail source target sourceCounts targetCounts base window false
  have b:=rowMatrix_work C E prepared rows.1 tail source target sourceCounts targetCounts base window true
  have c:=rowMatrix_work C E prepared rows.2 tail source target sourceCounts targetCounts base window false
  have d:=rowMatrix_work C E prepared rows.2 tail source target sourceCounts targetCounts base window true
  simp only [CursorRow.get,Bool.false_eq_true,if_false,if_true] at a b c d
  simp only [blocks,CursorBlocks.work]
  omega

theorem pointBlocks_work (C E : DFA α) (rows : Option (RowContext C E)×Option (RowContext C E))
    (tail : Replay C E) (source target : Array Bool) (window : SourceWindow) :
    (pointBlocks C E rows tail source target window).work≤
      4*((1+C.stateCount+E.stateCount)*((1+C.stateCount+E.stateCount)*21)) := by
  have a:=pointRowMatrix_work C E rows.1 tail source target window false
  have b:=pointRowMatrix_work C E rows.1 tail source target window true
  have c:=pointRowMatrix_work C E rows.2 tail source target window false
  have d:=pointRowMatrix_work C E rows.2 tail source target window true
  simp only [CursorRow.get,Bool.false_eq_true,if_false,if_true] at a b c d
  simp only [pointBlocks,CursorBlocks.work]
  omega

def denseCompilerBudget (C E : DFA α) (K n : Nat) : Nat :=
  2*denseRowPrepBudget C E n+(C.stateCount+E.stateCount+16*(Nat.log2 n+2)+6)+
    4*((1+C.stateCount+E.stateCount)*((1+C.stateCount+E.stateCount)*(rowBudget C E K+1)))+3

def pointCompilerBudget (C E : DFA α) (n : Nat) : Nat :=
  2*pointRowPrepBudget C E n+(C.stateCount+E.stateCount+16*(Nat.log2 n+2)+6)+
    4*((1+C.stateCount+E.stateCount)*((1+C.stateCount+E.stateCount)*21))+3

theorem compileDense_work (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount) (w : Word α)
    (s q m L H next incoming : Nat) (enabled : Bool) (source target : Array Bool)
    (sourceCounts targetCounts : Array Nat) (base : Nat) (window : SourceWindow)
    (hq : q≤H) (hm : 0<m) (hLH : L≤H) (hpen : s+(m-1)*q+H≤next)
    (hsep : s+m*q<next) (hnext : next≤w.length) (hbound : s+m*q+H≤w.length)
    (hin : enabled=true→s<incoming ∧ incoming≤s+q) :
    (compileDense C E prepared (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
      s q m L H next incoming enabled source target sourceCounts targetCounts base window).2≤
        denseCompilerBudget C E prepared.K w.length := by
  have a:=prepareRows_work C E w s q m H next incoming enabled hq hm hpen hsep hnext hbound hin
  have b:=(replay_bounds C E w s L H hLH (by omega)).2.2
  have c:=blocks_work C E prepared
    (prepareRows C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
      s q m H next incoming enabled).1
    (replay C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w) s L H).maps
    source target sourceCounts targetCounts base window
  simp only [compileDense,denseCompilerBudget]
  omega

theorem compilePoint_work (C E : DFA α) (w : Word α)
    (s L H next incoming : Nat) (enabled : Bool) (source target : Array Bool) (window : SourceWindow)
    (hLH : L≤H) (hsep : s<next) (hnext : next≤w.length) (hbound : s+H≤w.length)
    (hin : enabled=true→s<incoming ∧ incoming≤next) :
    (compilePoint C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
      s L H next incoming enabled source target window).2≤pointCompilerBudget C E w.length := by
  have a:=preparePointRows_work C E w s H next incoming enabled hsep hnext hbound hin
  have b:=(replay_bounds C E w s L H hLH hbound).2.2
  have c:=pointBlocks_work C E
    (preparePointRows C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
      s H next incoming enabled).1
    (replay C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w) s L H).maps
    source target window
  simp only [compilePoint,pointCompilerBudget]
  omega

end REWB.MaskedCluster
