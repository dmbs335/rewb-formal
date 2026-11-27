import REWB.MaskedClusterCursorGeometry

/-! Actual preparation and materialization of one incoming cursor row.
    Preparation reads real range maps once. Tabulation can then be
    repeated over the fixed replay-map universe without repeating those
    range queries. A row has normal and overshoot output matrices.
-/
namespace REWB.MaskedCluster
variable {α : Type}

structure RowContext (C E : DFA α) where
  start : Nat
  step : Nat
  entry : Nat
  lo : Nat
  hi : Nat
  last : Nat
  pass : Replay C E
  normal : Option (Context C E)
  over : Option (Context C E)

def prepareRow (C E : DFA α) (ci : BoundaryApplication.Range.Index C)
    (ei : BoundaryApplication.Range.Index E) (s q m H next incoming : Nat)
    (enabled mode : Bool) : Option (RowContext C E)×Nat :=
  if modeAllowed enabled mode then
    let I:=cursor s incoming mode
    let lo:=lower mode
    let hi:=normalHi s q m H next
    let last:=s+m*q
    let pass:=passContext C E ci ei I next
    let normal:=if lo≤hi then
      let out:=contexts C E ci ei I s H q lo hi next
      (some out.maps,out.work+1)
      else (none,1)
    let over:=if overMode s q m H next then
      let out:=pointContexts C E ci ei I last H (last+H)
      (some out.maps,out.work+1)
      else (none,1)
    (some ⟨s,q,I,lo,hi,last,pass.maps,normal.1,over.1⟩,pass.work+normal.2+over.2+12)
  else (none,1)

def rowCell (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (ctx : Option (RowContext C E)) (tail : Replay C E)
    (source target : Array Bool) (sourceCounts targetCounts : Array Nat)
    (base : Nat) (window : SourceWindow) (outMode : Bool)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount) : MaskedProgression.Answer :=
  match ctx with
  | none => ⟨false,0,1⟩
  | some ctx =>
    if outMode then
      match ctx.over with
      | none => ⟨false,0,1⟩
      | some maps => filteredPointCell C E maps tail source target ctx.last window input output
    else
      let pass:=passCell C E ctx.pass input output
      match ctx.normal with
      | none => pass
      | some maps => either pass (filteredCell C E prepared maps tail ctx.lo ctx.hi sourceCounts
          targetCounts base ctx.step ctx.start window input output)

theorem rowCell_inactive (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (s q m H next incoming : Nat) (enabled mode : Bool) (h : modeAllowed enabled mode≠true)
    (tail : Replay C E) (source target : Array Bool) (sourceCounts targetCounts : Array Nat)
    (base : Nat) (window : SourceWindow) (outMode : Bool)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount) :
    rowCell C E prepared (prepareRow C E ci ei s q m H next incoming enabled mode).1
      tail source target sourceCounts targetCounts base window outMode input output=⟨false,0,1⟩ := by
  simp only [prepareRow,h,Bool.false_eq_true,if_false,rowCell]

theorem rowCell_normal (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (s q m H next incoming : Nat) (enabled mode : Bool) (h : modeAllowed enabled mode=true)
    (tail : Replay C E) (source target : Array Bool) (sourceCounts targetCounts : Array Nat)
    (base : Nat) (window : SourceWindow)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount) :
    rowCell C E prepared (prepareRow C E ci ei s q m H next incoming enabled mode).1
      tail source target sourceCounts targetCounts base window false input output=
      if lower mode≤normalHi s q m H next then
        either (passCell C E (passContext C E ci ei (cursor s incoming mode) next).maps input output)
          (filteredCell C E prepared
            (contexts C E ci ei (cursor s incoming mode) s H q (lower mode) (normalHi s q m H next) next).maps
            tail (lower mode) (normalHi s q m H next) sourceCounts targetCounts base q s window input output)
      else passCell C E (passContext C E ci ei (cursor s incoming mode) next).maps input output := by
  by_cases hn : lower mode≤normalHi s q m H next <;>
    simp only [prepareRow,h,hn,if_true,if_false,rowCell,Bool.false_eq_true]

theorem rowCell_over (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (s q m H next incoming : Nat) (enabled mode : Bool) (h : modeAllowed enabled mode=true)
    (tail : Replay C E) (source target : Array Bool) (sourceCounts targetCounts : Array Nat)
    (base : Nat) (window : SourceWindow)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount) :
    rowCell C E prepared (prepareRow C E ci ei s q m H next incoming enabled mode).1
      tail source target sourceCounts targetCounts base window true input output=
      if overMode s q m H next then
        filteredPointCell C E (pointContexts C E ci ei (cursor s incoming mode) (s+m*q) H (s+m*q+H)).maps
          tail source target (s+m*q) window input output
      else ⟨false,0,1⟩ := by
  by_cases ho : overMode s q m H next=true <;>
    simp only [prepareRow,h,ho,if_true,if_false,rowCell,Bool.false_eq_true]

def rowBudget (C E : DFA α) (K : Nat) : Nat := max (cellBudget C E K+4) 16

theorem rowCell_work (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (ctx : Option (RowContext C E)) (tail : Replay C E)
    (source target : Array Bool) (sourceCounts targetCounts : Array Nat)
    (base : Nat) (window : SourceWindow) (outMode : Bool)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount) :
    (rowCell C E prepared ctx tail source target sourceCounts targetCounts base window outMode input output).slots+
      (rowCell C E prepared ctx tail source target sourceCounts targetCounts base window outMode input output).arithmetic≤
        rowBudget C E prepared.K := by
  have hlo:=Nat.le_max_left (cellBudget C E prepared.K+4) 16
  have hhi:=Nat.le_max_right (cellBudget C E prepared.K+4) 16
  cases ctx with
  | none => simp only [rowCell,rowBudget]; omega
  | some ctx =>
    cases outMode with
    | true =>
      cases ho : ctx.over <;> simp only [rowCell,if_true,ho,filteredPointCell,rowBudget] <;> omega
    | false =>
      cases hn : ctx.normal with
      | none => simp only [rowCell,Bool.false_eq_true,if_false,hn,passCell,rowBudget]; omega
      | some maps =>
        have hh:=filteredCell_work C E prepared maps tail ctx.lo ctx.hi sourceCounts targetCounts
          base ctx.step ctx.start window input output
        simp only [rowCell,Bool.false_eq_true,if_false,hn,either,passCell,rowBudget]
        omega

structure CursorRow (m : Nat) where
  normal : MatrixResult m
  over : MatrixResult m

def rowMatrix (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (ctx : Option (RowContext C E)) (tail : Replay C E)
    (source target : Array Bool) (sourceCounts targetCounts : Array Nat)
    (base : Nat) (window : SourceWindow) : CursorRow (MaskedClusterStage.dfa C E).stateCount :=
  ⟨materialize (fun i j=>rowCell C E prepared ctx tail source target sourceCounts targetCounts base window false
      (MaskedClusterStage.decode C E i) (MaskedClusterStage.decode C E j)),
    materialize (fun i j=>rowCell C E prepared ctx tail source target sourceCounts targetCounts base window true
      (MaskedClusterStage.decode C E i) (MaskedClusterStage.decode C E j))⟩

def CursorRow.get {m : Nat} (row : CursorRow m) (mode : Bool) : MatrixResult m :=
  if mode then row.over else row.normal

theorem rowMatrix_get (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (ctx : Option (RowContext C E)) (tail : Replay C E)
    (source target : Array Bool) (sourceCounts targetCounts : Array Nat)
    (base : Nat) (window : SourceWindow) (mode : Bool)
    (i j : Fin (MaskedClusterStage.dfa C E).stateCount) :
    ((((rowMatrix C E prepared ctx tail source target sourceCounts targetCounts base window).get mode).cells.get i).get j)=
      (rowCell C E prepared ctx tail source target sourceCounts targetCounts base window mode
        (MaskedClusterStage.decode C E i) (MaskedClusterStage.decode C E j)).answer := by
  cases mode <;> exact materialize_get _ _ _

theorem rowMatrix_work (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (ctx : Option (RowContext C E)) (tail : Replay C E)
    (source target : Array Bool) (sourceCounts targetCounts : Array Nat)
    (base : Nat) (window : SourceWindow) (mode : Bool) :
    ((rowMatrix C E prepared ctx tail source target sourceCounts targetCounts base window).get mode).work≤
      (1+C.stateCount+E.stateCount)*((1+C.stateCount+E.stateCount)*(rowBudget C E prepared.K+1)) := by
  rw [←MaskedClusterStage.dfa_size C E]
  cases mode <;> apply materialize_work <;> intro i j <;>
    exact rowCell_work C E prepared ctx tail source target sourceCounts targetCounts base window _ _ _

end REWB.MaskedCluster
