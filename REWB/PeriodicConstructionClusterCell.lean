import REWB.PeriodicConstructionClusterQuery
import REWB.MaskedClusterMutableCursor

/-! Concrete one-jump cells including acceptance-map preparation and
finite formula compilation. Source cells use the persistent current
source index; target cells retain the immutable prefix counts. Exact
Answer equality permits substitution into existing bank builders. -/
namespace REWB.PeriodicConstruction.Cluster
open REWB.PeriodicConstruction REWB.MaskedCluster
variable {α : Type}

def cell (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (maps : Context C E) (tail : Replay C E) (lo hi : Nat) (idx : Mutable.Index)
    (targetCounts : Array Nat) (q s : Nat) (window : SourceWindow) :
    MaskedClusterStage.State C.stateCount E.stateCount→
      MaskedClusterStage.State C.stateCount E.stateCount→Result Mutable.Answer
  | .waiting,.gap output =>
    let a:=Masked.always C
    let b:=Masked.exit C maps.rightC tail.1 maps.afterC output
    let out:=sourcePairQuery a.1 b.1 lo hi idx q s prepared.K window
    (out.1,a.2+b.2+out.2+5)
  | .gap input,.suffix output =>
    let a:=Masked.entry C E maps input
    let b:=Masked.exit E maps.rightE tail.2 maps.afterE output
    let out:=pairQuery a.1 b.1 lo hi targetCounts idx.base q s prepared.K
    (Mutable.ofStatic out.1,a.2+b.2+out.2+6)
  | _,_ => (⟨false,1⟩,2)

def cellCost (c e K : Nat) : Nat :=
  14*c+6*e+sourceCost c c K+pairCost c e K+20

theorem cell_value (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (maps : Context C E) (tail : Replay C E) (lo hi : Nat) (idx : Mutable.Index)
    (targetCounts : Array Nat) (q s : Nat) (window : SourceWindow)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount) :
    (cell C E prepared maps tail lo hi idx targetCounts q s window input output).1=
      Mutable.cell C E prepared maps tail lo hi idx targetCounts q s window input output := by
  cases input <;> cases output <;>
    simp only [cell,sourcePairQuery_value,pairQuery_value,Masked.always_value,
      Masked.entry_value,Masked.exit_value,Mutable.cell,MaskedCluster.cell,Mutable.ofStatic]

theorem cell_extra (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (maps : Context C E) (tail : Replay C E) (lo hi : Nat) (idx : Mutable.Index)
    (targetCounts : Array Nat) (q s : Nat) (window : SourceWindow)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount) :
    (cell C E prepared maps tail lo hi idx targetCounts q s window input output).2≤
      (Mutable.cell C E prepared maps tail lo hi idx targetCounts q s window input output).work+
      cellCost C.stateCount E.stateCount prepared.K := by
  cases input with
  | waiting =>
    cases output with
    | gap output =>
      have ha:=Masked.always_work C
      have hb:=Masked.exit_work C maps.rightC tail.1 maps.afterC output
      have hc:=sourcePairQuery_extra (Masked.always C).1
        (Masked.exit C maps.rightC tail.1 maps.afterC output).1 lo hi idx q s prepared.K window
      rw [Masked.always_value,Masked.exit_value] at hc
      simp only [cell,Mutable.cell,cellCost]
      omega
    | waiting => simp only [cell,Mutable.cell,MaskedCluster.cell,Mutable.ofStatic,cellCost]; omega
    | suffix output => simp only [cell,Mutable.cell,MaskedCluster.cell,Mutable.ofStatic,cellCost]; omega
  | gap input =>
    cases output with
    | suffix output =>
      have ha:=Masked.entry_work C E maps input
      have hb:=Masked.exit_work E maps.rightE tail.2 maps.afterE output
      have hc:=pairQuery_extra (Masked.entry C E maps input).1
        (Masked.exit E maps.rightE tail.2 maps.afterE output).1 lo hi targetCounts idx.base q s prepared.K
      rw [Masked.entry_value,Masked.exit_value] at hc
      simp only [cell,Mutable.cell,MaskedCluster.cell,Mutable.ofStatic,cellCost]
      omega
    | waiting => simp only [cell,Mutable.cell,MaskedCluster.cell,Mutable.ofStatic,cellCost]; omega
    | gap output => simp only [cell,Mutable.cell,MaskedCluster.cell,Mutable.ofStatic,cellCost]; omega
  | suffix input =>
    cases output <;> simp only [cell,Mutable.cell,MaskedCluster.cell,Mutable.ofStatic,cellCost] <;> omega

theorem cell_inflate (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (maps : Context C E) (tail : Replay C E) (lo hi : Nat) (idx : Mutable.Index)
    (targetCounts : Array Nat) (q s : Nat) (window : SourceWindow)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount) :
    (cell C E prepared maps tail lo hi idx targetCounts q s window input output).2≤
      (cellCost C.stateCount E.stateCount prepared.K+1)*
      ((Mutable.cell C E prepared maps tail lo hi idx targetCounts q s window input output).work+1) :=
  Nat.le_trans (cell_extra C E prepared maps tail lo hi idx targetCounts q s window input output)
    (Masked.inflate _ _)

def rowCell (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (ctx : Option (RowContext C E)) (tail : Replay C E) (idx : Mutable.Index)
    (target : Array Bool) (targetCounts : Array Nat) (window : SourceWindow) (outMode : Bool)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount) : Result Mutable.Answer :=
  match ctx with
  | none => (⟨false,1⟩,2)
  | some ctx =>
    if outMode then
      match ctx.over with
      | none => (⟨false,1⟩,4)
      | some maps =>
        let out:=Mutable.pointCell C E maps tail idx target ctx.last window input output
        (out,out.work+7)
    else
      let pass:=Mutable.ofStatic (passCell C E ctx.pass input output)
      match ctx.normal with
      | none => (pass,pass.work+6)
      | some maps =>
        let out:=cell C E prepared maps tail ctx.lo ctx.hi idx targetCounts ctx.step ctx.start window input output
        (Mutable.either pass out.1,pass.work+out.2+8)

theorem rowCell_value (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (ctx : Option (RowContext C E)) (tail : Replay C E) (idx : Mutable.Index)
    (target : Array Bool) (targetCounts : Array Nat) (window : SourceWindow) (outMode : Bool)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount) :
    (rowCell C E prepared ctx tail idx target targetCounts window outMode input output).1=
      Mutable.rowCell C E prepared ctx tail idx target targetCounts window outMode input output := by
  cases ctx with
  | none => rfl
  | some ctx =>
    cases outMode with
    | true => cases h : ctx.over <;> simp only [rowCell,Mutable.rowCell,if_true,h]
    | false => cases h : ctx.normal <;>
        simp only [rowCell,Mutable.rowCell,Bool.false_eq_true,if_false,h,cell_value]

theorem rowCell_extra (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (ctx : Option (RowContext C E)) (tail : Replay C E) (idx : Mutable.Index)
    (target : Array Bool) (targetCounts : Array Nat) (window : SourceWindow) (outMode : Bool)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount) :
    (rowCell C E prepared ctx tail idx target targetCounts window outMode input output).2≤
      (Mutable.rowCell C E prepared ctx tail idx target targetCounts window outMode input output).work+
      cellCost C.stateCount E.stateCount prepared.K+8 := by
  cases ctx with
  | none => simp only [rowCell,Mutable.rowCell]; omega
  | some ctx =>
    cases outMode with
    | true =>
      cases h : ctx.over <;> simp only [rowCell,Mutable.rowCell,if_true,h] <;> omega
    | false =>
      cases h : ctx.normal with
      | none => simp only [rowCell,Mutable.rowCell,Bool.false_eq_true,if_false,h]; omega
      | some maps =>
        have hc:=cell_extra C E prepared maps tail ctx.lo ctx.hi idx targetCounts ctx.step ctx.start window input output
        simp only [rowCell,Mutable.rowCell,Bool.false_eq_true,if_false,h,Mutable.either]
        omega

end REWB.PeriodicConstruction.Cluster
