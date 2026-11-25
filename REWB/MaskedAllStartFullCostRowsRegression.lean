import REWB.ResidualActualFullCostInputsCost

/-! Small kernel regressions for restoring dependent tables while keeping
the two ledgers separate. Actual solver and table executions are exercised
by the bounded compiled probe. -/
namespace REWB.MaskedAllStart.FullCost.Rows.Regression

def tiny : BoundaryRange.Table.Index (fun _ : Fin 3=>Nat)×Nat :=
  FullCost.Table.build fun i : Fin 3=>((2*i.val,7+i.val),11+i.val)

theorem tiny_value : BoundaryRange.Table.get tiny.1 ⟨2,by decide⟩=4 := by decide
theorem tiny_old_work : tiny.1.work=34 := by decide
theorem tiny_full_work : tiny.2=81 := by decide

def dependent : BoundaryRange.Table.Index (fun i : Fin 3=>Fin (i.val+1))×Nat :=
  FullCost.Table.build fun i : Fin 3=>((⟨i.val,by omega⟩,i.val+2),i.val+5)

theorem dependent_value :
    (BoundaryRange.Table.get dependent.1 ⟨2,by decide⟩).val=2 := by decide
theorem empty_work :
    (FullCost.Table.build (F:=fun _ : Fin 0=>Nat) (fun i=>Fin.elim0 i)).2=6 := by decide

end REWB.MaskedAllStart.FullCost.Rows.Regression
