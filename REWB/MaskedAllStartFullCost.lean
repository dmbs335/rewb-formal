import REWB.MaskedAllStartFullCostPrepare
import REWB.MaskedAllStartFullCostExecute
import REWB.MaskedTraversalExecuteCostGrowth

/-! Actual all-start execution with the measured construction paths
installed. The old result is retained as the first projection so its
unconditional correctness and source-history theorems transfer exactly.
The second projection sums the executed preparation, execution and source
fanout ledgers; no caller supplies a budget or correctness premise. -/
namespace REWB.MaskedAllStart.FullCost
open REWB.ResidualCached.Growth
variable {σ : Nat}

def solve (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) :
    PeriodicConstruction.Result (MaskedAllStart.Result C E (MaskedSuffixClass.height text.size)) :=
  let ⟨prepared,prepareWork⟩:=prepare B C E text fallback source target
  let ⟨out,executeWork⟩:=Execution.plan prepared.env prepared.template.capacity
    prepared.template prepared.geometry.plan prepared.global
  let fanout:=out.global.store.sources.updateWork-prepared.initialSourceWork
  (⟨out,prepared.preparationWork+out.global.stats.work+fanout,out.global.stats.actionBuilds+1⟩,
    prepareWork+executeWork+fanout+10)

theorem solve_value (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) :
    (solve B C E text fallback source target).1=MaskedAllStart.solve B C E text fallback source target := by
  simp only [solve,prepare_value,Execution.plan_value,MaskedAllStart.solve]

theorem solve_correct (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) (p : Nat) :
    MaskedProgression.readMask (solve B C E text fallback source target).1.bits p=true ↔
      MaskedProgression.readMask source p=true ∧
        Spec.maskedStart B C E text.toList (MaskedProgression.readMask target) p := by
  rw [solve_value]
  exact MaskedAllStart.solve_correct B C E text fallback source target p

def solveBudget (B C E : DFA (Fin σ)) (n : Nat) : Nat :=
  preparationBudget B C E n+
    (Execution.coefficient B C E (MaskedCluster.modulus C.stateCount E.stateCount)+1)*
      MaskedTraversalExecute.Cost.executionBudget B C E n+10

theorem solve_work (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) :
    (solve B C E text fallback source target).2≤solveBudget B C E text.size := by
  let prepared:=(prepare B C E text fallback source target).1
  let raw:=Execution.plan prepared.env prepared.template.capacity
    prepared.template prepared.geometry.plan prepared.global
  let old:=MaskedAllStart.solve B C E text fallback source target
  let F:=Execution.coefficient B C E (MaskedCluster.modulus C.stateCount E.stateCount)
  have value : raw.1=old.output := by
    dsimp only [raw]
    rw [Execution.plan_value]
    dsimp only [prepared]
    rw [prepare_value]
    rfl
  have tiny : PeriodicConstruction.Cut.Tiny prepared.env.cut.tree :=
    prepare_tiny B C E text fallback source target
  have hw:=Execution.plan_work prepared.env prepared.template.capacity prepared.template
    prepared.geometry.plan prepared.global tiny
  rw [←Execution.plan_value prepared.env prepared.template.capacity prepared.template
    prepared.geometry.plan prepared.global] at hw
  change raw.2≤Execution.coefficient B C E prepared.env.repair.shared.prepared.K*raw.1.global.stats.work at hw
  rw [value] at hw
  have hk:=prepare_modulus B C E text fallback source target
  change prepared.env.repair.shared.prepared.K=MaskedCluster.modulus C.stateCount E.stateCount at hk
  rw [hk] at hw
  change raw.2≤F*old.output.global.stats.work at hw
  have ho : old.output.global.stats.work+
      (old.output.global.store.sources.updateWork-prepared.initialSourceWork)≤
        MaskedTraversalExecute.Cost.executionBudget B C E text.size := by
    dsimp only [prepared]
    rw [prepare_value]
    exact MaskedTraversalExecute.Cost.solve_execution_work B C E text fallback source target
  have hm:=Nat.mul_le_mul_left F
    (show old.output.global.stats.work≤MaskedTraversalExecute.Cost.executionBudget B C E text.size by omega)
  have hp:=prepare_work B C E text fallback source target
  change (prepare B C E text fallback source target).2+raw.2+
    (raw.1.global.store.sources.updateWork-prepared.initialSourceWork)+10≤_
  rw [value]
  change (prepare B C E text fallback source target).2+raw.2+
    (old.output.global.store.sources.updateWork-prepared.initialSourceWork)+10≤
      preparationBudget B C E text.size+(F+1)*MaskedTraversalExecute.Cost.executionBudget B C E text.size+10
  rw [Nat.add_mul,Nat.one_mul]
  omega

theorem solve_profile (B C E : DFA (Fin σ)) :
    ∃coefficient,∀n s,Bound n s (solveBudget B C E n) 1 0 0 3 coefficient := by
  obtain ⟨cp,hp⟩:=preparation_profile B C E
  obtain ⟨ce,he⟩:=MaskedTraversalExecute.Cost.execution_profile B C E
  let F:=Execution.coefficient B C E (MaskedCluster.modulus C.stateCount E.stateCount)+1
  refine ⟨cp+F*ce+10,?_⟩
  intro n s
  have hm:=REWB.ResidualCached.Growth.mul (constant n s F) (he n s)
  have hs:=REWB.ResidualCached.Growth.add
    (REWB.ResidualCached.Growth.add (hp n s) hm) (constant n s 10)
  simpa only [solveBudget,F,Nat.zero_add,Nat.zero_max,Nat.max_zero,Nat.max_self,
    show max 2 3=3 by decide] using hs

theorem solve_work_closed (B C E : DFA (Fin σ)) :
    ∃coefficient,∀(text : Array (Fin σ)) (fallback : Fin σ) (source target : Array Bool),
      (solve B C E text fallback source target).2≤
        coefficient*(text.size+2)*(height text.size)^3 := by
  obtain ⟨coefficient,hc⟩:=solve_profile B C E
  refine ⟨coefficient,?_⟩
  intro text fallback source target
  have hh:=Nat.le_trans (solve_work B C E text fallback source target) (hc text.size 1)
  simpa only [Bound,scale,Nat.pow_one,Nat.pow_zero,Nat.mul_one,Nat.mul_assoc] using hh

theorem solve_charged_work_closed (B C E : DFA (Fin σ)) (fixedCharge : Nat) :
    ∃coefficient,∀(text : Array (Fin σ)) (fallback : Fin σ) (source target : Array Bool),
      (solve B C E text fallback source target).2+
        fixedCharge*(solve B C E text fallback source target).1.fixedPatternBuilds≤
          coefficient*(text.size+2)*(height text.size)^3 := by
  obtain ⟨ca,ha⟩:=solve_work_closed B C E
  obtain ⟨cb,hb⟩:=MaskedTraversalExecute.Cost.solve_charged_work_closed B C E fixedCharge
  refine ⟨ca+cb,?_⟩
  intro text fallback source target
  have first:=ha text fallback source target
  have second:=hb text fallback source target
  rw [solve_value]
  change (solve B C E text fallback source target).2+
    fixedCharge*(MaskedAllStart.solve B C E text fallback source target).fixedPatternBuilds≤
      (ca+cb)*(text.size+2)*(height text.size)^3
  dsimp only [height] at first ⊢
  rw [Nat.add_mul,Nat.add_mul]
  omega

end REWB.MaskedAllStart.FullCost
