import REWB.MaskedPeriodicBatchCost

namespace REWB.MaskedPeriodic.Batch.Regression
open REWB.Periodic REWB.Spec REWB.MaskedProgression

def universal : DFA (Fin 2) := ⟨1,0,fun _ _=>0,fun _=>true⟩
def odd : DFA (Fin 2) := ⟨2,0,fun state letter=>
  if letter=1 then (if state=0 then 1 else 0) else state,fun state=>decide (state=1)⟩
def even : DFA (Fin 2) := ⟨2,0,fun state letter=>
  if letter=1 then (if state=0 then 1 else 0) else state,fun state=>decide (state=0)⟩
def text : Array (Fin 2) := #[1,1,1,1,1,1]
def sources : Array Bool := #[false,true,false,false,false,false,false]
def targets : Array Bool := #[false,false,false,true,false,false,false]

theorem unary_run : (⟨0,6,1⟩ : RunGeometry.Bounds).Valid (ArrayText.read text 0) 6 := by
  change Run (ArrayText.read text 0) 6 0 6 1
  refine ⟨by decide,by decide,by decide,?_,Or.inl rfl,Or.inl rfl⟩
  refine ⟨by decide,?_,?_⟩
  · intro i hi
    change i+1<6 at hi
    have hc : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
    rcases hc with rfl|rfl|rfl|rfl|rfl <;> rfl
  · intro q hq _
    change 1≤q
    omega

theorem unary_covered : Covered universal universal odd text 0 targets 1 := by
  refine ⟨⟨0,6,1⟩,unary_run,by decide,2,2,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;>
    (try simp only [DFA.accepts,Marked]) <;> decide

theorem full_batch_hit :
    readMask (solve universal universal odd text 0 sources targets).output.hits 1=true := by
  apply (solve_correct _ _ _ _ _ _ _ _).mpr
  exact ⟨rfl,unary_covered⟩

theorem excluded_source :
    readMask (solve universal universal odd text 0 sources targets).output.hits 0=false := by
  have hh:=solve_correct universal universal odd text 0 sources targets 0
  cases he : readMask (solve universal universal odd text 0 sources targets).output.hits 0
  · rfl
  · have hm:=(hh.mp he).1
    contradiction

theorem output_after_end :
    readMask (solve universal universal odd text 0 sources targets).output.hits 7=false := by
  unfold readMask
  rw [Array.getElem?_eq_none (by rw [solve_size]; decide)]
  rfl

end REWB.MaskedPeriodic.Batch.Regression
