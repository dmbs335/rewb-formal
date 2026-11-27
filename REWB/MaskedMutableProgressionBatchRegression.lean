import REWB.MaskedMutableProgressionBatchQuery

/-! Kernel regressions for the actual enumeration/source-update pipeline.
The empty-text boundary remains a singleton source; cubic-run witnesses
use the actual enumerator's descriptor IDs, never supplied indexes. -/
namespace REWB.MaskedMutableProgression.Batch.Regression
open REWB.RunGeometry REWB.Periodic

private def zero : Fin 1 := ⟨0,by decide⟩
private def emptyText : Array (Fin 1) := #[]

theorem empty_boundary :
    (member (run emptyText zero #[true] 1 []).singleton 0).1=true ∧
    (member (run emptyText zero #[true] 1 [0,0]).singleton 0).1=false := by
  constructor
  · rw [run_member emptyText zero #[true] 1 (by decide) [] 0]
    decide
  · have hh:=run_member emptyText zero #[true] 1 (by decide) [0,0] 0
    have hn : ¬(member (run emptyText zero #[true] 1 [0,0]).singleton 0).1=true := by
      rw [hh]
      decide
    exact Bool.eq_false_iff.mpr hn

private def cubeText : Array (Fin 1) := #[zero,zero,zero]
private def cube : Bounds := ⟨0,3,1⟩

private theorem cube_valid : cube.Valid (ArrayText.read cubeText zero) cubeText.size ∧
    3*cube.period≤cube.hi-cube.lo := by
  refine ⟨⟨by decide,by decide,by decide,⟨by decide,?_,?_⟩,Or.inl rfl,Or.inl rfl⟩,by decide⟩
  · intro i hi
    exact Subsingleton.elim _ _
  · intro q hq _
    change 1≤q
    omega

theorem actual_cube_survives :
    ∃id : Nat,(MaskedOrdered.Owner.enumerateAuto cubeText zero).runs.toArray[id]?=some cube ∧
      (queryRun (run cubeText zero #[true,true,true,true] 1 [0,2,0]) id 0 0 3 0).answer=true := by
  obtain ⟨id,hid⟩:=(prepare_run_exists cubeText zero #[true,true,true,true] 1 cube).mpr cube_valid
  rw [prepare_runs] at hid
  refine ⟨id,hid,?_⟩
  rw [run_query_correct cubeText zero #[true,true,true,true] 1 (by decide) [0,2,0] id 0 0 3 0 cube hid]
  exact ⟨1,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩

theorem actual_cube_exhausted :
    ∃id : Nat,(MaskedOrdered.Owner.enumerateAuto cubeText zero).runs.toArray[id]?=some cube ∧
      (queryRun (run cubeText zero #[true,true,true,true] 1 [0,1,2,3,0]) id 0 0 3 0).answer=false := by
  obtain ⟨id,hid⟩:=(prepare_run_exists cubeText zero #[true,true,true,true] 1 cube).mpr cube_valid
  rw [prepare_runs] at hid
  refine ⟨id,hid,Bool.eq_false_iff.mpr ?_⟩
  intro ha
  obtain ⟨k,_,hk,_,_,_,_,hn⟩:=(run_query_correct cubeText zero #[true,true,true,true] 1
    (by decide) [0,1,2,3,0] id 0 0 3 0 cube hid).mp ha
  simp only [cube,Nat.mul_one,Nat.zero_add,List.mem_cons,List.not_mem_nil,or_false] at hn
  omega

theorem repeated_delivery_bound (ps : List Nat) :
    (run cubeText zero #[true,true,true,true] 1 ps).delivered≤36 := by
  have hh:=run_delivered cubeText zero #[true,true,true,true] 1 (by decide) ps
  change _≤6*3*(Nat.log2 3+1) at hh
  have hl : Nat.log2 3=1 := by simp [Nat.log2]
  rw [hl] at hh
  exact hh

end REWB.MaskedMutableProgression.Batch.Regression
