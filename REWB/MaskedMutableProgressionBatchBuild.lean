import REWB.MaskedMutableProgressionBatch

/-! The initial per-run array is aligned with the one actual complete
cubic-run enumeration. Every row has exact current-source semantics;
the singleton snapshot also covers source boundaries in no cubic run. -/
namespace REWB.MaskedMutableProgression.Batch
open REWB.RunGeometry
open REWB.MaskedPeriodic.Batch (span totalSpan)
variable {σ : Nat}

theorem prepare_runs (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool) (K : Nat) :
    (prepare text fallback source K).runs=
      (MaskedOrdered.Owner.enumerateAuto text fallback).runs.toArray := rfl

theorem prepare_valid (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool)
    (K : Nat) (hK : 0<K) : Valid source [] (prepare text fallback source K) := by
  refine ⟨hK,MaskedSourceFanout.prepare_good text fallback,?_,?_,?_,?_,?_,?_⟩
  · exact MaskedSourceFanout.build_size text.size _
  · exact buildRows_size source K _
  · intro id R hR
    change (MaskedOrdered.Owner.enumerateAuto text fallback).runs.toArray[id]?=some R at hR
    rw [List.getElem?_toArray] at hR
    have hh:=(MaskedOrdered.Owner.enumerateAuto_mem text fallback R).mp (List.mem_of_getElem? hR)
    exact ⟨Nat.le_of_lt hh.1.1,hh.1.2.1,hh.1.2.2.2.1.1⟩
  · exact built_spec source 0 (text.size+1) 1
  · intro id R hR
    refine ⟨(build source R.lo (span R) (K*R.period)).index,?_,built_spec source _ _ _⟩
    change (buildRows source K (MaskedSourceFanout.prepare text fallback).runs).rows[id]?=_
    rw [buildRows_get]
    change (MaskedSourceFanout.prepare text fallback).runs[id]?=some R at hR
    rw [hR]
    rfl
  · intro p id
    simp only [List.not_mem_nil,not_false_eq_true,true_and]
    exact MaskedSourceFanout.prepare_mem text fallback p id

theorem prepare_run_exists (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool)
    (K : Nat) (R : Bounds) :
    (∃id : Nat,(prepare text fallback source K).runs[id]?=some R) ↔
      R.Valid (ArrayText.read text fallback) text.size ∧ 3*R.period≤R.hi-R.lo := by
  rw [prepare_runs]
  constructor
  · rintro ⟨id,hid⟩
    rw [List.getElem?_toArray] at hid
    exact (MaskedOrdered.Owner.enumerateAuto_mem text fallback R).mp (List.mem_of_getElem? hid)
  · intro hR
    have hm:=(MaskedOrdered.Owner.enumerateAuto_mem text fallback R).mpr hR
    have ha : R∈(MaskedOrdered.Owner.enumerateAuto text fallback).runs.toArray := by
      simpa only [Array.mem_toArray] using hm
    exact Array.getElem?_of_mem ha

theorem prepare_singleton_member (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool)
    (K p : Nat) :
    (member (prepare text fallback source K).singleton p).1=true ↔
      p≤text.size ∧ MaskedProgression.readMask source p=true := by
  change (member (build source 0 (text.size+1) 1).index p).1=true ↔ _
  rw [member_correct _ (build_valid source 0 (text.size+1) 1),build_live]
  constructor
  · rintro ⟨_,hb,hm⟩; exact ⟨by omega,hm⟩
  · rintro ⟨hp,hm⟩; exact ⟨Nat.zero_le _,by omega,hm⟩

end REWB.MaskedMutableProgression.Batch
