import REWB.MaskedEmptyBatch

namespace REWB.MaskedEmpty.SourceBatch.Regression

def allWords : DFA (Fin 2) :=
  ⟨1,⟨0,by decide⟩,fun _ _=>⟨0,by decide⟩,fun _=>true⟩
def nonempty : DFA (Fin 2) :=
  ⟨2,⟨0,by decide⟩,fun _ _=>⟨1,by decide⟩,fun q=>decide (q.val=1)⟩

def middle := start allWords allWords allWords #[0,0,0] 0
  #[true,true,true,true] #[false,false,true,false] 1

theorem reports_once : middle.reported=[0,1,2] ∧ middle.sources.requests=3 := by decide

theorem remaining_terminal :
    (MaskedMutableProgression.member middle.sources.singleton 0).1=false ∧
    (MaskedMutableProgression.member middle.sources.singleton 2).1=false ∧
    (MaskedMutableProgression.member middle.sources.singleton 3).1=true := by
  have h (p : Nat) := MaskedMutableProgression.Batch.run_member
    (#[0,0,0] : Array (Fin 2)) 0 #[true,true,true,true] 1 (by decide) middle.reported p
  change ∀p,(MaskedMutableProgression.member middle.sources.singleton p).1=true ↔ _ at h
  refine ⟨Bool.eq_false_iff.mpr ?_,Bool.eq_false_iff.mpr ?_,?_⟩
  · change ¬(MaskedMutableProgression.member middle.sources.singleton 0).1=true
    rw [h 0]; decide
  · change ¬(MaskedMutableProgression.member middle.sources.singleton 2).1=true
    rw [h 2]; decide
  · rw [h 3]; decide

theorem positive_B_preserves_sources :
    (start nonempty allWords allWords #[0] 0 #[true,true] #[true,true] 1).reported=[] ∧
    (start nonempty allWords allWords #[0] 0 #[true,true] #[true,true] 1).sources.requests=0 := by decide

theorem empty_text_is_reported :
    (start allWords allWords allWords #[] 0 #[true] #[true] 1).reported=[0] ∧
    (MaskedMutableProgression.member
      (start allWords allWords allWords #[] 0 #[true] #[true] 1).sources.singleton 0).1=false := by
  refine ⟨by decide,Bool.eq_false_iff.mpr ?_⟩
  change ¬(MaskedMutableProgression.member
    (MaskedMutableProgression.Batch.run (#[] : Array (Fin 2)) 0 #[true] 1 [0]).singleton 0).1=true
  rw [MaskedMutableProgression.Batch.run_member _ _ _ _ (by decide)]
  decide

end REWB.MaskedEmpty.SourceBatch.Regression
