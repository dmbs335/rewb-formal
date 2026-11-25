import REWB.MaskedEmptyCost
import REWB.MaskedMutableProgressionBatchQuery

/-! Execute and report the empty-capture branch before processing positive
    lengths.  Its actual accepted boundaries are erased from the global
    mutable source indexes.  The target mask and complete occurrence sets
    are not part of that mutation.  The run enumerator is called once.
-/
namespace REWB.MaskedEmpty
open MaskedProgression (readMask)
namespace SourceBatch
abbrev Batch := MaskedMutableProgression.Batch.State
variable {σ : Nat}

def positions (bits : Array Bool) : List Nat :=
  (List.range bits.size).filter (readMask bits)

theorem positions_mem (bits : Array Bool) (p : Nat) :
    p∈positions bits ↔ readMask bits p=true := by
  simp only [positions,List.mem_filter,List.mem_range]
  constructor
  · exact And.right
  · intro hp
    refine ⟨?_,hp⟩
    by_cases hi : p<bits.size
    · exact hi
    · have ho : bits.size≤p := by omega
      simp only [readMask,Array.getElem?_eq_none ho,Option.getD,Bool.false_eq_true] at hp

theorem positions_length (bits : Array Bool) : (positions bits).length≤bits.size := by
  have hh:=List.length_filter_le (readMask bits) (List.range bits.size)
  simpa only [positions,List.length_range] using hh

theorem positions_nodup (bits : Array Bool) : (positions bits).Nodup :=
  List.Pairwise.filter (readMask bits) List.nodup_range

structure Started where
  empty : Result
  reported : List Nat
  sources : Batch
  work : Nat

def start (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) (K : Nat) : Started :=
  let empty:=solve B C E text.toList source target
  let reported:=positions empty.answers
  let sources:=MaskedMutableProgression.Batch.run text fallback source K reported
  -- Sixteen per boundary cover the array-to-list input adapter, the
  -- counted range/filter pass and output-list construction.
  ⟨empty,reported,sources,empty.work+16*(text.size+1)+sources.totalWork⟩

theorem start_reported (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) (K p : Nat) :
    p∈(start B C E text fallback source target K).reported ↔
      readMask source p=true ∧ Witness B C E text.toList target p := by
  change p∈positions _ ↔ _
  rw [positions_mem,solve_correct]

theorem start_count (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) (K : Nat) :
    (start B C E text fallback source target K).reported.length≤text.size+1 := by
  have hh:=positions_length (solve B C E text.toList source target).answers
  simpa only [solve_size,Array.length_toList] using hh

theorem start_nodup (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) (K : Nat) :
    (start B C E text fallback source target K).reported.Nodup := positions_nodup _

theorem start_valid (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) (K : Nat) (hK : 0<K) :
    MaskedMutableProgression.Batch.Valid source
      (start B C E text fallback source target K).reported
      (start B C E text fallback source target K).sources :=
  MaskedMutableProgression.Batch.run_valid text fallback source K hK _

theorem start_current (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) (K p : Nat) :
    MaskedMutableProgression.Batch.Current source
      (start B C E text fallback source target K).reported p ↔
      readMask source p=true ∧ ¬Witness B C E text.toList target p := by
  unfold MaskedMutableProgression.Batch.Current
  rw [start_reported]
  constructor
  · rintro ⟨hs,hn⟩
    exact ⟨hs,fun hw=>hn ⟨hs,hw⟩⟩
  · rintro ⟨hs,hn⟩
    exact ⟨hs,fun hw=>hn hw.2⟩

theorem start_member (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) (K : Nat) (hK : 0<K) (p : Nat) :
    (MaskedMutableProgression.member
      (start B C E text fallback source target K).sources.singleton p).1=true ↔
      p≤text.size ∧ readMask source p=true ∧ ¬Witness B C E text.toList target p := by
  have hh:=MaskedMutableProgression.Batch.run_member text fallback source K hK
    (start B C E text fallback source target K).reported p
  change (MaskedMutableProgression.member
    (start B C E text fallback source target K).sources.singleton p).1=true ↔
      p≤text.size ∧ MaskedMutableProgression.Batch.Current source
        (start B C E text fallback source target K).reported p at hh
  rw [start_current] at hh
  exact hh

theorem start_partition (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) (K p : Nat) :
    (readMask source p=true ∧ Spec.maskedStart B C E text.toList (readMask target) p) ↔
      p∈(start B C E text fallback source target K).reported ∨
        (MaskedMutableProgression.Batch.Current source
          (start B C E text fallback source target K).reported p ∧
            PositiveWitness B C E text.toList target p) := by
  rw [start_reported,start_current,maskedStart_partition]
  constructor
  · rintro ⟨hs,hz | hp⟩
    · exact Or.inl ⟨hs,hz⟩
    · by_cases hz : Witness B C E text.toList target p
      · exact Or.inl ⟨hs,hz⟩
      · exact Or.inr ⟨⟨hs,hz⟩,hp⟩
  · rintro (⟨hs,hz⟩ | ⟨⟨hs,_⟩,hp⟩)
    · exact ⟨hs,Or.inl hz⟩
    · exact ⟨hs,Or.inr hp⟩

theorem start_work (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) (K : Nat) (hK : 0<K) :
    (start B C E text fallback source target K).work≤
      (12*C.stateCount+6*E.stateCount+80)*(text.size+1)+
        MaskedMutableProgression.Batch.totalBudget σ text.size (text.size+1) := by
  have hc:=start_count B C E text fallback source target K
  have hw:=MaskedMutableProgression.Batch.run_total_work text fallback source K hK
    (start B C E text fallback source target K).reported
  have hm:=Nat.mul_le_mul_right ((text.size+2).log2+1) (Nat.mul_le_mul_left 46 hc)
  have he:=solve_work B C E text.toList source target
  rw [Array.length_toList] at he
  change _+_+_≤_
  rw [he]
  unfold MaskedMutableProgression.Batch.totalBudget
    MaskedMutableProgression.Batch.sourceUpdateBudget at hw ⊢
  change _≤_ at hw
  have hsum : (12*C.stateCount+6*E.stateCount+80)*(text.size+1)=
      (12*C.stateCount+6*E.stateCount+64)*(text.size+1)+16*(text.size+1) := by
    rw [show 12*C.stateCount+6*E.stateCount+80=
      (12*C.stateCount+6*E.stateCount+64)+16 by omega,Nat.add_mul]
  rw [hsum]
  dsimp only [start] at hw hm
  omega

end SourceBatch
end REWB.MaskedEmpty
