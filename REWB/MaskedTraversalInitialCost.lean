import REWB.MaskedTraversalInitial

/-! Initialization ledger, including both actual run enumerations, the
physical bitmap union, history construction, and all initial source
erasures/fanout deliveries. The inherited periodic finite-compiler
exclusions are unchanged and remain explicit in `accountedWork`.
-/
namespace REWB.MaskedTraversalInitial
variable {σ : Nat}

def periodicBudget (B C E : DFA (Fin σ)) (n : Nat) : Nat :=
  let mass:=6*n*(n.log2+1)
  MaskedPeriodic.Batch.queryLimit B C E n*mass+6*mass+
    (n+1+MaskedPeriodic.Batch.preparationLimit n*mass)+
    MaskedRunEnumerationCost.coefficient σ*(n+1)*((n+1).log2+1)^2+(n.log2+1)*n

theorem periodic_work (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) :
    periodicUnits (MaskedPeriodic.Batch.solve B C E text fallback source target)≤periodicBudget B C E text.size := by
  obtain ⟨_,hq,hs,hp,he,hi⟩:=MaskedPeriodic.Batch.solve_work B C E text fallback source target
  unfold periodicUnits periodicBudget
  dsimp only
  rw [hi]
  omega

def initialBudget (B C E : DFA (Fin σ)) (n : Nat) : Nat :=
  (12*C.stateCount+6*E.stateCount+92)*(n+1)+periodicBudget B C E n+
    MaskedMutableProgression.Batch.totalBudget σ n (n+1)

theorem start_history_count (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) (K : Nat) :
    (start B C E text fallback source target K).answers.history.length≤text.size+1 := by
  rw [←(start_answers_valid B C E text fallback source target K).counted]
  exact start_count B C E text fallback source target K

theorem start_source_work (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) (K : Nat) (hK : 0<K) :
    (start B C E text fallback source target K).sources.totalWork≤
      MaskedMutableProgression.Batch.totalBudget σ text.size (text.size+1) := by
  have hh:=MaskedMutableProgression.Batch.run_total_work text fallback source K hK
    (start B C E text fallback source target K).answers.history
  have hc:=start_history_count B C E text fallback source target K
  have hm:=Nat.mul_le_mul_right ((text.size+2).log2+1) (Nat.mul_le_mul_left 46 hc)
  change (start B C E text fallback source target K).sources.totalWork≤_ at hh
  unfold MaskedMutableProgression.Batch.totalBudget MaskedMutableProgression.Batch.sourceUpdateBudget at hh ⊢
  omega

theorem start_accountedWork (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) (K : Nat) (hK : 0<K) :
    (start B C E text fallback source target K).accountedWork≤initialBudget B C E text.size := by
  have hs:=start_source_work B C E text fallback source target K hK
  have hp:=periodic_work B C E text fallback source target
  have he:=MaskedEmpty.solve_work B C E text.toList source target
  simp only [Array.length_toList] at he
  have ha : (start B C E text fallback source target K).answers.work=16*(text.size+1) := by
    change 16*(unionBits _ _ _).size=_
    rw [union_size]
  have h92 : (12*C.stateCount+6*E.stateCount+92)*(text.size+1)=
      (12*C.stateCount+6*E.stateCount+64)*(text.size+1)+16*(text.size+1)+12*(text.size+1) := by
    simp only [Nat.add_mul]
    omega
  unfold initialBudget
  rw [h92]
  change (MaskedEmpty.solve B C E text.toList source target).work+
      periodicUnits (MaskedPeriodic.Batch.solve B C E text fallback source target)+
      (start B C E text fallback source target K).answers.work+12*(text.size+1)+
      (start B C E text fallback source target K).sources.totalWork≤_
  rw [he,ha]
  omega

end REWB.MaskedTraversalInitial
