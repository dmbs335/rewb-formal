import REWB.ResidualActualIndependent
import REWB.MaskedTraversalExecuteCostGrowth
import REWB.ResidualCachedCost

/-! Actual independent-capture text-work accounting. Both all-start
calls, their fixed-action charges, the regular-gap aggregate and every
endpoint query are included. The inherited periodic compiler scope is
unchanged; no machine-bit-cost claim is introduced. -/
namespace REWB.ResidualActual.Independent.Cost
open REWB.BoundaryRange
open REWB.ResidualCached.Growth
variable {σ : Nat}

def volume (n : Nat) : Nat := (n+2)*(height n)^3

theorem volume_length (n : Nat) : n+2≤volume n := by
  have h : 1≤(height n)^3 := Nat.pow_pos (by unfold height; omega)
  simpa only [volume,Nat.mul_one] using Nat.mul_le_mul_left (n+2) h

theorem volume_positive (n : Nat) : 1≤volume n := by
  have h:=volume_length n
  omega

theorem row_charged_closed (B C E : DFA (Fin σ)) (charge : Nat) :
    ∃coefficient,∀(text : Array (Fin σ)) (fallback : Fin σ) (source target : Array Bool),
      (MaskedAllStart.Rows.row B C E text fallback source target).work+
        charge*(MaskedAllStart.Rows.row B C E text fallback source target).fixedPatternBuilds≤
          coefficient*volume text.size := by
  obtain ⟨coefficient,hc⟩:=MaskedTraversalExecute.Cost.solve_charged_work_closed B C E charge
  refine ⟨coefficient+4,?_⟩
  intro text fallback source target
  have h:=hc text fallback source target
  have hv:=Nat.mul_le_mul_left 4 (volume_positive text.size)
  change (MaskedAllStart.solve B C E text fallback source target).accountedWork+4+
    charge*(MaskedAllStart.solve B C E text fallback source target).fixedPatternBuilds≤_
  have h' : (MaskedAllStart.solve B C E text fallback source target).accountedWork+
      charge*(MaskedAllStart.solve B C E text fallback source target).fixedPatternBuilds≤coefficient*volume text.size := by
    simpa only [volume,height,Nat.mul_assoc] using h
  rw [Nat.add_mul]
  omega

theorem execute_charged_closed (P : SevenDFA (Fin σ)) (charge : Nat) :
    ∃coefficient,∀(text : Array (Fin σ)) (fallback : Fin σ),
      (execute P text fallback).accountedWork+charge*(execute P text fallback).fixedPatternBuilds≤
        coefficient*volume text.size := by
  obtain ⟨leftCoefficient,leftBound⟩:=row_charged_closed
    (Automata.reverse P.B) (Automata.reverse P.C) (Automata.reverse P.A) charge
  obtain ⟨rightCoefficient,rightBound⟩:=row_charged_closed P.F P.G P.H charge
  refine ⟨leftCoefficient+rightCoefficient+(6*P.D.stateCount+46+3*charge),?_⟩
  intro text fallback
  let marks:=MaskedAllStart.Rows.full text.size
  let left:=MaskedAllStart.Rows.row (Automata.reverse P.B) (Automata.reverse P.C)
    (Automata.reverse P.A) text.reverse fallback marks marks
  let right:=MaskedAllStart.Rows.row P.F P.G P.H text fallback marks marks
  have hl:=leftBound text.reverse fallback marks marks
  rw [Array.size_reverse] at hl
  change left.work+charge*left.fixedPatternBuilds≤_ at hl
  have hr:=rightBound text fallback marks marks
  change right.work+charge*right.fixedPatternBuilds≤_ at hr
  have hp:=prepare_work P text fallback
  change (prepare P text fallback).work≤left.work+right.work+
    (6*P.D.stateCount+7)*(text.size+1)+4*text.size+12 at hp
  have he:=execute_work P text fallback
  have hb : (execute P text fallback).fixedPatternBuilds=
      left.fixedPatternBuilds+right.fixedPatternBuilds+3 := rfl
  have hn:=volume_length text.size
  have hpos:=volume_positive text.size
  have hg:=Nat.mul_le_mul_left (6*P.D.stateCount+7) (show text.size+1≤volume text.size by omega)
  have hq:=Nat.mul_le_mul_left 13 (show text.size+1≤volume text.size by omega)
  have hn':=Nat.mul_le_mul_left 5 (show text.size≤volume text.size by omega)
  have hc:=Nat.mul_le_mul_left (21+3*charge) hpos
  rw [hb]
  simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.mul_comm charge 3] at hp he hg hq hn' hc ⊢
  omega

theorem volume_rounded (n : Nat) :
    volume n≤(ThresholdBudget.base n)^75*(height n)^3 := by
  have h:=Nat.le_trans (ThresholdBudget.rounded_lower n)
    (ResidualCached.Rounded.power_le (ThresholdBudget.base n) 39 75
      (ThresholdBudget.base_pos n) (by decide))
  exact Nat.mul_le_mul_right ((height n)^3) h

theorem execute_charged_rounded (P : SevenDFA (Fin σ)) (charge : Nat) :
    ∃coefficient,∀(text : Array (Fin σ)) (fallback : Fin σ),
      (execute P text fallback).accountedWork+charge*(execute P text fallback).fixedPatternBuilds≤
        coefficient*(ThresholdBudget.base text.size)^75*(height text.size)^3 := by
  obtain ⟨coefficient,hc⟩:=execute_charged_closed P charge
  refine ⟨coefficient,?_⟩
  intro text fallback
  have h:=Nat.le_trans (hc text fallback) (Nat.mul_le_mul_left coefficient (volume_rounded text.size))
  simpa only [Nat.mul_assoc] using h

end REWB.ResidualActual.Independent.Cost
