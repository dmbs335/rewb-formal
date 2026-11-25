import REWB.ResidualActualFullCostIndependent
import REWB.MaskedAllStartFullCostRowsCost
import REWB.ResidualActualIndependentCost

/-! The two actual measured rows and endpoint scan retain the linear
polylogarithmic envelope. Existing transition/query ledgers and the new
construction ledgers are combined explicitly; this is not a machine-bit,
reference-counting or allocation theorem. -/
namespace REWB.ResidualActual.FullCost.Independent.Cost
open REWB.BoundaryRange REWB.ResidualCached.Growth
variable {σ : Nat}

theorem execute_charged_closed (P : SevenDFA (Fin σ)) (charge : Nat) :
    ∃coefficient,∀(text : Array (Fin σ)) (fallback : Fin σ),
      (execute P text fallback).2+charge*(execute P text fallback).1.fixedPatternBuilds≤
        coefficient*ResidualActual.Independent.Cost.volume text.size := by
  obtain ⟨coefficient,hc⟩:=ResidualActual.Independent.Cost.execute_charged_closed P charge
  let leftCoefficient:=MaskedAllStart.FullCost.Rows.Cost.rowCoefficient
    (Automata.reverse P.B) (Automata.reverse P.C) (Automata.reverse P.A) 0
  let rightCoefficient:=MaskedAllStart.FullCost.Rows.Cost.rowCoefficient P.F P.G P.H 0
  refine ⟨coefficient+leftCoefficient+rightCoefficient,?_⟩
  intro text fallback
  have hold:=hc text fallback
  have he:=execute_work_le_base P text fallback
  have hl:=MaskedAllStart.FullCost.Rows.Cost.row_work
    (Automata.reverse P.B) (Automata.reverse P.C) (Automata.reverse P.A)
    text.reverse fallback (MaskedAllStart.Rows.full text.size) (MaskedAllStart.Rows.full text.size)
    0 text.size (by simp only [Array.size_reverse,Nat.le_refl])
  have hr:=MaskedAllStart.FullCost.Rows.Cost.row_work P.F P.G P.H
    text fallback (MaskedAllStart.Rows.full text.size) (MaskedAllStart.Rows.full text.size)
    0 text.size (Nat.le_refl _)
  simp only [Nat.zero_mul,Nat.add_zero] at hl hr
  change _≤leftCoefficient*ResidualActual.Independent.Cost.volume text.size at hl
  change _≤rightCoefficient*ResidualActual.Independent.Cost.volume text.size at hr
  rw [execute_builds]
  simp only [Nat.add_mul]
  omega

theorem execute_charged_rounded (P : SevenDFA (Fin σ)) (charge : Nat) :
    ∃coefficient,∀(text : Array (Fin σ)) (fallback : Fin σ),
      (execute P text fallback).2+charge*(execute P text fallback).1.fixedPatternBuilds≤
        coefficient*(ThresholdBudget.base text.size)^75*(height text.size)^3 := by
  obtain ⟨coefficient,hc⟩:=execute_charged_closed P charge
  refine ⟨coefficient,?_⟩
  intro text fallback
  have h:=Nat.le_trans (hc text fallback) (Nat.mul_le_mul_left coefficient
    (ResidualActual.Independent.Cost.volume_rounded text.size))
  simpa only [Nat.mul_assoc] using h

theorem execute_work_closed (P : SevenDFA (Fin σ)) :
    ∃coefficient,∀(text : Array (Fin σ)) (fallback : Fin σ),
      (execute P text fallback).2≤
        coefficient*ResidualActual.Independent.Cost.volume text.size := by
  simpa only [Nat.zero_mul,Nat.add_zero] using execute_charged_closed P 0

end REWB.ResidualActual.FullCost.Independent.Cost
