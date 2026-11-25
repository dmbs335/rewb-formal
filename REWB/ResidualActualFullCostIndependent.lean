import REWB.ResidualActualIndependent
import REWB.MaskedAllStartFullCostRows

/-! The independent-capture branch executes two construction-counted
all-start rows, then the existing backwards regular-gap aggregate and
endpoint scan. Both captured words remain independent. The first
projection preserves every original result field; the second adds the
actual row-construction work. Old computations are proof comparators,
never extra executable calls. -/
namespace REWB.ResidualActual.FullCost.Independent
open REWB.BoundaryRange REWB.OneUseRange
variable {σ : Nat}

def prepare (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) :
    ResidualActual.Independent.Index×Nat :=
  let marks:=MaskedAllStart.Rows.full text.size
  let reversed:=text.reverse
  let ends:=MaskedAllStart.FullCost.Rows.row
    (Automata.reverse P.B) (Automata.reverse P.C) (Automata.reverse P.A)
    reversed fallback marks marks
  let starts:=MaskedAllStart.FullCost.Rows.row P.F P.G P.H text fallback marks marks
  let suffix:=FarAggregate.build P.D text starts.1.bits
  (⟨text.size,ends.1.bits,suffix,ends.1.work+starts.1.work+suffix.work+4*text.size+12,
    ends.1.fixedPatternBuilds+starts.1.fixedPatternBuilds+3⟩,
    ends.2+starts.2+suffix.work+4*text.size+12)

theorem prepare_value (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) :
    (prepare P text fallback).1=ResidualActual.Independent.prepare P text fallback := by
  simp only [prepare,ResidualActual.Independent.prepare,MaskedAllStart.FullCost.Rows.row_value]

theorem prepare_work (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) :
    (prepare P text fallback).2=
      (MaskedAllStart.FullCost.Rows.row
        (Automata.reverse P.B) (Automata.reverse P.C) (Automata.reverse P.A)
        text.reverse fallback (MaskedAllStart.Rows.full text.size) (MaskedAllStart.Rows.full text.size)).2+
      (MaskedAllStart.FullCost.Rows.row P.F P.G P.H text fallback
        (MaskedAllStart.Rows.full text.size) (MaskedAllStart.Rows.full text.size)).2+
      (FarAggregate.build P.D text
        (MaskedAllStart.FullCost.Rows.row P.F P.G P.H text fallback
          (MaskedAllStart.Rows.full text.size) (MaskedAllStart.Rows.full text.size)).1.bits).work+
      4*text.size+12 := rfl

theorem prepare_work_le_base (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) :
    (prepare P text fallback).2≤(ResidualActual.Independent.prepare P text fallback).work+
      (MaskedAllStart.FullCost.Rows.row
        (Automata.reverse P.B) (Automata.reverse P.C) (Automata.reverse P.A)
        text.reverse fallback (MaskedAllStart.Rows.full text.size) (MaskedAllStart.Rows.full text.size)).2+
      (MaskedAllStart.FullCost.Rows.row P.F P.G P.H text fallback
        (MaskedAllStart.Rows.full text.size) (MaskedAllStart.Rows.full text.size)).2 := by
  unfold prepare ResidualActual.Independent.prepare
  simp only [MaskedAllStart.FullCost.Rows.row_value]
  dsimp only
  omega

def execute (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) :
    ResidualActual.Independent.Execution×Nat :=
  let idx:=prepare P text fallback
  let checked:=ResidualCached.any (ResidualActual.Independent.query idx.1) (List.range (idx.1.length+1))
  (⟨checked.1,idx.1.work+checked.2+idx.1.length+8,idx.1.fixedPatternBuilds⟩,
    idx.2+checked.2+idx.1.length+8)

theorem execute_value (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) :
    (execute P text fallback).1=ResidualActual.Independent.execute P text fallback := by
  simp only [execute,prepare_value,ResidualActual.Independent.execute]

theorem execute_correct (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) :
    (execute P text fallback).1.answer=true ↔ MatchesWithin P.independent text.toList 2 := by
  rw [execute_value]
  exact ResidualActual.Independent.execute_correct P text fallback

theorem execute_builds (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) :
    (execute P text fallback).1.fixedPatternBuilds=
      (ResidualActual.Independent.execute P text fallback).fixedPatternBuilds := by
  rw [execute_value]

theorem execute_work (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) :
    (execute P text fallback).2≤(prepare P text fallback).2+13*(text.size+1)+text.size+9 := by
  have h:=ResidualCached.any_work
    (ResidualActual.Independent.query (ResidualActual.Independent.prepare P text fallback))
    (List.range (text.size+1)) 10
    (fun t _=>ResidualActual.Independent.query_work _ t)
  rw [List.length_range] at h
  unfold execute
  rw [prepare_value]
  dsimp only
  change (prepare P text fallback).2+
    (ResidualCached.any
      (ResidualActual.Independent.query (ResidualActual.Independent.prepare P text fallback))
      (List.range (text.size+1))).2+text.size+8≤_
  omega

theorem execute_work_le_base (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) :
    (execute P text fallback).2≤(ResidualActual.Independent.execute P text fallback).accountedWork+
      (MaskedAllStart.FullCost.Rows.row
        (Automata.reverse P.B) (Automata.reverse P.C) (Automata.reverse P.A)
        text.reverse fallback (MaskedAllStart.Rows.full text.size) (MaskedAllStart.Rows.full text.size)).2+
      (MaskedAllStart.FullCost.Rows.row P.F P.G P.H text fallback
        (MaskedAllStart.Rows.full text.size) (MaskedAllStart.Rows.full text.size)).2 := by
  have hp:=prepare_work_le_base P text fallback
  unfold execute ResidualActual.Independent.execute
  rw [prepare_value]
  dsimp only
  omega

end REWB.ResidualActual.FullCost.Independent
