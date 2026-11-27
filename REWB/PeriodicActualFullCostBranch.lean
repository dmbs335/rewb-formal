import REWB.PeriodicActualFullCostPrepareCost
import REWB.PeriodicActualBranchCost

/-! Measured primitive preparations are installed into the actual long
and short chronological joins. Each preparation and join executes once.
The complete previous BranchResult and Cubic Bool/work pair are retained
in the first projection; the second records the refined construction.
Five-variable P1 projection is unchanged in this correctness refinement. -/
namespace REWB.PeriodicActual.FullCost
variable {σ : Nat}

namespace Long

def solve (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    PeriodicActual.BranchResult×Nat :=
  let prepared:=prepare P f n Q
  let joined:=PeriodicActual.Join.run P.C prepared.1.modulus n
    prepared.1.text prepared.1.sources prepared.1.targets
  (⟨joined.1,prepared.1.work,joined.2⟩,
    prepared.2+joined.2+PeriodicActual.joinLedger joined.1+11)

theorem solve_value (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (solve P f n Q).1=PeriodicActual.Long.solve P f n Q := by
  simp only [solve,prepare_value,PeriodicActual.Long.solve]

theorem solve_answer (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (solve P f n Q).1.answer=(CountedSmallPeriodP1.solve P f n Q).answer := by
  rw [solve_value]
  exact PeriodicActual.Long.solve_value P f n Q

theorem solve_sound (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat)
    (h : (solve P f n Q).1.answer=true) :
    MatchesWithin P.nested1 (Periodic.segment f 0 n) 2 := by
  rw [solve_value] at h
  exact PeriodicActual.Long.solve_sound P f n Q h

theorem solve_work_le_base (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (solve P f n Q).2≤(PeriodicActual.Long.solve P f n Q).work+(prepare P f n Q).2+6 := by
  simp only [solve,prepare_value,PeriodicActual.Long.solve,PeriodicActual.BranchResult.work]
  omega

end Long

namespace Short

def solve (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    PeriodicActual.BranchResult×Nat :=
  let prepared:=prepare P f n Q
  let joined:=PeriodicActual.Join.run P.C prepared.1.modulus 0
    prepared.1.text prepared.1.sources prepared.1.targets
  (⟨joined.1,prepared.1.work,joined.2⟩,
    prepared.2+joined.2+PeriodicActual.joinLedger joined.1+11)

theorem solve_value (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (solve P f n Q).1=PeriodicActual.Short.solve P f n Q := by
  simp only [solve,prepare_value,PeriodicActual.Short.solve]

theorem solve_answer (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (solve P f n Q).1.answer=(CountedShortBranch.solve P f n Q).answer := by
  rw [solve_value]
  exact PeriodicActual.Short.solve_value P f n Q

theorem solve_sound (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat)
    (h : (solve P f n Q).1.answer=true) :
    MatchesWithin P.nested1 (Periodic.segment f 0 n) 2 := by
  rw [solve_value] at h
  exact PeriodicActual.Short.solve_sound P f n Q h

theorem solve_work_le_base (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (solve P f n Q).2≤(PeriodicActual.Short.solve P f n Q).work+(prepare P f n Q).2+6 := by
  simp only [solve,prepare_value,PeriodicActual.Short.solve,PeriodicActual.BranchResult.work]
  omega

end Short

namespace Cubic

def solve (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) : (Bool×Nat)×Nat :=
  let left:=Long.solve P f n Q
  let right:=Short.solve P f n Q
  ((left.1.answer || right.1.answer,left.1.work+right.1.work+3),left.2+right.2+9)

theorem solve_value (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (solve P f n Q).1=PeriodicActual.Cubic.solve P f n Q := by
  simp only [solve,Long.solve_value,Short.solve_value,PeriodicActual.Cubic.solve]

theorem solve_answer (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (solve P f n Q).1.1=(CountedP1Cubic.solve P f n Q).answer := by
  rw [solve_value]
  exact PeriodicActual.Cubic.solve_value P f n Q

theorem solve_work (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (solve P f n Q).2=(Long.solve P f n Q).2+(Short.solve P f n Q).2+9 := rfl

end Cubic
end REWB.PeriodicActual.FullCost
