import REWB.PeriodicActualPrepare
import REWB.PeriodicActualJoinCost
import REWB.PeriodicAccounting

/-! Executable P1 branches using the measured preparation and join.
Each branch prepares its actual event lists once and calls the actual
measured chronological join once. The result retains the original join
counters and the separate construction ledger from that same call.
The existing public matcher is not changed by this module. -/
namespace REWB.PeriodicActual
open REWB.PeriodicConstruction
variable {σ : Nat}

/-- The established sorting and chronological counters of one join. -/
def joinLedger (r : CountedJoin.Result) : Nat :=
  r.value.tests+r.value.eventVisits+r.value.textVisits+r.value.nodes+r.sortSteps

structure BranchResult where
  joined : CountedJoin.Result
  preparationWork : Nat
  constructionWork : Nat

def BranchResult.answer (r : BranchResult) : Bool := r.joined.value.answer

def BranchResult.work (r : BranchResult) : Nat :=
  r.preparationWork+r.constructionWork+joinLedger r.joined+5

namespace Long

def solve (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n Q : Nat) : BranchResult :=
  let prepared := prepare P f n Q
  let ⟨joined,construction⟩ := Join.run P.C prepared.modulus n
    prepared.text prepared.sources prepared.targets
  ⟨joined,prepared.work,construction⟩

theorem solve_join (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n Q : Nat) :
    (solve P f n Q).joined=
      ⟨(CountedSmallPeriodP1.solve P f n Q).toResult,
        (CountedSmallPeriodP1.solve P f n Q).sortSteps⟩ := by
  simp only [solve,Join.run_value,prepare_text,prepare_sources,prepare_targets,prepare_modulus]
  rfl

theorem solve_value (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n Q : Nat) :
    (solve P f n Q).answer=(CountedSmallPeriodP1.solve P f n Q).answer := by
  unfold BranchResult.answer
  rw [solve_join]
  rfl

theorem solve_original (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n Q : Nat) :
    (solve P f n Q).answer=(P1Events.solve P f n Q).answer := by
  rw [solve_value,CountedSmallPeriodP1.solve_answer]

theorem solve_sound (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n Q : Nat)
    (h : (solve P f n Q).answer=true) :
    MatchesWithin P.nested1 (Periodic.segment f 0 n) 2 := by
  rw [solve_value] at h
  exact CountedSmallPeriodP1.solve_sound P f n Q h

theorem solve_preparationWork (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n Q : Nat) :
    (solve P f n Q).preparationWork=(prepare P f n Q).work := by
  simp only [solve]

theorem solve_constructionWork (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n Q : Nat) :
    (solve P f n Q).constructionWork=
      (Join.run P.C (prepare P f n Q).modulus n (prepare P f n Q).text
        (prepare P f n Q).sources (prepare P f n Q).targets).2 := by
  simp only [solve]

theorem solve_work (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n Q : Nat) :
    (solve P f n Q).work=(prepare P f n Q).work+
      (Join.run P.C (prepare P f n Q).modulus n (prepare P f n Q).text
        (prepare P f n Q).sources (prepare P f n Q).targets).2+
      joinLedger ⟨(CountedSmallPeriodP1.solve P f n Q).toResult,
        (CountedSmallPeriodP1.solve P f n Q).sortSteps⟩+5 := by
  rw [BranchResult.work,solve_preparationWork,solve_constructionWork,solve_join]

theorem solve_joinLedger (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n Q : Nat) :
    joinLedger (solve P f n Q).joined≤
      PeriodicAccounting.longWork (CountedSmallPeriodP1.solve P f n Q) := by
  rw [solve_join]
  unfold joinLedger PeriodicAccounting.longWork
  omega

end Long

namespace Short

def solve (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n Q : Nat) : BranchResult :=
  let prepared := prepare P f n Q
  let ⟨joined,construction⟩ := Join.run P.C prepared.modulus 0
    prepared.text prepared.sources prepared.targets
  ⟨joined,prepared.work,construction⟩

theorem solve_join (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n Q : Nat) :
    (solve P f n Q).joined=
      ⟨(CountedShortBranch.solve P f n Q).toResult,
        (CountedShortBranch.solve P f n Q).sortSteps⟩ := by
  simp only [solve,Join.run_value,prepare_text,prepare_sources,prepare_targets,prepare_modulus,
    CountedShortBranch.solve,CountedShortBranch.sourceEvents_value,CountedShortTargets.targets_value]
  rfl

theorem solve_value (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n Q : Nat) :
    (solve P f n Q).answer=(CountedShortBranch.solve P f n Q).answer := by
  unfold BranchResult.answer
  rw [solve_join]
  rfl

theorem solve_original (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n Q : Nat) :
    (solve P f n Q).answer=(P1ShortBranch.solve P f n Q).answer := by
  rw [solve_value,CountedShortBranch.solve_answer]

theorem solve_sound (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n Q : Nat)
    (h : (solve P f n Q).answer=true) :
    MatchesWithin P.nested1 (Periodic.segment f 0 n) 2 := by
  rw [solve_value] at h
  exact CountedShortBranch.solve_sound P f n Q h

theorem solve_preparationWork (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n Q : Nat) :
    (solve P f n Q).preparationWork=(prepare P f n Q).work := by
  simp only [solve]

theorem solve_constructionWork (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n Q : Nat) :
    (solve P f n Q).constructionWork=
      (Join.run P.C (prepare P f n Q).modulus 0 (prepare P f n Q).text
        (prepare P f n Q).sources (prepare P f n Q).targets).2 := by
  simp only [solve]

theorem solve_work (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n Q : Nat) :
    (solve P f n Q).work=(prepare P f n Q).work+
      (Join.run P.C (prepare P f n Q).modulus 0 (prepare P f n Q).text
        (prepare P f n Q).sources (prepare P f n Q).targets).2+
      joinLedger ⟨(CountedShortBranch.solve P f n Q).toResult,
        (CountedShortBranch.solve P f n Q).sortSteps⟩+5 := by
  rw [BranchResult.work,solve_preparationWork,solve_constructionWork,solve_join]

theorem solve_joinLedger (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n Q : Nat) :
    joinLedger (solve P f n Q).joined≤
      PeriodicAccounting.shortWork (CountedShortBranch.solve P f n Q) := by
  rw [solve_join]
  unfold joinLedger PeriodicAccounting.shortWork
  omega

end Short

namespace Cubic

def solve (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n Q : Nat) : Result Bool :=
  let long := Long.solve P f n Q
  let short := Short.solve P f n Q
  (long.answer || short.answer,long.work+short.work+3)

theorem solve_value (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n Q : Nat) :
    (solve P f n Q).1=(CountedP1Cubic.solve P f n Q).answer := by
  simp only [solve,Long.solve_value,Short.solve_value,CountedP1Cubic.solve,CountedP1Cubic.Result.answer]

theorem solve_work (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n Q : Nat) :
    (solve P f n Q).2=(Long.solve P f n Q).work+(Short.solve P f n Q).work+3 := rfl

end Cubic
end REWB.PeriodicActual
