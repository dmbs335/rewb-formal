import REWB.P1Cubic
import REWB.CountedSmallPeriodP1
import REWB.CountedShortBranch
import REWB.ArrayText

/-! Executable cubic-run P1 dispatch, using the measured long-source and
    short-source pipelines. The long path computes its actual formula
    modulus; the short path uses modulus one and exact full-word keys. -/
namespace REWB.CountedP1Cubic
open REWB.Periodic REWB.RunGeometry
variable {σ : Nat}

structure Result where
  long : CountedSmallPeriodP1.Result
  short : CountedShortBranch.Result

def Result.answer (r : Result) : Bool := r.long.answer || r.short.answer
def Result.tests (r : Result) : Nat := r.long.tests+r.short.tests
def Result.eventVisits (r : Result) : Nat := r.long.eventVisits+r.short.eventVisits
def Result.textVisits (r : Result) : Nat := r.long.textVisits+r.short.textVisits
def Result.sortSteps (r : Result) : Nat := r.long.sortSteps+r.short.sortSteps

def solve (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) : Result :=
  ⟨CountedSmallPeriodP1.solve P f n Q,CountedShortBranch.solve P f n Q⟩

theorem solve_answer (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (solve P f n Q).answer=P1Cubic.solve P f n Q := by
  unfold solve Result.answer P1Cubic.solve
  rw [CountedSmallPeriodP1.solve_answer,CountedShortBranch.solve_answer]

theorem solve_sound (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat)
    (h : (solve P f n Q).answer=true) : MatchesWithin P.nested1 (segment f 0 n) 2 := by
  rw [solve_answer] at h
  exact P1Cubic.solve_sound P f n Q h

theorem solve_complete (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat)
    (T : Bounds) (hT : T.Valid f n) (hq : T.period≤Q)
    (hc : 3*T.period≤T.hi-T.lo) (w : P1Cubic.Witness P f n T) :
    (solve P f n Q).answer=true := by
  rw [solve_answer]
  exact P1Cubic.solve_complete P f n Q T hT hq hc w

theorem solve_tests (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (solve P f n Q).tests≤(DyadicIndex.heightFor n+1)*
      (CountedSmallPeriodP1.windowBudget P n Q+CountedShortBranch.eventBudget P n Q) := by
  have h := Nat.add_le_add (CountedSmallPeriodP1.solve_counts P f n Q).1
    (CountedShortBranch.solve_counts P f n Q).1
  simpa only [Nat.mul_add] using h

theorem solve_sortSteps (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (solve P f n Q).sortSteps≤(DyadicIndex.heightFor n+1)*
      (10*CountedSmallPeriodP1.windowBudget P n Q*
        ((CountedSmallPeriodP1.windowBudget P n Q).log2+1)+
       10*CountedShortBranch.eventBudget P n Q*
        ((CountedShortBranch.eventBudget P n Q).log2+1)) := by
  have h := Nat.add_le_add (CountedSmallPeriodP1.solve_sort_steps P f n Q)
    (CountedShortBranch.solve_sortSteps P f n Q)
  simpa only [Nat.mul_add] using h

/-- Materialize an actual finite input once and use safe array reads.
    The fallback is irrelevant to all bounded input factors. -/
def solveWord (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (Q : Nat) : Result :=
  let text := w.toArray
  solve P (ArrayText.read text fallback) text.size Q

theorem solveWord_sound (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (Q : Nat) (h : (solveWord P w fallback Q).answer=true) : MatchesWithin P.nested1 w 2 := by
  unfold solveWord at h
  dsimp only at h
  rw [List.size_toArray] at h
  have hh := solve_sound P (ArrayText.read w.toArray fallback) w.length Q h
  rwa [ArrayText.segment_full] at hh

theorem solveWord_complete (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (Q : Nat) (T : Bounds) (hT : T.Valid (ArrayText.read w.toArray fallback) w.length)
    (hq : T.period≤Q) (hc : 3*T.period≤T.hi-T.lo)
    (wit : P1Cubic.Witness P (ArrayText.read w.toArray fallback) w.length T) :
    (solveWord P w fallback Q).answer=true := by
  unfold solveWord
  dsimp only
  rw [List.size_toArray]
  exact solve_complete P (ArrayText.read w.toArray fallback) w.length Q T hT hq hc wit

end REWB.CountedP1Cubic
