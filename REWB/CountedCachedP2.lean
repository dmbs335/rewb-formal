import REWB.CountedProjection
import REWB.BoundaryContexts

/-! The counted projection solver applied to the actual fully cached
    P2 formula. Equality-cache reads and projection structural operations
    remain distinct counters. Descriptor construction and formula assembly
    are not included in projectionSteps. -/
namespace REWB.CountedCachedP2
open REWB.AffineProjection REWB.UniformProjection REWB.UniformPhaseBounds
variable {α : Type}

structure Result where
  accepted : Bool
  equalityReads : Nat
  projectionSteps : Nat
  deriving Repr

def solveAt (P : SevenDFA α) (n q : Nat) (I : FullyCachedP2.Shared P)
    (ph : P2Periodic.Layout Nat) : Result :=
  let f := FullyCachedP2.countedFormula P q n I (P2Periodic.endpoints ph)
  let r := CountedProjection.search [] 8 f.1
  ⟨r.1,f.2,r.2⟩

theorem solveAt_correct (P : SevenDFA α) (n q : Nat) (I : FullyCachedP2.Shared P)
    (ph : P2Periodic.Layout Nat) :
    (solveAt P n q I ph).accepted=FullyCachedP2.solveAt P n q I ph := by
  simp only [solveAt,CountedProjection.search_value,FullyCachedP2.countedFormula_correct,
    FullyCachedP2.solveAt]

theorem solveAt_equalityReads (P : SevenDFA α) (n q : Nat) (I : FullyCachedP2.Shared P)
    (ph : P2Periodic.Layout Nat) : (solveAt P n q I ph).equalityReads≤6 :=
  FullyCachedP2.countedFormula_cost P q n I (P2Periodic.endpoints ph)

theorem formula_covered [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (q n : Nat) (pre post : Word α) (ph : P2Periodic.Layout Nat) :
    Covered (FullyCachedP2.formula P q n (FullyCachedP2.prepare P s q pre post)
      (P2Periodic.endpoints ph)) (p2Family P) := by
  rw [FullyCachedP2.formula_eq]
  exact p2_covered P s q n pre post ph

theorem solveAt_projectionSteps_of_covered (P : SevenDFA α) (n q : Nat)
    (I : FullyCachedP2.Shared P) (ph : P2Periodic.Layout Nat)
    (h : Covered (FullyCachedP2.formula P q n I (P2Periodic.endpoints ph)) (p2Family P)) :
    (solveAt P n q I ph).projectionSteps≤CountedProjection.p2Steps P := by
  change (CountedProjection.search [] 8
    (FullyCachedP2.countedFormula P q n I (P2Periodic.endpoints ph)).1).2≤_
  rw [FullyCachedP2.countedFormula_correct]
  exact CountedProjection.p2_search_steps P _ h

/-- This bound applies to the cached executable, through exact formula
    equality, without recomputing the uncached string descriptors. -/
theorem solveAt_projectionSteps [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (n q : Nat) (pre post : Word α) (ph : P2Periodic.Layout Nat) :
    (solveAt P n q (FullyCachedP2.prepare P s q pre post) ph).projectionSteps≤
      CountedProjection.p2Steps P :=
  solveAt_projectionSteps_of_covered P n q _ ph (formula_covered P s q n pre post ph)

theorem solveAt_projectionSteps_at [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (n q : Nat) (w : Word α) (lo hi : Nat) (hlo : lo≤w.length) (hhi : hi≤w.length)
    (ph : P2Periodic.Layout Nat) :
    (solveAt P n q (BoundaryContexts.prepareAt P s q (BoundaryContexts.build P w).1 lo hi) ph).projectionSteps≤
      CountedProjection.p2Steps P := by
  rw [BoundaryContexts.prepareAt_correct P s q w lo hi hlo hhi]
  exact solveAt_projectionSteps P s n q (w.take lo) (w.drop hi) ph

theorem cached_stage_bits [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (q n : Nat) (pre post : Word α) (ph : P2Periodic.Layout Nat)
    (k : Nat) (hk : k≤8) (C : Conj) (a : Atom)
    (hC : C∈AffineProjection.project k
      (FullyCachedP2.formula P q n (FullyCachedP2.prepare P s q pre post)
        (P2Periodic.endpoints ph))) (ha : a∈C) :
    ProjectionMagnitude.bits ((payload a).eval [])≤
      (ProjectionMagnitude.p2AllStagesLinearConstant P).log2+(n+2).log2+2 := by
  rw [FullyCachedP2.formula_eq] at hC
  exact ProjectionMagnitude.p2_all_stage_bits P s q n pre post ph k hk C a hC ha

theorem cached_project_value [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (q n : Nat) (pre post : Word α) (ph : P2Periodic.Layout Nat) (k : Nat) :
    (CountedProjection.project k
      (FullyCachedP2.formula P q n (FullyCachedP2.prepare P s q pre post)
        (P2Periodic.endpoints ph))).1=
      AffineProjection.project k (PhaseSolver.compileSystem q n s
        (P2Periodic.constraints P q n pre post (P2Periodic.endpoints ph))) := by
  rw [CountedProjection.project_value,FullyCachedP2.formula_eq]

end REWB.CountedCachedP2
