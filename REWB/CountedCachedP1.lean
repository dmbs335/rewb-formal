import REWB.CachedP1
import REWB.CountedProjection

/-! Measured five-variable projection of actual cached P1 target events.
    Source events already have just one free length variable and require
    no existential projection. Equality-cache reads and projection
    structural operations are distinct counters. As for CountedCachedP2,
    cached descriptor construction and initial DNF assembly are separate. -/
namespace REWB.CountedCachedP1
open REWB.AffineProjection REWB.UniformProjection REWB.UniformPhaseBounds
variable {α : Type}

structure Result where
  formula : Formula
  equalityReads : Nat
  projectionSteps : Nat
  deriving Repr

def source (P : SevenDFA α) (n q a phase rho : Nat) (I : FullyCachedP2.Shared P) : Result :=
  ⟨CachedP1.source P n q a phase rho I,0,0⟩

theorem source_value (P : SevenDFA α) (n q a phase rho : Nat) (I : FullyCachedP2.Shared P) :
    (source P n q a phase rho I).formula=CachedP1.source P n q a phase rho I := rfl

def project (P : SevenDFA α) (n q p rho : Nat) (I : FullyCachedP2.Shared P)
    (ph : P1Target.Layout Nat) : Result :=
  let f := CachedP1.countedTargetFormula P n q p rho I ph
  let r := CountedProjection.project 5 f.1
  ⟨r.1,f.2,r.2⟩

theorem project_value (P : SevenDFA α) (n q p rho : Nat) (I : FullyCachedP2.Shared P)
    (ph : P1Target.Layout Nat) :
    (project P n q p rho I ph).formula=CachedP1.projection P n q p rho I ph := by
  simp only [project,CountedProjection.project_value,CachedP1.countedTargetFormula_correct,CachedP1.projection]

theorem project_equalityReads (P : SevenDFA α) (n q p rho : Nat) (I : FullyCachedP2.Shared P)
    (ph : P1Target.Layout Nat) : (project P n q p rho I ph).equalityReads≤3 :=
  CachedP1.countedTargetFormula_cost P n q p rho I ph

theorem project_le_solve (k : Nat) (F : Formula) :
    (CountedProjection.project k F).2≤(CountedProjection.solve k F []).2 := by
  change (CountedProjection.project k F).2≤(CountedProjection.project k F).2+
    (CountedProjection.decide [] (CountedProjection.project k F).1).2+1
  omega

theorem project_uniform_steps (k : Nat) (F : Formula) (fs : Family) (h : Covered F fs) :
    (CountedProjection.project k F).2≤CountedProjection.stepsBudget k 0 fs :=
  Nat.le_trans (project_le_solve k F) (CountedProjection.solve_uniform_steps k F fs [] h)

def targetSteps (P : SevenDFA α) : Nat := CountedProjection.stepsBudget 5 0 (p1TargetFamily P)

theorem project_steps_of_covered (P : SevenDFA α) (n q p rho : Nat)
    (I : FullyCachedP2.Shared P) (ph : P1Target.Layout Nat)
    (h : Covered (CachedP1.targetFormula P n q p rho I ph) (p1TargetFamily P)) :
    (project P n q p rho I ph).projectionSteps≤targetSteps P := by
  change (CountedProjection.project 5 (CachedP1.countedTargetFormula P n q p rho I ph).1).2≤_
  rw [CachedP1.countedTargetFormula_correct]
  exact project_uniform_steps _ _ _ h

theorem project_steps [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (n q p rho : Nat) (pre post : Word α) (ph : P1Target.Layout Nat) :
    (project P n q p rho (FullyCachedP2.prepare P s q pre post) ph).projectionSteps≤targetSteps P := by
  apply project_steps_of_covered
  rw [CachedP1.targetFormula_eq]
  exact p1_target_covered P s n q p rho post ph

theorem project_steps_at [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (n q p rho : Nat) (w : Word α) (lo hi : Nat) (hlo : lo≤w.length) (hhi : hi≤w.length)
    (ph : P1Target.Layout Nat) :
    (project P n q p rho (BoundaryContexts.prepareAt P s q (BoundaryContexts.build P w).1 lo hi)
      ph).projectionSteps≤targetSteps P := by
  rw [BoundaryContexts.prepareAt_correct P s q w lo hi hlo hhi]
  exact project_steps P s n q p rho (w.take lo) (w.drop hi) ph

theorem project_eq_at [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (n q p rho : Nat) (w : Word α) (lo hi : Nat) (hlo : lo≤w.length) (hhi : hi≤w.length)
    (ph : P1Target.Layout Nat) :
    (project P n q p rho (BoundaryContexts.prepareAt P s q (BoundaryContexts.build P w).1 lo hi)
      ph).formula=P1Target.projection P s n q p rho (w.drop hi) ph := by
  rw [project_value,CachedP1.projectionAt_eq P s n q p rho w lo hi hlo hhi ph]

theorem source_bound_at [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (n q a phase rho : Nat) (w : Word α) (lo hi : Nat) (hlo : lo≤w.length) (hhi : hi≤w.length) :
    measure (source P n q a phase rho
      (BoundaryContexts.prepareAt P s q (BoundaryContexts.build P w).1 lo hi)).formula≤p1SourceBudget P := by
  rw [source_value,CachedP1.sourceAt_eq P s n q a phase rho w lo hi hlo hhi]
  exact projection_budget 0 _ _ (UniformJoin.localSource_covered P s n q a phase rho (w.take lo))

theorem project_bound_at [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (n q p rho : Nat) (w : Word α) (lo hi : Nat) (hlo : lo≤w.length) (hhi : hi≤w.length)
    (ph : P1Target.Layout Nat) :
    measure (project P n q p rho
      (BoundaryContexts.prepareAt P s q (BoundaryContexts.build P w).1 lo hi) ph).formula≤p1TargetBudget P := by
  rw [project_eq_at P s n q p rho w lo hi hlo hhi ph]
  exact p1_target_bound P s n q p rho (w.drop hi) ph

end REWB.CountedCachedP1
