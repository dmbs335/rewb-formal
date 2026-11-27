import REWB.BoundaryContexts
import REWB.UniformJoin

/-! P1 source and target formula construction from one prepared run.
    The source excludes the C gap, which the chronological join checks.
    Every periodic transition, short equality, and exterior DFA context
    is materialized before the event loop. Integer projection is still
    the existing exact solver; counters here concern equality-cache reads. -/
namespace REWB.CachedP1
open REWB.Periodic REWB.PhaseSolver REWB.AffineProjection
variable {α : Type}

def source (P : SevenDFA α) (n q a phase rho : Nat) (I : FullyCachedP2.Shared P) : Formula :=
  let l := P1Source.start q a phase
  let r := P2Periodic.endEndpoint q a
  if tailLen q l r=rho then
    both (CachedPhase.regular q n I.a I.ta P2Periodic.zeroEndpoint l)
      (orderFormula q n l r)
  else []

theorem source_eq [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (n q a phase rho : Nat) (pre post : Word α) :
    source P n q a phase rho (FullyCachedP2.prepare P s q pre post)=
      UniformJoin.localSource P s n q a phase rho pre := by
  simp only [source,FullyCachedP2.prepare,ContextCache.prepare_correct,
    CachedPhase.regular_eq,UniformJoin.localSource]

def targetSystem (P : SevenDFA α) (n q p : Nat) (I : FullyCachedP2.Shared P)
    (L : P1Target.Layout Endpoint) : Formula :=
  both (CachedPhase.regular q n P.D I.td (P1Target.fixed q p) L.j)
    (both (CachedPhase.regular q n P.B I.tb L.j L.t)
    (both (CachedPhase.regular q n P.F I.tf L.t L.e)
    (both (CachedPhase.regular q n P.G I.tg L.e L.k)
    (both (CachedPhase.regular q n I.h I.th L.f (P2Periodic.endEndpoint q n))
    (both (PhaseEqualityCache.equalFormula q n I.equality (P1Target.fixed q p) L.e L.k L.f)
      [[]])))))

theorem targetSystem_eq [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (n q p : Nat) (pre post : Word α) (L : P1Target.Layout Endpoint) :
    targetSystem P n q p (FullyCachedP2.prepare P s q pre post) L=
      compileSystem q n s (P1Target.constraints P q n p post L) := by
  simp only [targetSystem,FullyCachedP2.prepare,ContextCache.prepare_correct,
    CachedPhase.regular_eq,PhaseEqualityCache.equalFormula_eq,
    P1Target.constraints,compileSystem,Constraint.compile]

def targetFormula (P : SevenDFA α) (n q p rho : Nat) (I : FullyCachedP2.Shared P)
    (ph : P1Target.Layout Nat) : Formula :=
  let L := P1Target.endpoints ph
  if tailLen q L.j L.t=rho then
    both (targetSystem P n q p I L) (eq (countExpr L.j L.t) (.var 5))
  else []

theorem targetFormula_eq [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (n q p rho : Nat) (pre post : Word α) (ph : P1Target.Layout Nat) :
    targetFormula P n q p rho (FullyCachedP2.prepare P s q pre post) ph=
      P1Target.formula P s n q p rho post ph := by
  simp only [targetFormula,targetSystem_eq,P1Target.formula]

def projection (P : SevenDFA α) (n q p rho : Nat) (I : FullyCachedP2.Shared P)
    (ph : P1Target.Layout Nat) : Formula :=
  project 5 (targetFormula P n q p rho I ph)

theorem projection_eq [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (n q p rho : Nat) (pre post : Word α) (ph : P1Target.Layout Nat) :
    projection P n q p rho (FullyCachedP2.prepare P s q pre post) ph=
      P1Target.projection P s n q p rho post ph := by
  simp only [projection,targetFormula_eq,P1Target.projection]

theorem sourceAt_eq [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (n q a phase rho : Nat) (w : Word α) (lo hi : Nat)
    (hlo : lo≤w.length) (hhi : hi≤w.length) :
    source P n q a phase rho (BoundaryContexts.prepareAt P s q (BoundaryContexts.build P w).1 lo hi)=
      UniformJoin.localSource P s n q a phase rho (w.take lo) := by
  rw [BoundaryContexts.prepareAt_correct P s q w lo hi hlo hhi]
  exact source_eq P s n q a phase rho (w.take lo) (w.drop hi)

theorem targetFormulaAt_eq [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (n q p rho : Nat) (w : Word α) (lo hi : Nat)
    (hlo : lo≤w.length) (hhi : hi≤w.length) (ph : P1Target.Layout Nat) :
    targetFormula P n q p rho
      (BoundaryContexts.prepareAt P s q (BoundaryContexts.build P w).1 lo hi) ph=
      P1Target.formula P s n q p rho (w.drop hi) ph := by
  rw [BoundaryContexts.prepareAt_correct P s q w lo hi hlo hhi]
  exact targetFormula_eq P s n q p rho (w.take lo) (w.drop hi) ph

theorem projectionAt_eq [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (n q p rho : Nat) (w : Word α) (lo hi : Nat)
    (hlo : lo≤w.length) (hhi : hi≤w.length) (ph : P1Target.Layout Nat) :
    projection P n q p rho
      (BoundaryContexts.prepareAt P s q (BoundaryContexts.build P w).1 lo hi) ph=
      P1Target.projection P s n q p rho (w.drop hi) ph := by
  rw [BoundaryContexts.prepareAt_correct P s q w lo hi hlo hhi]
  exact projection_eq P s n q p rho (w.take lo) (w.drop hi) ph

def countedTargetSystem (P : SevenDFA α) (n q p : Nat) (I : FullyCachedP2.Shared P)
    (L : P1Target.Layout Endpoint) : Formula×Nat :=
  let equal := PhaseEqualityCache.countedFormula q n I.equality (P1Target.fixed q p) L.e L.k L.f
  (both (CachedPhase.regular q n P.D I.td (P1Target.fixed q p) L.j)
    (both (CachedPhase.regular q n P.B I.tb L.j L.t)
    (both (CachedPhase.regular q n P.F I.tf L.t L.e)
    (both (CachedPhase.regular q n P.G I.tg L.e L.k)
    (both (CachedPhase.regular q n I.h I.th L.f (P2Periodic.endEndpoint q n))
    (both equal.1 [[]]))))),equal.2)

theorem countedTargetSystem_correct (P : SevenDFA α) (n q p : Nat) (I : FullyCachedP2.Shared P)
    (L : P1Target.Layout Endpoint) :
    (countedTargetSystem P n q p I L).1=targetSystem P n q p I L := by
  simp only [countedTargetSystem,PhaseEqualityCache.countedFormula_correct,targetSystem]

theorem countedTargetSystem_cost (P : SevenDFA α) (n q p : Nat) (I : FullyCachedP2.Shared P)
    (L : P1Target.Layout Endpoint) : (countedTargetSystem P n q p I L).2≤3 :=
  PhaseEqualityCache.countedFormula_cost q n I.equality (P1Target.fixed q p) L.e L.k L.f

def countedTargetFormula (P : SevenDFA α) (n q p rho : Nat) (I : FullyCachedP2.Shared P)
    (ph : P1Target.Layout Nat) : Formula×Nat :=
  let L := P1Target.endpoints ph
  if tailLen q L.j L.t=rho then
    let r := countedTargetSystem P n q p I L
    (both r.1 (eq (countExpr L.j L.t) (.var 5)),r.2)
  else ([],0)

theorem countedTargetFormula_correct (P : SevenDFA α) (n q p rho : Nat) (I : FullyCachedP2.Shared P)
    (ph : P1Target.Layout Nat) :
    (countedTargetFormula P n q p rho I ph).1=targetFormula P n q p rho I ph := by
  unfold countedTargetFormula targetFormula
  dsimp only
  split
  · simp only [countedTargetSystem_correct]
  · rfl

theorem countedTargetFormula_cost (P : SevenDFA α) (n q p rho : Nat) (I : FullyCachedP2.Shared P)
    (ph : P1Target.Layout Nat) : (countedTargetFormula P n q p rho I ph).2≤3 := by
  unfold countedTargetFormula
  dsimp only
  split
  · exact countedTargetSystem_cost P n q p I (P1Target.endpoints ph)
  · exact Nat.zero_le _

def countedProjection (P : SevenDFA α) (n q p rho : Nat) (I : FullyCachedP2.Shared P)
    (ph : P1Target.Layout Nat) : Formula×Nat :=
  let r := countedTargetFormula P n q p rho I ph
  (project 5 r.1,r.2)

theorem countedProjection_correct (P : SevenDFA α) (n q p rho : Nat) (I : FullyCachedP2.Shared P)
    (ph : P1Target.Layout Nat) :
    (countedProjection P n q p rho I ph).1=projection P n q p rho I ph := by
  simp only [countedProjection,countedTargetFormula_correct,projection]

theorem countedProjection_cost (P : SevenDFA α) (n q p rho : Nat) (I : FullyCachedP2.Shared P)
    (ph : P1Target.Layout Nat) : (countedProjection P n q p rho I ph).2≤3 :=
  countedTargetFormula_cost P n q p rho I ph

end REWB.CachedP1
