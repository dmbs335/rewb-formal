import REWB.ProjectionModulusRAM
import REWB.PeriodicConstructionSystems

/-! Instantiation for the installed cached P1/P2 projection paths.
The finite shape-family coverage is discharged for actual prepared
contexts. Thus all observed projection LCM calls have concrete checked
machine runs and a pattern-only multiplier against the actual ledger.
This covers the arithmetic calls inside projection, not the enclosing
formula construction, traversal, or complete matcher implementation. -/
namespace REWB.ProjectionModulus.Actual
open REWB.AffineProjection REWB.UniformProjection
variable {α : Type}

def p2Cap (P : SevenDFA α) : Nat := Calls.familyCap 8 (UniformPhaseBounds.p2Family P)
def targetCap (P : SevenDFA α) : Nat := Calls.familyCap 5 (UniformPhaseBounds.p1TargetFamily P)

def p2ProjectionCalls (P : SevenDFA α) (n q : Nat) (I : FullyCachedP2.Shared P)
    (ph : P2Periodic.Layout Nat) : List Calls.Call :=
  Calls.search [] 8 (PeriodicConstruction.Formula.p2 P q n I (P2Periodic.endpoints ph)).1

def targetProjectionCalls (P : SevenDFA α) (n q p rho : Nat) (I : FullyCachedP2.Shared P)
    (ph : P1Target.Layout Nat) : List Calls.Call :=
  Calls.project 5 (PeriodicConstruction.Formula.target P n q p rho I ph).1

theorem p2_formula_covered [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (n q : Nat) (pre post : Word α) (ph : P2Periodic.Layout Nat) :
    Covered (PeriodicConstruction.Formula.p2 P q n (FullyCachedP2.prepare P s q pre post)
      (P2Periodic.endpoints ph)).1 (UniformPhaseBounds.p2Family P) := by
  rw [PeriodicConstruction.Formula.p2_value]
  exact CountedCachedP2.formula_covered P s q n pre post ph

theorem target_formula_covered [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (n q p rho : Nat) (pre post : Word α) (ph : P1Target.Layout Nat) :
    Covered (PeriodicConstruction.Formula.target P n q p rho
      (FullyCachedP2.prepare P s q pre post) ph).1 (UniformPhaseBounds.p1TargetFamily P) := by
  rw [PeriodicConstruction.Formula.target_value,CachedP1.targetFormula_eq]
  exact UniformPhaseBounds.p1_target_covered P s n q p rho post ph

theorem p2_instructions_of_covered (P : SevenDFA α) (n q : Nat) (I : FullyCachedP2.Shared P)
    (ph : P2Periodic.Layout Nat)
    (h : Covered (PeriodicConstruction.Formula.p2 P q n I (P2Periodic.endpoints ph)).1
      (UniformPhaseBounds.p2Family P)) :
    RAM.instructions (p2ProjectionCalls P n q I ph)≤
      (5*p2Cap P+6)*(PeriodicConstruction.Formula.solveP2 P n q I ph).2 := by
  have hb := RAM.search_instructions [] 8 _ _ h
  apply Nat.le_trans hb
  apply Nat.mul_le_mul_left
  simp only [PeriodicConstruction.Formula.solveP2]
  omega

theorem target_instructions_of_covered (P : SevenDFA α) (n q p rho : Nat)
    (I : FullyCachedP2.Shared P) (ph : P1Target.Layout Nat)
    (h : Covered (PeriodicConstruction.Formula.target P n q p rho I ph).1
      (UniformPhaseBounds.p1TargetFamily P)) :
    RAM.instructions (targetProjectionCalls P n q p rho I ph)≤
      (5*targetCap P+6)*(PeriodicConstruction.Formula.projectTarget P n q p rho I ph).2 := by
  have hb := RAM.project_instructions 5 _ _ h
  apply Nat.le_trans hb
  apply Nat.mul_le_mul_left
  simp only [PeriodicConstruction.Formula.projectTarget]
  omega

theorem p2_instructions [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (n q : Nat) (pre post : Word α) (ph : P2Periodic.Layout Nat) :
    RAM.instructions (p2ProjectionCalls P n q (FullyCachedP2.prepare P s q pre post) ph)≤
      (5*p2Cap P+6)*(PeriodicConstruction.Formula.solveP2 P n q
        (FullyCachedP2.prepare P s q pre post) ph).2 :=
  p2_instructions_of_covered P n q _ ph (p2_formula_covered P s n q pre post ph)

theorem target_instructions [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (n q p rho : Nat) (pre post : Word α) (ph : P1Target.Layout Nat) :
    RAM.instructions (targetProjectionCalls P n q p rho
      (FullyCachedP2.prepare P s q pre post) ph)≤
      (5*targetCap P+6)*(PeriodicConstruction.Formula.projectTarget P n q p rho
        (FullyCachedP2.prepare P s q pre post) ph).2 :=
  target_instructions_of_covered P n q p rho _ ph (target_formula_covered P s n q p rho pre post ph)

theorem p2_instructions_at [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (n q : Nat) (w : Word α) (lo hi : Nat) (hlo : lo≤w.length) (hhi : hi≤w.length)
    (ph : P2Periodic.Layout Nat) :
    RAM.instructions (p2ProjectionCalls P n q
      (BoundaryContexts.prepareAt P s q (BoundaryContexts.build P w).1 lo hi) ph)≤
      (5*p2Cap P+6)*(PeriodicConstruction.Formula.solveP2 P n q
        (BoundaryContexts.prepareAt P s q (BoundaryContexts.build P w).1 lo hi) ph).2 := by
  rw [BoundaryContexts.prepareAt_correct P s q w lo hi hlo hhi]
  exact p2_instructions P s n q (w.take lo) (w.drop hi) ph

theorem target_instructions_at [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (n q p rho : Nat) (w : Word α) (lo hi : Nat) (hlo : lo≤w.length) (hhi : hi≤w.length)
    (ph : P1Target.Layout Nat) :
    RAM.instructions (targetProjectionCalls P n q p rho
      (BoundaryContexts.prepareAt P s q (BoundaryContexts.build P w).1 lo hi) ph)≤
      (5*targetCap P+6)*(PeriodicConstruction.Formula.projectTarget P n q p rho
        (BoundaryContexts.prepareAt P s q (BoundaryContexts.build P w).1 lo hi) ph).2 := by
  rw [BoundaryContexts.prepareAt_correct P s q w lo hi hlo hhi]
  exact target_instructions P s n q p rho (w.take lo) (w.drop hi) ph

theorem p2_call_certificate [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (n q : Nat) (pre post : Word α) (ph : P2Periodic.Layout Nat) (pair : Calls.Call)
    (hp : pair∈p2ProjectionCalls P n q (FullyCachedP2.prepare P s q pre post) ph) :
    WordRAM.WordExec (2^RAM.wordBits 8 (UniformPhaseBounds.p2Family P))
      WordRAM.Arithmetic.lcmProgram (WordRAM.Arithmetic.lcmSteps pair.1 pair.2)
      (WordRAM.Arithmetic.lcmInput pair.1 pair.2) (WordRAM.Arithmetic.lcmOutput pair.1 pair.2) ∧
    WordRAM.Arithmetic.lcmSteps pair.1 pair.2≤5*p2Cap P+6 ∧
    (WordRAM.Arithmetic.lcmOutput pair.1 pair.2).regs 0=Nat.lcm pair.1 pair.2 ∧
    (WordRAM.Arithmetic.lcmOutput pair.1 pair.2).halted=true :=
  RAM.search_call_certificate [] 8 _ _ (p2_formula_covered P s n q pre post ph) pair hp

theorem target_call_certificate [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (n q p rho : Nat) (pre post : Word α) (ph : P1Target.Layout Nat) (pair : Calls.Call)
    (hp : pair∈targetProjectionCalls P n q p rho (FullyCachedP2.prepare P s q pre post) ph) :
    WordRAM.WordExec (2^RAM.wordBits 5 (UniformPhaseBounds.p1TargetFamily P))
      WordRAM.Arithmetic.lcmProgram (WordRAM.Arithmetic.lcmSteps pair.1 pair.2)
      (WordRAM.Arithmetic.lcmInput pair.1 pair.2) (WordRAM.Arithmetic.lcmOutput pair.1 pair.2) ∧
    WordRAM.Arithmetic.lcmSteps pair.1 pair.2≤5*targetCap P+6 ∧
    (WordRAM.Arithmetic.lcmOutput pair.1 pair.2).regs 0=Nat.lcm pair.1 pair.2 ∧
    (WordRAM.Arithmetic.lcmOutput pair.1 pair.2).halted=true :=
  RAM.project_call_certificate 5 _ _ (target_formula_covered P s n q p rho pre post ph) pair hp

theorem p2_word_bits (P : SevenDFA α) (n : Nat) :
    RAM.wordBits 8 (UniformPhaseBounds.p2Family P)≤
      RAM.wordBits 8 (UniformPhaseBounds.p2Family P)*((n+2).log2+1) :=
  RAM.wordBits_le_log _ _ _

theorem target_word_bits (P : SevenDFA α) (n : Nat) :
    RAM.wordBits 5 (UniformPhaseBounds.p1TargetFamily P)≤
      RAM.wordBits 5 (UniformPhaseBounds.p1TargetFamily P)*((n+2).log2+1) :=
  RAM.wordBits_le_log _ _ _

end REWB.ProjectionModulus.Actual
