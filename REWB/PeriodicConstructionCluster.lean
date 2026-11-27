import REWB.PeriodicConstructionMaskedBranch

/-! Counted cluster formula and residue-window construction. Both orbit
inputs are materialized. All dimensions depend only on fixed automata;
physical starts, periods and source windows contribute only scalar
literals or coefficients and never drive a construction loop. -/
namespace REWB.PeriodicConstruction.Cluster
open REWB.PeriodicConstruction REWB.AffineProjection
variable {m n : Nat}

def bounds (lo hi : Nat) : Result AffineProjection.Formula :=
  Formula.charge (Formula.join (Formula.le (.lit lo) (.var 0))
    (Formula.le (.var 0) (.lit hi))) 5

def boundsBudget : Formula.Budget := Formula.eqBudget.charge 5

theorem bounds_value (lo hi : Nat) : (bounds lo hi).1=MaskedCluster.bounds lo hi := by
  simp only [bounds,Formula.charge,Formula.join_value,Formula.le,MaskedCluster.bounds]

theorem bounds_covers (lo hi : Nat) : Formula.Covers (bounds lo hi) boundsBudget :=
  Formula.charge_covers _ _ _ (Formula.join_covers _ _ _ _
    (Formula.le_covers _ _) (Formula.le_covers _ _))

def pairFormula (before : Masked.Input m) (after : Masked.Input n) (lo hi : Nat) :
    Result AffineProjection.Formula :=
  Formula.charge (Formula.join (bounds lo hi)
    (Formula.join (Masked.orbitFormula before (MaskedCluster.leftExpr lo))
      (Masked.orbitFormula after (MaskedCluster.rightExpr hi)))) 12

def pairBudget (m n : Nat) : Formula.Budget :=
  (boundsBudget.join ((Masked.orbitBudget m).join (Masked.orbitBudget n))).charge 12

theorem pairFormula_value (before : Masked.Input m) (after : Masked.Input n) (lo hi : Nat) :
    (pairFormula before after lo hi).1=MaskedCluster.pairFormula before.data after.data lo hi := by
  simp only [pairFormula,Formula.charge,Formula.join_value,bounds_value,
    Masked.orbitFormula_value,MaskedCluster.pairFormula]

theorem pairFormula_covers (before : Masked.Input m) (after : Masked.Input n) (lo hi : Nat) :
    Formula.Covers (pairFormula before after lo hi) (pairBudget m n) :=
  Formula.charge_covers _ _ _ (Formula.join_covers _ _ _ _ (bounds_covers _ _)
    (Formula.join_covers _ _ _ _ (Masked.orbitFormula_covers _ _) (Masked.orbitFormula_covers _ _)))

theorem bounds_atoms (lo hi : Nat) : Syntax.Atoms (MaskedCluster.bounds lo hi) 9 := by
  apply Syntax.atoms_both
  · exact Syntax.atoms_mono _ _ _ (Syntax.atoms_le _ _) (by simp [Syntax.aff])
  · exact Syntax.atoms_mono _ _ _ (Syntax.atoms_le _ _) (by simp [Syntax.aff])

theorem pairFormula_atoms (before : Masked.Input m) (after : Masked.Input n) (lo hi : Nat) :
    Syntax.Atoms (pairFormula before after lo hi).1 9 := by
  rw [pairFormula_value]
  apply Syntax.atoms_both _ _ _ (bounds_atoms _ _)
  apply Syntax.atoms_both
  · simpa only [MaskedCluster.leftExpr,Aff.sub,Syntax.aff] using
      Syntax.atoms_descriptor before.data.descriptor (MaskedCluster.leftExpr lo)
  · simpa only [MaskedCluster.rightExpr,Aff.sub,Syntax.aff] using
      Syntax.atoms_descriptor after.data.descriptor (MaskedCluster.rightExpr hi)

theorem pairFormula_syntax (before : Masked.Input m) (after : Masked.Input n) (lo hi : Nat) :
    Syntax.formula (pairFormula before after lo hi).1≤61*(m*n) := by
  have h:=Syntax.formula_bound (pairFormula before after lo hi).1
    (pairBudget m n).branches (pairBudget m n).atoms 9
    (pairFormula_covers before after lo hi).1 (pairFormula_atoms before after lo hi)
  simpa only [pairBudget,boundsBudget,Formula.eqBudget,Formula.Budget.charge,
    Formula.Budget.join,Formula.leBudget,Masked.orbitBudget,Formula.descriptorBudget,
    Nat.one_mul,Nat.reduceAdd,Nat.reduceMul,Nat.mul_comm _ 61] using h

def sourceBounds (window : MaskedCluster.SourceWindow) (s q : Nat) : Result AffineProjection.Formula :=
  let p:=MaskedCluster.positionExpr s q
  Formula.charge (Formula.join (Formula.le (.lit window.lo) p)
    (Formula.le p (.lit ((window.hi:Int)-1)))) 9

def sourceBoundsBudget : Formula.Budget := Formula.eqBudget.charge 9

theorem sourceBounds_value (window : MaskedCluster.SourceWindow) (s q : Nat) :
    (sourceBounds window s q).1=MaskedCluster.sourceBounds window s q := by
  simp only [sourceBounds,Formula.charge,Formula.join_value,Formula.le,MaskedCluster.sourceBounds]

theorem sourceBounds_covers (window : MaskedCluster.SourceWindow) (s q : Nat) :
    Formula.Covers (sourceBounds window s q) sourceBoundsBudget :=
  Formula.charge_covers _ _ _ (Formula.join_covers _ _ _ _
    (Formula.le_covers _ _) (Formula.le_covers _ _))

theorem sourceBounds_atoms (window : MaskedCluster.SourceWindow) (s q : Nat) :
    Syntax.Atoms (MaskedCluster.sourceBounds window s q) 9 := by
  apply Syntax.atoms_both
  · simpa only [MaskedCluster.positionExpr,Syntax.aff] using
      Syntax.atoms_le (.lit window.lo) (MaskedCluster.positionExpr s q)
  · simpa only [MaskedCluster.positionExpr,Syntax.aff] using
      Syntax.atoms_le (MaskedCluster.positionExpr s q) (.lit ((window.hi:Int)-1))

def sourceFormula (before : Masked.Input m) (after : Masked.Input n) (lo hi s q : Nat)
    (window : MaskedCluster.SourceWindow) : Result AffineProjection.Formula :=
  Formula.charge (Formula.join (pairFormula before after lo hi) (sourceBounds window s q)) 10

def sourceBudget (m n : Nat) : Formula.Budget :=
  ((pairBudget m n).join sourceBoundsBudget).charge 10

theorem sourceFormula_value (before : Masked.Input m) (after : Masked.Input n) (lo hi s q : Nat)
    (window : MaskedCluster.SourceWindow) :
    (sourceFormula before after lo hi s q window).1=
      MaskedCluster.sourceFormula before.data after.data lo hi s q window := by
  simp only [sourceFormula,Formula.charge,Formula.join_value,pairFormula_value,sourceBounds_value,
    MaskedCluster.sourceFormula]

theorem sourceFormula_covers (before : Masked.Input m) (after : Masked.Input n) (lo hi s q : Nat)
    (window : MaskedCluster.SourceWindow) :
    Formula.Covers (sourceFormula before after lo hi s q window) (sourceBudget m n) :=
  Formula.charge_covers _ _ _ (Formula.join_covers _ _ _ _
    (pairFormula_covers _ _ _ _) (sourceBounds_covers _ _ _))

theorem sourceFormula_atoms (before : Masked.Input m) (after : Masked.Input n) (lo hi s q : Nat)
    (window : MaskedCluster.SourceWindow) :
    Syntax.Atoms (sourceFormula before after lo hi s q window).1 9 := by
  simp only [sourceFormula,Formula.charge,Formula.join_value]
  exact Syntax.atoms_both _ _ _ (pairFormula_atoms _ _ _ _)
    (by rw [sourceBounds_value]; exact sourceBounds_atoms _ _ _)

theorem sourceFormula_syntax (before : Masked.Input m) (after : Masked.Input n) (lo hi s q : Nat)
    (window : MaskedCluster.SourceWindow) :
    Syntax.formula (sourceFormula before after lo hi s q window).1≤81*(m*n) := by
  have h:=Syntax.formula_bound (sourceFormula before after lo hi s q window).1
    (sourceBudget m n).branches (sourceBudget m n).atoms 9
    (sourceFormula_covers before after lo hi s q window).1 (sourceFormula_atoms before after lo hi s q window)
  simpa only [sourceBudget,sourceBoundsBudget,pairBudget,boundsBudget,Formula.eqBudget,
    Formula.Budget.charge,Formula.Budget.join,Formula.leBudget,Masked.orbitBudget,
    Formula.descriptorBudget,Nat.one_mul,Nat.mul_one,Nat.reduceAdd,Nat.reduceMul,Nat.mul_comm _ 81] using h

def pairWindows (before : Masked.Input m) (after : Masked.Input n) (lo hi K : Nat) :
    Result (List (Nat×ExponentIntervals.Window)) :=
  let F:=pairFormula before after lo hi
  let out:=PeriodicConstruction.allWindows K hi F.1
  (out.1,F.2+out.2+1)

def pairCost (m n K : Nat) : Nat := (pairBudget m n).work+24*K*(61*(m*n)+1)+4

theorem pairWindows_value (before : Masked.Input m) (after : Masked.Input n) (lo hi K : Nat) :
    (pairWindows before after lo hi K).1=MaskedCluster.pairWindows before.data after.data lo hi K := by
  simp only [pairWindows,PeriodicConstruction.allWindows_value,pairFormula_value,MaskedCluster.pairWindows]

theorem pairWindows_work (before : Masked.Input m) (after : Masked.Input n) (lo hi K : Nat) :
    (pairWindows before after lo hi K).2≤pairCost m n K := by
  have hf:=(pairFormula_covers before after lo hi).2
  have hw:=Syntax.allWindows_work K hi (pairFormula before after lo hi).1
  have hm:=Nat.mul_le_mul_left (24*K) (Nat.add_le_add_right (pairFormula_syntax before after lo hi) 1)
  unfold pairWindows pairCost
  dsimp only
  omega

def sourceWindows (before : Masked.Input m) (after : Masked.Input n) (lo hi s q K : Nat)
    (window : MaskedCluster.SourceWindow) : Result (List (Nat×ExponentIntervals.Window)) :=
  let F:=sourceFormula before after lo hi s q window
  let out:=PeriodicConstruction.allWindows K hi F.1
  (out.1,F.2+out.2+1)

def sourceCost (m n K : Nat) : Nat := (sourceBudget m n).work+24*K*(81*(m*n)+1)+4

theorem sourceWindows_value (before : Masked.Input m) (after : Masked.Input n) (lo hi s q K : Nat)
    (window : MaskedCluster.SourceWindow) :
    (sourceWindows before after lo hi s q K window).1=ExponentIntervals.allWindows K hi
      (MaskedCluster.sourceFormula before.data after.data lo hi s q window) := by
  simp only [sourceWindows,PeriodicConstruction.allWindows_value,sourceFormula_value]

theorem sourceWindows_work (before : Masked.Input m) (after : Masked.Input n) (lo hi s q K : Nat)
    (window : MaskedCluster.SourceWindow) :
    (sourceWindows before after lo hi s q K window).2≤sourceCost m n K := by
  have hf:=(sourceFormula_covers before after lo hi s q window).2
  have hw:=Syntax.allWindows_work K hi (sourceFormula before after lo hi s q window).1
  have hm:=Nat.mul_le_mul_left (24*K) (Nat.add_le_add_right (sourceFormula_syntax before after lo hi s q window) 1)
  unfold sourceWindows sourceCost
  dsimp only
  omega

end REWB.PeriodicConstruction.Cluster
