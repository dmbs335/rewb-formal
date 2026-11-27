import REWB.PeriodicConstructionMaskedOrbit

/-! Full local construction of a masked periodic branch. The executable
path constructs all three finite orbits, the DNF, its projection, and
the clipped residue windows before calling the immutable AP index.
Only cached pattern K and materialized transition maps are inputs.
The extra work is bounded by a concrete pattern-only constant. -/
namespace REWB.PeriodicConstruction.Masked
open REWB.PeriodicConstruction REWB.MaskedPeriodic REWB.MaskedFiniteAction.Maps
open REWB.AffineProjection
variable {α : Type} {b c e : Nat}

structure InputData (b c e : Nat) where
  capture : Input b
  gap : Input c
  suffix : Input e

def InputData.data (d : InputData b c e) : MaskedPeriodic.Data b c e :=
  ⟨d.capture.data,d.gap.data,d.suffix.data⟩

def upper (branch : Branch) (N : Nat) : Result AffineProjection.Formula :=
  match branch with
  | .zero => Formula.charge (Formula.le (.add kExpr aExpr) (.lit N)) 9
  | .interior => Formula.charge (Formula.le (.add (.add kExpr aExpr) (.lit 1)) (.lit N)) 9
  | .ending => Formula.charge (Formula.eq (.add kExpr aExpr) (.lit N)) 9

def upperBudget : Formula.Budget := ⟨1,2,64⟩

theorem upper_value (branch : Branch) (N : Nat) :
    (upper branch N).1=MaskedPeriodic.upperFormula branch N := by
  cases branch <;> simp only [upper,Formula.charge,Formula.le,
    Formula.eq_value,MaskedPeriodic.upperFormula]

theorem upper_covers (branch : Branch) (N : Nat) :
    Formula.Covers (upper branch N) upperBudget := by
  cases branch <;>
    simp [upper,upperBudget,Formula.Covers,Formula.Shape,Formula.charge,Formula.le,
      Formula.eq,Formula.join,Formula.both,CountedProjection.flatMap,
      CountedProjection.map,CountedProjection.append,PhaseSolver.le,PhaseSolver.unit]

def bounds (branch : Branch) (N : Nat) : Result AffineProjection.Formula :=
  Formula.charge (Formula.join (Formula.le (.lit 2) aExpr)
    (Formula.join (Formula.le (.add aExpr (.lit branch.carry)) kExpr) (upper branch N))) 16

def boundsBudget : Formula.Budget :=
  (Formula.leBudget.join (Formula.leBudget.join upperBudget)).charge 16

theorem bounds_value (branch : Branch) (N : Nat) :
    (bounds branch N).1=MaskedPeriodic.boundsFormula branch N := by
  simp only [bounds,Formula.charge,Formula.join_value,Formula.le,upper_value,
    MaskedPeriodic.boundsFormula]

theorem bounds_covers (branch : Branch) (N : Nat) :
    Formula.Covers (bounds branch N) boundsBudget :=
  Formula.charge_covers _ _ _ (Formula.join_covers _ _ _ _ (Formula.le_covers _ _)
    (Formula.join_covers _ _ _ _ (Formula.le_covers _ _) (upper_covers _ _)))

def formula (d : InputData b c e) (branch : Branch) (N : Nat) : Result AffineProjection.Formula :=
  Formula.charge (Formula.join (bounds branch N)
    (Formula.join (orbitFormula d.capture aExpr)
      (Formula.join (orbitFormula d.gap (gapExpr branch))
        (orbitFormula d.suffix (tailExpr branch N))))) 20

def formulaBudget (b c e : Nat) : Formula.Budget :=
  (boundsBudget.join ((orbitBudget b).join ((orbitBudget c).join (orbitBudget e)))).charge 20

theorem formula_value (d : InputData b c e) (branch : Branch) (N : Nat) :
    (formula d branch N).1=MaskedPeriodic.formula d.data branch N := by
  simp only [formula,Formula.charge,Formula.join_value,bounds_value,orbitFormula_value,
    MaskedPeriodic.formula,InputData.data]

theorem formula_covers (d : InputData b c e) (branch : Branch) (N : Nat) :
    Formula.Covers (formula d branch N) (formulaBudget b c e) :=
  Formula.charge_covers _ _ _ (Formula.join_covers _ _ _ _ (bounds_covers _ _)
    (Formula.join_covers _ _ _ _ (orbitFormula_covers _ _)
      (Formula.join_covers _ _ _ _ (orbitFormula_covers _ _) (orbitFormula_covers _ _))))

def projection (d : InputData b c e) (branch : Branch) (N : Nat) : Result AffineProjection.Formula :=
  let F:=formula d branch N
  let out:=CountedProjection.project 1 F.1
  (out.1,F.2+out.2+1)

theorem projection_value (d : InputData b c e) (branch : Branch) (N : Nat) :
    (projection d branch N).1=(MaskedPeriodic.projection d.data branch N).1 := by
  simp only [projection,formula_value,MaskedPeriodic.projection]

theorem projection_work (d : InputData b c e) (branch : Branch) (N : Nat) :
    (projection d branch N).2≤(formulaBudget b c e).work+projectionBudget b c e+1 := by
  have hf:=(formula_covers d branch N).2
  have hp:=MaskedPeriodic.projection_steps d.data branch N
  unfold projection
  dsimp only
  rw [formula_value]
  change _+_+1≤_
  exact Nat.add_le_add_right (Nat.add_le_add hf hp) 1

def windows (d : InputData b c e) (branch : Branch) (N K : Nat) :
    Result (List (Nat×ExponentIntervals.Window)) :=
  let F:=projection d branch N
  let out:=PeriodicConstruction.allWindows K N F.1
  (out.1,F.2+out.2+1)

def windowsCost (b c e K : Nat) : Nat :=
  (formulaBudget b c e).work+projectionBudget b c e+
    24*K*(syntaxBudget b c e+1)+5

theorem windows_value (d : InputData b c e) (branch : Branch) (N K : Nat) :
    (windows d branch N K).1=ExponentIntervals.allWindows K N
      (MaskedPeriodic.projection d.data branch N).1 := by
  simp only [windows,PeriodicConstruction.allWindows_value,projection_value]

theorem windows_work (d : InputData b c e) (branch : Branch) (N K : Nat) :
    (windows d branch N K).2≤windowsCost b c e K := by
  have hp:=projection_work d branch N
  have hw:=PeriodicConstruction.allWindows_work K N (projection d branch N).1
  have hs:=MaskedPeriodic.projection_size d.data branch N
  rw [projection_value] at hw
  have hm:=Nat.mul_le_mul_left (24*K) (Nat.add_le_add_right hs 1)
  unfold windows windowsCost
  dsimp only
  rw [projection_value]
  omega

def queryBranch (d : InputData b c e) (branch : Branch) (N : Nat)
    (counts : Array Nat) (base q s K : Nat) : Result MaskedProgression.Answer :=
  let ws:=windows d branch N K
  let out:=MaskedPeriodic.queryWindows counts base q K s ws.1
  (out,ws.2+out.slots+out.arithmetic+1)

theorem queryBranch_value (d : InputData b c e) (branch : Branch) (N : Nat)
    (counts : Array Nat) (base q s K : Nat) :
    (queryBranch d branch N counts base q s K).1=
      MaskedPeriodic.queryBranch d.data branch N counts base q s K := by
  simp only [queryBranch,windows_value,MaskedPeriodic.queryBranch]

theorem queryBranch_extra (d : InputData b c e) (branch : Branch) (N : Nat)
    (counts : Array Nat) (base q s K : Nat) :
    (queryBranch d branch N counts base q s K).2≤
      (MaskedPeriodic.queryBranch d.data branch N counts base q s K).slots+
      (MaskedPeriodic.queryBranch d.data branch N counts base q s K).arithmetic+
      windowsCost b c e K+1 := by
  have hw:=windows_work d branch N K
  unfold queryBranch
  dsimp only
  rw [windows_value]
  unfold MaskedPeriodic.queryBranch
  omega

theorem inflate (x c : Nat) : x+c≤(c+1)*(x+1) := by
  simp only [Nat.add_mul,Nat.mul_add,Nat.one_mul,Nat.mul_one]
  omega

theorem queryBranch_inflate (d : InputData b c e) (branch : Branch) (N : Nat)
    (counts : Array Nat) (base q s K : Nat) :
    (queryBranch d branch N counts base q s K).2≤
      (windowsCost b c e K+2)*
      ((MaskedPeriodic.queryBranch d.data branch N counts base q s K).slots+
       (MaskedPeriodic.queryBranch d.data branch N counts base q s K).arithmetic+1) := by
  exact Nat.le_trans (queryBranch_extra d branch N counts base q s K)
    (by simpa only [Nat.add_assoc] using (inflate
      ((MaskedPeriodic.queryBranch d.data branch N counts base q s K).slots+
       (MaskedPeriodic.queryBranch d.data branch N counts base q s K).arithmetic)
      (windowsCost b c e K+1)))

end REWB.PeriodicConstruction.Masked
