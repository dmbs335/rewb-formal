import REWB.P1Source
import REWB.CachedPhase

/-! The two source/target count formulas can be joined without scanning
    any repetition counts. The exact phase key and text-order context
    are checked separately. This is a per-pair decision, not the
    amortized source index used by the intended faster matcher. -/
namespace REWB.P1Join
open REWB.AffineProjection
open REWB.PhaseSolver
open REWB.Periodic
open REWB.P2Periodic (factor)
variable {α : Type}

def nonnegative : Formula := le (.lit 0) (.var 0)

def joinFormula (S T : Formula) : Formula := both nonnegative (both S T)

theorem joinFormula_good (S T : Formula) (hs : FormulaGood S) (ht : FormulaGood T) :
    FormulaGood (joinFormula S T) :=
  both_good _ _ (le_good _ _) (both_good _ _ hs ht)

theorem joinFormula_correct (S T : Formula) (x : Int) :
    Satisfies (joinFormula S T) [x] ↔
      0≤x ∧ Satisfies S [x] ∧ Satisfies T [x] := by
  rw [joinFormula,both_correct,both_correct,nonnegative,le_correct]
  rfl

def join (S T : Formula) : Bool := solve 1 (joinFormula S T) []

theorem join_correct (S T : Formula) (hs : FormulaGood S) (ht : FormulaGood T) :
    join S T=true ↔ ∃ m : Nat,
      decideFormula S [(m:Int)]=true ∧ decideFormula T [(m:Int)]=true := by
  rw [join,solve_correct _ _ _ (joinFormula_good S T hs ht)]
  change (∃ x : Int,Satisfies (joinFormula S T) [x]) ↔ _
  constructor
  · rintro ⟨x,hx⟩
    obtain ⟨h0,hS,hT⟩ := (joinFormula_correct S T x).mp hx
    have he : (x.toNat:Int)=x := by rw [Int.ofNat_toNat]; omega
    refine ⟨x.toNat,?_,?_⟩
    · rw [he]
      exact (decideFormula_correct S [x] hs).mpr hS
    · rw [he]
      exact (decideFormula_correct T [x] ht).mpr hT
  · rintro ⟨m,hS,hT⟩
    exact ⟨m,(joinFormula_correct S T m).mpr ⟨Int.ofNat_nonneg _,
      (decideFormula_correct _ _ hs).mp hS,(decideFormula_correct _ _ ht).mp hT⟩⟩

/-- Exact membership join with an independently prepared target projection.
    The key comparison is on actual words; hash collisions are not assumed
    impossible. An indexed implementation can use verified suffix ranks. -/
def decidePair [DecidableEq α] (P : SevenDFA α)
    (source target : Nat→α) (nS nT q a p phase rho : Nat)
    (preS gap postT : Word α) (ph : P1Target.Layout Nat) : Bool :=
  if segment source phase q=segment target ph.j q then
    join (P1Source.formula P source nS q a phase rho preS gap)
      (P1Target.projection P target nT q p rho postT ph)
  else false

theorem decidePair_correct [DecidableEq α] (P : SevenDFA α)
    (source target : Nat→α) (nS nT q a p phase rho : Nat)
    (preS gap postT : Word α) (ph : P1Target.Layout Nat)
    (hS : Period source nS q) (hT : LeastPeriod target nT q) :
    decidePair P source target nS nT q a p phase rho preS gap postT ph=true ↔
      segment source phase q=segment target ph.j q ∧
      ∃ m : Nat,
        decideFormula (P1Source.formula P source nS q a phase rho preS gap) [(m:Int)]=true ∧
        decideFormula (P1Target.projection P target nT q p rho postT ph) [(m:Int)]=true := by
  unfold decidePair
  by_cases hkey : segment source phase q=segment target ph.j q
  · have hgood : FormulaGood (P1Target.projection P target nT q p rho postT ph) := by
      unfold P1Target.projection
      exact project_good 5 _ (P1Target.formula_good P target nT q p rho hT postT ph)
    rw [if_pos hkey,join_correct _ _ (P1Source.formula_good P source nS q a phase rho preS gap hS) hgood]
    simp only [hkey,true_and]
  · simp [hkey]

theorem decidePair_sound [DecidableEq α] (P : SevenDFA α)
    (source target : Nat→α) (nS nT q a p phase rho : Nat)
    (preS gap preT postT : Word α) (ph : P1Target.Layout Nat)
    (hS : Period source nS q) (hT : LeastPeriod target nT q) (hp : p≤nT)
    (htext : preT++factor target 0 p=preS++segment source 0 a++gap)
    (h : decidePair P source target nS nT q a p phase rho preS gap postT ph=true) :
    MatchesWithin P.nested1 (preT++segment target 0 nT++postT) 2 := by
  obtain ⟨hkey,m,hs,ht⟩ := (decidePair_correct P source target nS nT q a p phase rho
    preS gap postT ph hS hT).mp h
  exact P1Source.join_sources P source target nS nT q a p phase rho m preS gap preT postT ph
    hS hT hp htext hkey hs ht

end REWB.P1Join
