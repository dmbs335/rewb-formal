import REWB.ResidualActualMatcher
import REWB.FullMatcher

/-! Kernel regressions for the actual complete dispatcher. Large finite
row universes are not reduced by the kernel: the universal public theorem
connects each concrete input to small independent literal decisions. -/
namespace REWB.ResidualActual.Regression
open REWB.BoundaryRange

def oneLetter (a : Fin 2) : DFA (Fin 2) :=
  ⟨3,0,fun q c=>if q=0 ∧ c=a then 1 else 2,fun q=>q==1⟩

def independentPattern : SevenDFA (Fin 2) :=
  ⟨epsilon,oneLetter 0,epsilon,epsilon,oneLetter 1,epsilon,epsilon⟩

theorem independent_different_captures :
    (Independent.execute independentPattern #[0,0,1,1] 0).answer=true := by
  apply (Independent.execute_correct independentPattern #[0,0,1,1] 0).mpr
  apply (Reference.independent_correct independentPattern [0,0,1,1]).mp
  decide

theorem independent_wrong_order :
    (Independent.execute independentPattern #[1,1,0,0] 0).answer=false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have hs:=(Independent.execute_correct independentPattern #[1,1,0,0] 0).mp h
  have hr:=(Reference.independent_correct independentPattern [1,1,0,0]).mpr hs
  have hn : Reference.independent independentPattern [1,1,0,0]=false := by decide
  simp only [hn,Bool.false_eq_true] at hr

def sameThree : FiveDFA (Fin 2) := ⟨epsilon,oneLetter 0,epsilon,epsilon,epsilon⟩

theorem same_three_copies : (same sameThree #[0,0,0] 0).answer=true := by
  apply (same_correct sameThree #[0,0,0] 0).mpr
  apply (Reference.same_correct sameThree [0,0,0]).mp
  decide

theorem once_empty_capture :
    (once (epsilon : DFA (Fin 2)) epsilon epsilon epsilon #[] 0).answer=true := by
  apply (once_correct epsilon epsilon epsilon epsilon #[] 0).mpr
  apply (CompleteNormalization.once_matches epsilon epsilon epsilon epsilon []).mpr
  exact ⟨[],[],[],[],(epsilon_accepts []).mpr rfl,(epsilon_accepts []).mpr rfl,
    (epsilon_accepts []).mpr rfl,(epsilon_accepts []).mpr rfl,rfl⟩

theorem cached_projection :
    Table.get (project (Table.build fun i : Fin 3=>(i.val+7,2)) (fun _ x=>x+10)) 2=19 := by
  decide

/-- All six actual constructors agree with the earlier executable semantic
baseline. This equality supplies no runtime answers to the new code. -/
theorem form_eq_reference {σ : Nat} (F : CompleteNormalization.Form (Fin σ))
    (text : Array (Fin σ)) (fallback : Fin σ) :
    (Matcher.form F text fallback).answer=FullMatcher.form F text.toList := by
  apply Bool.eq_iff_iff.mpr
  exact (Matcher.form_correct F text fallback).trans (FullMatcher.form_correct F text.toList).symm

theorem source_expression_eq_reference {σ : Nat} (p : Expr (Fin σ))
    (fallback : Fin σ) (w : Word (Fin σ)) :
    Matcher.matchWord p fallback w=FullMatcher.matchWord p w := by
  apply Bool.eq_iff_iff.mpr
  exact (Matcher.matchWord_correct p fallback w).trans (FullMatcher.matchWord_correct p w).symm

end REWB.ResidualActual.Regression
