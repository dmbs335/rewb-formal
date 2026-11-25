import REWB.MaskedClusterPoint
import REWB.MaskedClusterCertificate

/-! Small kernel regressions for a nonperiodic singleton and concrete
    fixed-state moduli. The separate runtime audit checks all matrix
    cells against literal Stage.direct scans, including noninjective
    automata and distinct immutable source/target masks.
-/
namespace REWB.MaskedCluster.Regression

def seen : DFA Bool := ⟨2,0,fun q letter=>if letter then 1 else q,fun q=>decide (q=1)⟩
def last : DFA Bool := ⟨2,0,fun _ letter=>if letter then 1 else 0,fun q=>decide (q=1)⟩
def seen1 : Fin seen.stateCount := ⟨1,by decide⟩
def last1 : Fin last.stateCount := ⟨1,by decide⟩

theorem fixed_moduli : common 1=1 ∧ common 2=2 ∧ common 3=6 ∧ common 4=12 := by decide

def singletonWord : Word Bool := [false,true,false,false,true]
def singletonMask : Array Bool := #[false,true,false,false,false]

theorem genuine_singleton :
    (pointCell seen last
      (pointContexts seen last (BoundaryApplication.Range.build seen singletonWord)
        (BoundaryApplication.Range.build last singletonWord) 0 1 3 5).maps
      (replay seen last (BoundaryApplication.Range.build seen singletonWord)
        (BoundaryApplication.Range.build last singletonWord) 1 1 3).maps
      singletonMask singletonMask 1 .waiting (.gap seen1)).answer=true := by
  apply (pointCell_direct seen last singletonWord 1 0 1 1 3 5 singletonMask singletonMask
    .waiting (.gap seen1) (by decide) (by decide) (by decide) (by decide) (by decide) rfl).mpr
  decide

theorem singleton_target_stage :
    (pointCell seen last
      (pointContexts seen last (BoundaryApplication.Range.build seen singletonWord)
        (BoundaryApplication.Range.build last singletonWord) 0 1 3 5).maps
      (replay seen last (BoundaryApplication.Range.build seen singletonWord)
        (BoundaryApplication.Range.build last singletonWord) 1 1 3).maps
      singletonMask singletonMask 1 (.gap seen1) (.suffix last1)).answer=true := by
  apply (pointCell_direct seen last singletonWord 1 0 1 1 3 5 singletonMask singletonMask
    (.gap seen1) (.suffix last1) (by decide) (by decide) (by decide) (by decide) (by decide) rfl).mpr
  decide

theorem singleton_not_unary :
    ¬RunGeometry.OnPeriod (ArrayText.read singletonWord.toArray false) 1 4 1 := by
  intro h
  have he:=h 1 (by decide) (by decide)
  have hf : true=false := he
  cases hf

end REWB.MaskedCluster.Regression
