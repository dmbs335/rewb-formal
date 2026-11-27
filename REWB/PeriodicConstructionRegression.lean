import REWB.PeriodicConstructionClusterBank
import REWB.PeriodicConstructionMaskedPhase
import REWB.MaskedPeriodicRegression

/-! Kernel regressions for the measured local compilers: arbitrary
physical coefficients, disabled windows, source deletion and immutable
target retention, and the degenerate guarded phase. -/
namespace REWB.PeriodicConstruction.Regression
open REWB.PeriodicConstruction

def one : DFA Bool := MaskedPeriodic.Regression.universal
def live : MaskedCluster.Mutable.Index := (MaskedMutableProgression.build #[true,false,true] 0 3 1).index
def gone : MaskedCluster.Mutable.Index := (MaskedMutableProgression.erase live 0).index
def orbit : Masked.Input 1 := (Masked.always one).1
def target : Array Nat := (MaskedProgression.build #[true,false,true] 0 3 1).counts

theorem physical_coefficient_shape (s q : Nat) :
    Syntax.aff (MaskedCluster.positionExpr s q)=5 := rfl

theorem disabled_window_no_compilation :
    (Cluster.sourcePairQuery orbit orbit 0 2 live 1 0 1 ⟨false,0,3⟩).2=2 := rfl

set_option maxRecDepth 4096 in
theorem source_erase_target_retained :
    (Cluster.sourcePairQuery orbit orbit 0 0 live 1 0 1 ⟨true,0,3⟩).1.answer=true ∧
    (Cluster.sourcePairQuery orbit orbit 0 0 gone 1 0 1 ⟨true,0,3⟩).1.answer=false ∧
    (Cluster.pairQuery orbit orbit 0 0 target 0 1 0 1).1.answer=true := by
  have hv : live.Valid := MaskedMutableProgression.build_valid _ _ _ _
  have hg : gone.Valid := MaskedMutableProgression.erase_valid live hv 0
  have hp : MaskedCluster.PairAccepts orbit.data orbit.data 0 0 0 := by
    unfold MaskedCluster.PairAccepts
    decide
  have hl : live.Live 0 := by
    unfold live
    rw [MaskedMutableProgression.build_live]
    decide
  have hn : ¬gone.Live 0 := by
    intro h
    exact ((MaskedMutableProgression.erase_live live hv 0 0).mp h).1 rfl
  have h1:=MaskedCluster.Mutable.sourcePairQuery_correct orbit.data orbit.data 0 0 live hv 1 0 1
    ⟨true,0,3⟩ (by decide) (by decide) (by decide) (by decide)
  have h2:=MaskedCluster.Mutable.sourcePairQuery_correct orbit.data orbit.data 0 0 gone hg 1 0 1
    ⟨true,0,3⟩ (by decide) (by decide) (by decide) (by decide)
  rw [Cluster.sourcePairQuery_value,Cluster.sourcePairQuery_value,Cluster.pairQuery_value]
  refine ⟨h1.mpr ⟨0,hp,by decide,by decide,hl,by decide⟩,?_,?_⟩
  · apply Bool.eq_false_iff.mpr
    intro h
    obtain ⟨k,hk,_,_,hlive,_⟩:=h2.mp h
    have hk0 : k=0 := by have hh:=hk.2.1; omega
    subst k
    exact hn hlive
  · apply (MaskedCluster.pairQuery_correct orbit.data orbit.data 0 0 #[true,false,true]
      0 3 1 0 1 (by decide) (by decide) (by decide)).mpr
    exact ⟨0,hp,by unfold MaskedPeriodic.Marked; decide⟩

set_option maxRecDepth 4096 in
theorem empty_source_window :
    (Cluster.sourcePairQuery orbit orbit 0 2 live 1 0 1 ⟨true,1,1⟩).1.answer=false := by decide

theorem scalar_period_same_traversal :
    (PeriodicConstruction.allWindows 1 7 [[.le (MaskedCluster.positionExpr 3 1)]]).2=
      (PeriodicConstruction.allWindows 1 7 [[.le (MaskedCluster.positionExpr 3 1048576)]]).2 := by decide

theorem zero_period_guard (prepared : MaskedPeriodic.PreparedPattern 1 1 1) :
    (Masked.query one one one prepared MaskedPeriodic.Regression.oneIndex
      (MaskedFiniteAction.Maps.identity 1) 0 0 0 #[] 0).1.result.answer=false ∧
    (Masked.query one one one prepared MaskedPeriodic.Regression.oneIndex
      (MaskedFiniteAction.Maps.identity 1) 0 0 0 #[] 0).2=4 := by
  constructor <;> rfl

end REWB.PeriodicConstruction.Regression
