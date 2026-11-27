import REWB.ActualModulusCalls
import REWB.PeriodicActualFullCostPrepare

/-! The LCM operand bound is instantiated on the actual installed long
periodic preparation, without a caller-provided compatibility certificate.
The call observations are proof objects; constructing them is not added to
the runtime matcher. Full machine refinement of the enclosing traversal
is a separate obligation. -/
namespace REWB.PeriodicActual.FullCost.ModulusCalls
open REWB.ActualModulus
variable {σ : Nat}

theorem long_good (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n Q : Nat) :
    TimedJoin.Good (UniformPhaseBounds.p1Modulus P) (Long.prepare P f n Q).1.sources ∧
    TimedJoin.Good (UniformPhaseBounds.p1Modulus P) (Long.prepare P f n Q).1.targets := by
  simp only [Long.prepare_value, PeriodicActual.Long.prepare_sources,
    PeriodicActual.Long.prepare_targets]
  exact P1Events.generated_good P f n Q

theorem long_divides (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n Q : Nat) :
    Calls.Divides (UniformPhaseBounds.p1Modulus P)
      (Calls.build (Long.prepare P f n Q).1.sources (Long.prepare P f n Q).1.targets) := by
  have hg := long_good P f n Q
  exact Calls.build_divides _ _ _ (UniformPhaseBounds.p1Modulus_pos P) hg.1 hg.2

theorem long_operands (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n Q : Nat)
    (pair : Calls.Call)
    (hp : pair ∈ (Calls.build (Long.prepare P f n Q).1.sources
      (Long.prepare P f n Q).1.targets).calls) :
    pair.1 ≤ UniformPhaseBounds.p1Modulus P ∧ pair.2 ≤ UniformPhaseBounds.p1Modulus P :=
  Calls.operands_le _ _ (UniformPhaseBounds.p1Modulus_pos P) (long_divides P f n Q) pair hp

theorem long_counter_le_work (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n Q : Nat) :
    (ActualModulus.build (Long.prepare P f n Q).1.sources
      (Long.prepare P f n Q).1.targets).2 ≤ (Long.prepare P f n Q).2 := by
  simp only [Long.prepare]
  omega

theorem long_calls_le_work (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n Q : Nat) :
    (Calls.build (Long.prepare P f n Q).1.sources
      (Long.prepare P f n Q).1.targets).calls.length ≤ (Long.prepare P f n Q).2 := by
  have h := long_counter_le_work P f n Q
  rw [Calls.build_counter] at h
  omega

end REWB.PeriodicActual.FullCost.ModulusCalls
