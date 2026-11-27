import REWB.MachineWordBounds
import REWB.P1Magnitude

/-! Concrete unsigned-magnitude word capacities for the constant terms
of the actual periodic formulas. The word width is an explicit logarithm
of text length plus a fixed-pattern constant. These statements cover the
named formula payloads, not every intermediate value or heap address of
the complete matcher. A signed representation uses one additional bit. -/
namespace REWB.MachineWordBounds
open REWB.AffineProjection REWB.PhaseSolver REWB.Periodic
variable {α : Type}

theorem p2_stage_constant_fits [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (q n : Nat) (pre post : Word α) (ph : P2Periodic.Layout Nat)
    (k : Nat) (hk : k≤8) (C : Conj) (a : Atom)
    (hC : C∈project k (compileSystem q n s
      (P2Periodic.constraints P q n pre post (P2Periodic.endpoints ph)))) (ha : a∈C) :
    ((UniformProjection.payload a).eval []).natAbs<
      2^(width (ProjectionMagnitude.p2AllStagesLinearConstant P) 1 n) := by
  apply value_fits
  simpa only [cap,Nat.pow_one] using
    ProjectionMagnitude.p2_stage_constant_linear P s q n pre post ph k hk C a hC ha

theorem p1_target_stage_constant_fits [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (q n p rho : Nat) (hp : p≤n) (post : Word α) (ph : P1Target.Layout Nat)
    (k : Nat) (hk : k≤5) (C : Conj) (a : Atom)
    (hC : C∈project k (P1Target.formula P s n q p rho post ph)) (ha : a∈C) :
    ((UniformProjection.payload a).eval []).natAbs<
      2^(width (ProjectionMagnitude.p1TargetAllStagesLinearConstant P) 1 n) := by
  apply value_fits
  simpa only [cap,Nat.pow_one] using
    ProjectionMagnitude.p1_target_stage_constant_linear P s q n p rho hp post ph k hk C a hC ha

theorem p1_source_constant_fits (P : SevenDFA α) (s : Nat→α)
    (q n a phase rho : Nat) (ha : a≤n) (pre : Word α) (C : Conj) (atom : Atom)
    (hC : C∈UniformJoin.localSource P s n q a phase rho pre) (hatom : atom∈C) :
    ((UniformProjection.payload atom).eval []).natAbs<
      2^(width (ProjectionMagnitude.p1SourceLinearConstant P) 1 n) := by
  apply value_fits
  simpa only [cap,Nat.pow_one] using
    ProjectionMagnitude.p1_source_constant_linear P s q n a phase rho ha pre C atom hC hatom

end REWB.MachineWordBounds
