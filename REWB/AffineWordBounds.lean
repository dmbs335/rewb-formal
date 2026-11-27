import REWB.PeriodicMachineWordBounds

/-! Bounds for every affine subexpression, including values that later
cancel. These strengthen bounds on the final constant term: each node
evaluated recursively has a bounded magnitude. They are data invariants,
not an assertion that the complete projection evaluator has been lowered
to a RAM program. -/
namespace REWB.AffineWordBounds
open AffineProjection UniformProjection ProjectionMagnitude PhaseSolver UniformPhaseBounds

inductive Subterm : Aff → Aff → Prop
  | root (a : Aff) : Subterm a a
  | left {t a b} : Subterm t a → Subterm t (.add a b)
  | right {t a b} : Subterm t b → Subterm t (.add a b)
  | scaled {t a c} : Subterm t a → Subterm t (.scale c a)

theorem subterm_measure {t a : Aff} (h : Subterm t a) : affMeasure t ≤ affMeasure a := by
  induction h with
  | root => exact Nat.le_refl _
  | left h ih => simp only [affMeasure]; omega
  | right h ih => simp only [affMeasure]; omega
  | @scaled a c h ih =>
    have hm := Nat.mul_le_mul_right (affMeasure a+1) (show 1 ≤ c.natAbs+1 by omega)
    simp only [Nat.one_mul] at hm
    simp only [affMeasure]
    omega

theorem subterm_literals (B : Nat) {t a : Aff} (h : Subterm t a) :
    AffBound B a → AffBound B t := by
  induction h with
  | root => exact id
  | left h ih => exact fun hb => ih hb.1
  | right h ih => exact fun hb => ih hb.2
  | scaled h ih => exact ih

theorem eval_bound (B : Nat) (env : List Int) (a : Aff)
    (he : ∀ i : Nat, (env[i]?.getD (0 : Int)).natAbs ≤ B) (ha : AffBound B a) :
    (a.eval env).natAbs ≤ affMeasure a*B := by
  induction a with
  | lit z => simpa only [Aff.eval,affMeasure,Nat.one_mul] using ha
  | var i =>
    apply Nat.le_trans (he i)
    simpa only [affMeasure,Nat.one_mul] using
      Nat.mul_le_mul_right B (show 1 ≤ i+2 by omega)
  | add a b ihA ihB =>
    have hs := Int.natAbs_add_le (a.eval env) (b.eval env)
    have hb := Nat.add_le_add (ihA ha.1) (ihB ha.2)
    change (a.eval env+b.eval env).natAbs ≤ (affMeasure a+affMeasure b+1)*B
    rw [Nat.add_mul,Nat.one_mul,Nat.add_mul]
    omega
  | scale c a ih =>
    change (c*a.eval env).natAbs ≤ ((c.natAbs+1)*(affMeasure a+1))*B
    rw [Int.natAbs_mul]
    have hh := Nat.mul_le_mul_left c.natAbs (ih ha)
    have hm := Nat.mul_le_mul_right B
      (Nat.mul_le_mul (show c.natAbs ≤ c.natAbs+1 by omega)
        (show affMeasure a ≤ affMeasure a+1 by omega))
    rw [Nat.mul_assoc] at hm
    exact Nat.le_trans hh hm

theorem subterm_eval_bound (B : Nat) (env : List Int) {t a : Aff}
    (hs : Subterm t a) (he : ∀ i : Nat, (env[i]?.getD (0 : Int)).natAbs ≤ B) (ha : AffBound B a) :
    (t.eval env).natAbs ≤ affMeasure a*B :=
  Nat.le_trans (eval_bound B env t he (subterm_literals B hs ha))
    (Nat.mul_le_mul_right B (subterm_measure hs))

theorem formula_subterm_eval_bound (B : Nat) (env : List Int) (F : Formula)
    (he : ∀ i : Nat, (env[i]?.getD (0 : Int)).natAbs ≤ B) (hF : FormulaBound B F)
    (C : Conj) (a : Atom) (t : Aff) (hC : C ∈ F) (ha : a ∈ C)
    (ht : Subterm t (payload a)) : (t.eval env).natAbs ≤ measure F*B := by
  have hm := Nat.le_trans (payload_measure a)
    (Nat.le_trans (member_atom_measure C a ha) (member_conj_measure F C hC))
  exact Nat.le_trans (subterm_eval_bound B env ht he (hF C hC a ha))
    (Nat.mul_le_mul_right B hm)

theorem projected_stage_subterm_bound (k K B : Nat) (F : Formula) (fs : Family)
    (hf : Covered F fs) (hB : FormulaBound B F) (hk : k ≤ K)
    (C : Conj) (a : Atom) (t : Aff) (hC : C ∈ project k F) (ha : a ∈ C)
    (ht : Subterm t (payload a)) :
    (t.eval []).natAbs ≤ stageBudget K fs*max B (familyExtra K fs) := by
  have he : ∀ i : Nat, (([] : List Int)[i]?.getD (0 : Int)).natAbs ≤ max B (familyExtra K fs) := by
    intro i
    simp
  exact Nat.le_trans
    (formula_subterm_eval_bound _ [] _ he (uniform_stage_literals k K B F fs hf hB hk)
      C a t hC ha ht)
    (Nat.mul_le_mul_right _ (projection_stage_budget k K F fs hf hk))

variable {α : Type}

theorem p2_subterm_linear [DecidableEq α] (P : SevenDFA α) (s : Nat → α)
    (q n : Nat) (pre post : Word α) (ph : P2Periodic.Layout Nat)
    (k : Nat) (hk : k ≤ 8) (C : Conj) (a : Atom) (t : Aff)
    (hC : C ∈ project k (compileSystem q n s
      (P2Periodic.constraints P q n pre post (P2Periodic.endpoints ph)))) (ha : a ∈ C)
    (ht : Subterm t (payload a)) :
    (t.eval []).natAbs ≤ p2AllStagesLinearConstant P*(n+2) := by
  have hh := projected_stage_subterm_bound k 8 (inputCap P n) _ _
    (p2_covered P s q n pre post ph) (p2_input_bound P s q n pre post ph) hk C a t hC ha ht
  have hc := Nat.mul_le_mul_left (p2AllStagesBudget P) (cap_linear n (states P) (p2LiteralExtra P))
  change (t.eval []).natAbs ≤ p2AllStagesBudget P*max (inputCap P n) (p2LiteralExtra P) at hh
  change p2AllStagesBudget P*max (inputCap P n) (p2LiteralExtra P) ≤
    p2AllStagesBudget P*((states P+p2LiteralExtra P+1)*(n+2)) at hc
  simpa only [p2AllStagesLinearConstant,Nat.mul_assoc] using Nat.le_trans hh hc

theorem p1_target_subterm_linear [DecidableEq α] (P : SevenDFA α) (s : Nat → α)
    (q n p rho : Nat) (hp : p ≤ n) (post : Word α) (ph : P1Target.Layout Nat)
    (k : Nat) (hk : k ≤ 5) (C : Conj) (a : Atom) (t : Aff)
    (hC : C ∈ project k (P1Target.formula P s n q p rho post ph)) (ha : a ∈ C)
    (ht : Subterm t (payload a)) :
    (t.eval []).natAbs ≤ p1TargetAllStagesLinearConstant P*(n+2) := by
  have hh := projected_stage_subterm_bound k 5 (inputCap P n) _ _
    (p1_target_covered P s n q p rho post ph)
    (p1_target_input_bound P s q n p rho hp post ph) hk C a t hC ha ht
  have hc := Nat.mul_le_mul_left (p1TargetAllStagesBudget P)
    (cap_linear n (states P) (p1TargetLiteralExtra P))
  change (t.eval []).natAbs ≤ p1TargetAllStagesBudget P*
    max (inputCap P n) (p1TargetLiteralExtra P) at hh
  change p1TargetAllStagesBudget P*max (inputCap P n) (p1TargetLiteralExtra P) ≤
    p1TargetAllStagesBudget P*((states P+p1TargetLiteralExtra P+1)*(n+2)) at hc
  simpa only [p1TargetAllStagesLinearConstant,Nat.mul_assoc] using Nat.le_trans hh hc

theorem p2_subterm_fits [DecidableEq α] (P : SevenDFA α) (s : Nat → α)
    (q n : Nat) (pre post : Word α) (ph : P2Periodic.Layout Nat)
    (k : Nat) (hk : k ≤ 8) (C : Conj) (a : Atom) (t : Aff)
    (hC : C ∈ project k (compileSystem q n s
      (P2Periodic.constraints P q n pre post (P2Periodic.endpoints ph)))) (ha : a ∈ C)
    (ht : Subterm t (payload a)) :
    (t.eval []).natAbs < 2^MachineWordBounds.width (p2AllStagesLinearConstant P) 1 n := by
  apply MachineWordBounds.value_fits
  simpa only [MachineWordBounds.cap,Nat.pow_one] using
    p2_subterm_linear P s q n pre post ph k hk C a t hC ha ht

theorem p1_target_subterm_fits [DecidableEq α] (P : SevenDFA α) (s : Nat → α)
    (q n p rho : Nat) (hp : p ≤ n) (post : Word α) (ph : P1Target.Layout Nat)
    (k : Nat) (hk : k ≤ 5) (C : Conj) (a : Atom) (t : Aff)
    (hC : C ∈ project k (P1Target.formula P s n q p rho post ph)) (ha : a ∈ C)
    (ht : Subterm t (payload a)) :
    (t.eval []).natAbs < 2^MachineWordBounds.width (p1TargetAllStagesLinearConstant P) 1 n := by
  apply MachineWordBounds.value_fits
  simpa only [MachineWordBounds.cap,Nat.pow_one] using
    p1_target_subterm_linear P s q n p rho hp post ph k hk C a t hC ha ht

end REWB.AffineWordBounds
