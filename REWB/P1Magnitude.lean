import REWB.PhaseMagnitude
import REWB.CountedCachedP1

/-! Numeric magnitudes for the actual P1 source and target formulas.
    The free source exponent is retained symbolically. All five target
    projection stages have integer constant terms at most a pattern-only
    multiple of the text length, including the cached executable path. -/
namespace REWB.ProjectionMagnitude
open REWB.AffineProjection REWB.UniformProjection REWB.UniformPhaseBounds REWB.PhaseSolver
open REWB.Periodic
variable {α : Type}

theorem p1_target_system_bound [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (q n p : Nat) (hp : p≤n) (post : Word α) (ph : P1Target.Layout Nat) :
    FormulaBound (inputCap P n) (compileSystem q n s
      (P1Target.constraints P q n p post (P1Target.endpoints ph))) := by
  apply system_bound (inputCap P n) q n s _ (by unfold inputCap; omega) (by unfold inputCap; omega)
  intro c hc
  simp only [P1Target.constraints,List.mem_cons,List.mem_nil_iff] at hc
  rcases hc with h|h|h|h|h|h|h
  all_goals first
    | contradiction
    | (subst c
       simp only [ConstraintBound,P1Target.endpoints,P1Target.fixed,
         P2Periodic.endEndpoint,contextual,AffBound,Int.natAbs,true_and,and_true] <;>
       (have hn := Nat.div_le_self n q
        have hp' := Nat.div_le_self p q
        unfold inputCap states
        omega))

theorem p1_target_input_bound [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (q n p rho : Nat) (hp : p≤n) (post : Word α) (ph : P1Target.Layout Nat) :
    FormulaBound (inputCap P n) (P1Target.formula P s n q p rho post ph) := by
  unfold P1Target.formula
  dsimp only
  split
  · apply both_bound
    · exact p1_target_system_bound P s q n p hp post ph
    · exact eq_bound _ _ _
        (count_bound _ _ _ (by unfold inputCap; omega) trivial trivial) trivial
  · exact empty_bound _

theorem p1_start_bound (B q a phase : Nat) (ha : a≤B) (hB : 1≤B) :
    AffBound B (P1Source.start q a phase).1 := by
  change ((a/q≤B) ∧ (carry (.lit 0,phase) (P2Periodic.endEndpoint q a)≤B)) ∧ True
  exact ⟨⟨Nat.le_trans (Nat.div_le_self _ _) ha,
    Nat.le_trans (carry_le_one _ _) hB⟩,trivial⟩

theorem p1_source_input_bound (P : SevenDFA α) (s : Nat→α)
    (q n a phase rho : Nat) (ha : a≤n) (pre : Word α) :
    FormulaBound (inputCap P n) (UniformJoin.localSource P s n q a phase rho pre) := by
  have hN : n≤inputCap P n := by unfold inputCap; omega
  have hB : 1≤inputCap P n := by unfold inputCap; omega
  have hl := p1_start_bound (inputCap P n) q a phase (Nat.le_trans ha hN) hB
  have hr : AffBound (inputCap P n) (P2Periodic.endEndpoint q a).1 := by
    exact lit_nat_bound _ _ (Nat.le_trans (Nat.div_le_self _ _) (Nat.le_trans ha hN))
  unfold UniformJoin.localSource
  split
  · apply both_bound
    · apply regular_bound _ q n s _ _ _ hN hB _ (lit_zero_bound _) hl
      simp only [contextual]
      unfold inputCap states
      omega
    · exact order_bound _ q n _ _ hN hB hl hr
  · exact empty_bound _

def p1TargetLiteralExtra (P : SevenDFA α) : Nat := familyExtra 5 (p1TargetFamily P)

theorem p1_target_stage_literals [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (q n p rho : Nat) (hp : p≤n) (post : Word α) (ph : P1Target.Layout Nat)
    (k : Nat) (hk : k≤5) :
    FormulaBound (max (inputCap P n) (p1TargetLiteralExtra P))
      (AffineProjection.project k (P1Target.formula P s n q p rho post ph)) :=
  uniform_stage_literals k 5 _ _ _ (p1_target_covered P s n q p rho post ph)
    (p1_target_input_bound P s q n p rho hp post ph) hk

def p1TargetAllStagesLinearConstant (P : SevenDFA α) : Nat :=
  p1TargetAllStagesBudget P*(states P+p1TargetLiteralExtra P+1)

theorem p1_target_stage_constant_linear [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (q n p rho : Nat) (hp : p≤n) (post : Word α) (ph : P1Target.Layout Nat)
    (k : Nat) (hk : k≤5) (C : Conj) (a : Atom)
    (hC : C∈AffineProjection.project k (P1Target.formula P s n q p rho post ph)) (ha : a∈C) :
    ((payload a).eval []).natAbs≤p1TargetAllStagesLinearConstant P*(n+2) := by
  have hh := projected_stage_constant_bound k 5 (inputCap P n) _ _
    (p1_target_covered P s n q p rho post ph)
    (p1_target_input_bound P s q n p rho hp post ph) hk C a hC ha
  have hc := Nat.mul_le_mul_left (p1TargetAllStagesBudget P)
    (cap_linear n (states P) (p1TargetLiteralExtra P))
  change ((payload a).eval []).natAbs≤
    p1TargetAllStagesBudget P*max (inputCap P n) (p1TargetLiteralExtra P) at hh
  change p1TargetAllStagesBudget P*max (inputCap P n) (p1TargetLiteralExtra P)≤
    p1TargetAllStagesBudget P*((states P+p1TargetLiteralExtra P+1)*(n+2)) at hc
  simpa only [p1TargetAllStagesLinearConstant,Nat.mul_assoc] using Nat.le_trans hh hc

theorem p1_target_all_stage_bits [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (q n p rho : Nat) (hp : p≤n) (post : Word α) (ph : P1Target.Layout Nat)
    (k : Nat) (hk : k≤5) (C : Conj) (a : Atom)
    (hC : C∈AffineProjection.project k (P1Target.formula P s n q p rho post ph)) (ha : a∈C) :
    bits ((payload a).eval [])≤(p1TargetAllStagesLinearConstant P).log2+(n+2).log2+2 :=
  linear_bits _ _ n (p1_target_stage_constant_linear P s q n p rho hp post ph k hk C a hC ha)

def p1SourceLinearConstant (P : SevenDFA α) : Nat := p1SourceBudget P*(states P+1)

theorem p1_source_constant_linear (P : SevenDFA α) (s : Nat→α)
    (q n a phase rho : Nat) (ha : a≤n) (pre : Word α) (C : Conj) (atom : Atom)
    (hC : C∈UniformJoin.localSource P s n q a phase rho pre) (hatom : atom∈C) :
    ((payload atom).eval []).natAbs≤p1SourceLinearConstant P*(n+2) := by
  have hh := formula_eval_bound _ _ (p1_source_input_bound P s q n a phase rho ha pre)
    C atom hC hatom
  have hm := projection_budget 0 _ _ (UniformJoin.localSource_covered P s n q a phase rho pre)
  change measure (UniformJoin.localSource P s n q a phase rho pre)≤p1SourceBudget P at hm
  have hc : inputCap P n≤(states P+1)*(n+2) := by
    simpa only [Nat.add_zero,Nat.max_zero] using cap_linear n (states P) 0
  have hb := Nat.mul_le_mul hm hc
  exact Nat.le_trans hh (by simpa only [p1SourceLinearConstant,Nat.mul_assoc] using hb)

theorem p1_source_bits (P : SevenDFA α) (s : Nat→α)
    (q n a phase rho : Nat) (ha : a≤n) (pre : Word α) (C : Conj) (atom : Atom)
    (hC : C∈UniformJoin.localSource P s n q a phase rho pre) (hatom : atom∈C) :
    bits ((payload atom).eval [])≤(p1SourceLinearConstant P).log2+(n+2).log2+2 :=
  linear_bits _ _ n (p1_source_constant_linear P s q n a phase rho ha pre C atom hC hatom)

/-- The actual counted cached target returns the same bounded unary formula. -/
theorem p1_cached_target_bits_at [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (n q p rho : Nat) (hp : p≤n) (w : Word α) (lo hi : Nat)
    (hlo : lo≤w.length) (hhi : hi≤w.length) (ph : P1Target.Layout Nat)
    (C : Conj) (a : Atom)
    (hC : C∈(CountedCachedP1.project P n q p rho
      (BoundaryContexts.prepareAt P s q (BoundaryContexts.build P w).1 lo hi) ph).formula)
    (ha : a∈C) :
    bits ((payload a).eval [])≤(p1TargetAllStagesLinearConstant P).log2+(n+2).log2+2 := by
  rw [CountedCachedP1.project_eq_at P s n q p rho w lo hi hlo hhi ph] at hC
  exact p1_target_all_stage_bits P s q n p rho hp (w.drop hi) ph 5 (by decide) C a hC ha

theorem p1_cached_source_bits_at [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (n q a phase rho : Nat) (ha : a≤n) (w : Word α) (lo hi : Nat)
    (hlo : lo≤w.length) (hhi : hi≤w.length) (C : Conj) (atom : Atom)
    (hC : C∈(CountedCachedP1.source P n q a phase rho
      (BoundaryContexts.prepareAt P s q (BoundaryContexts.build P w).1 lo hi)).formula)
    (hatom : atom∈C) :
    bits ((payload atom).eval [])≤(p1SourceLinearConstant P).log2+(n+2).log2+2 := by
  rw [CountedCachedP1.source_value,CachedP1.sourceAt_eq P s n q a phase rho w lo hi hlo hhi] at hC
  exact p1_source_bits P s q n a phase rho ha (w.take lo) C atom hC hatom

end REWB.ProjectionMagnitude
