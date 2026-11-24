import REWB.RunExtension

/-! Coverage of the earlier source of a long P1 inner copy.
    Equality to a sufficiently long factor of a run forces the same
    minimum period in the source. Its maximal run contains the entire
    source, and the canonical period-block keys agree exactly. -/
namespace REWB.LongSourceCoverage
open REWB.Periodic REWB.RunGeometry
variable {α : Type}

theorem segment_shift (f : Nat→α) (a b L : Nat) :
    segment (shift f a) b L=segment f (a+b) L := by
  induction L generalizing b with
  | zero => rfl
  | succ L ih =>
    change f (a+b)::segment (shift f a) (b+1) L=
      f (a+b)::segment f (a+b+1) L
    rw [ih,← Nat.add_assoc]

theorem period_transport (f : Nat→α) (a b L p : Nat)
    (h : segment f a L=segment f b L) :
    Period (shift f a) L p ↔ Period (shift f b) L p := by
  have he := (segment_eq_points f a b L).mp h
  constructor
  · intro hp i hi
    have h1 := he i (by omega)
    have h2 := he (i+p) hi
    have hh := hp i hi
    unfold shift at hh ⊢
    exact h1.symm.trans (hh.trans h2)
  · intro hp i hi
    have h1 := he i (by omega)
    have h2 := he (i+p) hi
    have hh := hp i hi
    unfold shift at hh ⊢
    exact h1.trans (hh.trans h2.symm)

theorem least_transport (f : Nat→α) (a b L p : Nat)
    (h : segment f a L=segment f b L)
    (hp : LeastPeriod (shift f b) L p) :
    LeastPeriod (shift f a) L p :=
  ⟨hp.1,(period_transport f a b L p h).mpr hp.2.1,
    fun q hq hQ=>hp.2.2 q hq ((period_transport f a b L q h).mp hQ)⟩

variable [DecidableEq α]

theorem factor_in_run (f : Nat→α) (n i L p : Nat)
    (hn : i+L≤n) (hL : 2*p≤L) (h : LeastPeriod (shift f i) L p) :
    ∃ R : Bounds,R.Valid f n ∧ R.period=p ∧ R.lo≤i ∧ i+L≤R.hi := by
  have hsq : PrimitiveSquare f n i p := by
    refine ⟨by omega,?_⟩
    have hh := least_factor (shift f i) L p 0 (2*p) h (Nat.le_refl _) (by omega)
    have he : shift (shift f i) 0=shift f i := by
      funext j
      simp [shift]
    rwa [he] at hh
  let R := RunExtension.extend f n i p
  have hv := RunExtension.extend_valid f n i p hsq
  have hc := RunExtension.extend_contains f n i p hsq
  refine ⟨R,hv,rfl,hc.1,?_⟩
  let b := RunExtension.right f p (n-p-(i+p)) (i+p)
  have hr := RunExtension.right_spec f p (n-p-(i+p)) (i+p)
  change i+p≤b ∧ b≤i+p+(n-p-(i+p)) ∧
    (∀ j,i+p≤j→j<b→f j=f (j+p)) ∧
    (b=i+p+(n-p-(i+p)) ∨ f b≠f (b+p)) at hr
  change i+L≤b+p
  by_cases he : i+L≤b+p
  · exact he
  · rcases hr.2.2.2 with hend|hbad
    · omega
    · have hP := (on_iff f i (i+L) p).mpr (show Period (shift f i) (i+L-i) p by
        rw [show i+L-i=L by omega]
        exact h.2.1)
      exact False.elim (hbad (hP b (by omega) (by omega)))

theorem phase_key (f : Nat→α) (n : Nat) (R : Bounds) (h : R.Valid f n)
    (i : Nat) (hi : R.lo≤i) (hn : i+R.period≤R.hi) :
    segment (shift f R.lo) ((i-R.lo)%R.period) R.period=
      segment f i R.period := by
  have hh := factor_at_phase h.2.2.2.1.2.1 (i-R.lo) R.period (by omega)
  rw [segment_shift,show R.lo+(i-R.lo)=i by omega] at hh
  exact hh.symm

/-- A long equal source and target determine the same exact period key.
    If L >= 3p the source run is cubic as well. -/
theorem long_source (f : Nat→α) (n i j L : Nat) (T : Bounds)
    (ht : T.Valid f n) (hj : T.lo≤j) (hjt : j+L≤T.hi)
    (hL : 2*T.period≤L) (hi : i+L≤n)
    (he : segment f i L=segment f j L) :
    ∃ S : Bounds,S.Valid f n ∧ S.period=T.period ∧ S.lo≤i ∧ i+L≤S.hi ∧
      segment (shift f S.lo) ((i-S.lo)%T.period) T.period =
        segment (shift f T.lo) ((j-T.lo)%T.period) T.period := by
  have htarget := on_least_factor f T.lo T.hi T.period j (j+L)
    ht.2.2.2.1 hj hjt (by omega)
  rw [show j+L-j=L by omega] at htarget
  have hsource := least_transport f i j L T.period he htarget
  obtain ⟨S,hS,hp,hlo,hhi⟩ := factor_in_run f n i L T.period hi hL hsource
  have h1 := phase_key f n S hS i hlo (by omega)
  rw [hp] at h1
  have h2 := phase_key f n T ht j hj (by omega)
  refine ⟨S,hS,hp,hlo,hhi,?_⟩
  rw [h1,h2]
  apply (segment_eq_points f i j T.period).mpr
  intro k hk
  exact (segment_eq_points f i j L).mp he k (by omega)

end REWB.LongSourceCoverage
