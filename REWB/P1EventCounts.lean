import REWB.P1Events

/-! Actual operation counters of concrete P1 event generation. The
    event lists and their measured projection work come from P1Events.run;
    all global bounds use the concrete small-period run enumerator. -/
namespace REWB.P1Events
open REWB.Periodic REWB.RunGeometry
variable {σ : Nat}

theorem sum_map_le_constant {X : Type} (xs : List X) (f : X→Nat) (B : Nat)
    (h : ∀ x,f x≤B) : (xs.map f).sum≤B*xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.mul_add,Nat.mul_one]
    exact Nat.le_trans (Nat.add_le_add (h x) ih) (by omega)

theorem run_equality_reads (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (I : BoundaryContexts.Index P)
    (Q next : Nat) (e : Bounds×Array Nat) :
    (run P f I Q next e).equalityReads≤3*(run P f I Q next e).targets.length := by
  have h := sum_map_le_constant (P1PhaseFamily.targets e.1.period (e.1.hi-e.1.lo))
    (fun v=>(targetWork P Q next e.1 e.2
      (BoundaryContexts.countedPrepareAt P (shift f e.1.lo) e.1.period I e.1.lo e.1.hi).1 v).2.1) 3
    (fun v=>CountedCachedP1.project_equalityReads P _ _ _ _ _ _)
  simpa only [run,List.map_map,List.length_map,Function.comp_def] using h

theorem runs_equality_reads (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (I : BoundaryContexts.Index P)
    (Q next : Nat) (es : List (Bounds×Array Nat)) :
    (runs P f I Q next es).equalityReads≤3*(runs P f I Q next es).targets.length := by
  induction es with
  | nil => simp [runs]
  | cons e es ih =>
    have h := run_equality_reads P f I Q next e
    change (run P f I Q next e).equalityReads+(runs P f I Q next es).equalityReads≤_
    simp only [runs,List.length_append,Nat.mul_add]
    exact Nat.add_le_add h ih

theorem run_projection_steps (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (w : Word (Fin σ))
    (Q next : Nat) (e : Bounds×Array Nat) (hlo : e.1.lo≤w.length) (hhi : e.1.hi≤w.length) :
    (run P f (BoundaryContexts.build P w).1 Q next e).projectionSteps≤
      CountedCachedP1.targetSteps P*(run P f (BoundaryContexts.build P w).1 Q next e).targets.length := by
  have h := sum_map_le_constant (P1PhaseFamily.targets e.1.period (e.1.hi-e.1.lo))
    (fun v=>(targetWork P Q next e.1 e.2
      (BoundaryContexts.countedPrepareAt P (shift f e.1.lo) e.1.period
        (BoundaryContexts.build P w).1 e.1.lo e.1.hi).1 v).2.2)
    (CountedCachedP1.targetSteps P) (fun v=>by
      change (CountedCachedP1.project P (e.1.hi-e.1.lo) e.1.period v.1 v.2.rho
        (BoundaryContexts.countedPrepareAt P (shift f e.1.lo) e.1.period
          (BoundaryContexts.build P w).1 e.1.lo e.1.hi).1
        (P1PhaseFamily.extend e.1.period v.1 v.2)).projectionSteps≤_
      rw [BoundaryContexts.countedPrepareAt_correct]
      exact CountedCachedP1.project_steps_at P (shift f e.1.lo) _ _ _ _
        w e.1.lo e.1.hi hlo hhi _)
  simpa only [run,List.map_map,List.length_map,Function.comp_def] using h

theorem runs_projection_steps (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (w : Word (Fin σ))
    (Q next : Nat) (es : List (Bounds×Array Nat))
    (hv : ∀ e,e∈es→e.1.lo≤w.length ∧ e.1.hi≤w.length) :
    (runs P f (BoundaryContexts.build P w).1 Q next es).projectionSteps≤
      CountedCachedP1.targetSteps P*(runs P f (BoundaryContexts.build P w).1 Q next es).targets.length := by
  induction es with
  | nil => simp [runs]
  | cons e es ih =>
    have he := hv e (by simp)
    have h := run_projection_steps P f w Q next e he.1 he.2
    have ht := ih (fun z hz=>hv z (by simp [hz]))
    change (run P f (BoundaryContexts.build P w).1 Q next e).projectionSteps+
      (runs P f (BoundaryContexts.build P w).1 Q next es).projectionSteps≤_
    simp only [runs,List.length_append,Nat.mul_add]
    exact Nat.add_le_add h ht

theorem generated_equality_reads_length (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (generated P f n Q).equalityReads≤3*(generated P f n Q).targets.length :=
  runs_equality_reads P f _ Q _ _

theorem generated_equality_reads (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (generated P f n Q).equalityReads≤9*Q^3*(2*n*DyadicIndex.heightFor n) := by
  have h := Nat.le_trans (generated_equality_reads_length P f n Q)
    (Nat.mul_le_mul_left 3 (generated_sizes P f n Q).2)
  simpa only [← Nat.mul_assoc] using h

theorem generated_projection_steps_length (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (generated P f n Q).projectionSteps≤
      CountedCachedP1.targetSteps P*(generated P f n Q).targets.length := by
  apply runs_projection_steps P f (segment f 0 n)
  intro e he
  have hm : e.1∈SmallPeriodRuns.cubic f n Q := by
    rw [← ExactKeys.buildRunTables_runs ExactKeys.initial f (SmallPeriodRuns.cubic f n Q)]
    exact List.mem_map.mpr ⟨e,he,rfl⟩
  have hv := ((SmallPeriodRuns.cubic_mem f n Q e.1).mp hm).1
  rw [segment_length]
  have hlo := hv.1
  have hhi := hv.2.1
  exact ⟨by omega,hhi⟩

theorem generated_projection_steps (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (generated P f n Q).projectionSteps≤
      CountedCachedP1.targetSteps P*3*Q^3*(2*n*DyadicIndex.heightFor n) := by
  have h := Nat.le_trans (generated_projection_steps_length P f n Q)
    (Nat.mul_le_mul_left (CountedCachedP1.targetSteps P) (generated_sizes P f n Q).2)
  simpa only [Nat.mul_assoc] using h

theorem generated_cache_work (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (generated P f n Q).cacheWork≤
      (FullyCachedP2.stateSum P*Q+Q^2)*(2*n*DyadicIndex.heightFor n) := by
  have hr := runs_cache P f (BoundaryContexts.build P (segment f 0 n)).1 Q
    (ExactKeys.buildRunTables ExactKeys.initial f (SmallPeriodRuns.cubic f n Q)).registry.next
    (ExactKeys.buildRunTables ExactKeys.initial f (SmallPeriodRuns.cubic f n Q)).tables
  rw [ExactKeys.buildRunTables_runs] at hr
  change (runs P f _ Q _ _).cacheWork≤_
  rw [hr,Nat.add_mul]
  have h1 := SmallPeriodRuns.cubic_phase_bound f n Q 1
  have h2 := SmallPeriodRuns.cubic_phase_bound f n Q 2
  have hfirst := Nat.mul_le_mul_left (FullyCachedP2.stateSum P) h1
  simpa only [Nat.pow_one,Nat.mul_assoc] using Nat.add_le_add hfirst h2

/-- Trie visits of the exact phase-word rank construction actually used
    by generated; ranks are read from its run-local arrays thereafter. -/
theorem generated_key_work (f : Nat→Fin σ) (n Q : Nat) :
    (ExactKeys.buildRunTables ExactKeys.initial f (SmallPeriodRuns.cubic f n Q)).work≤
      ((3*σ+1)*Q+1)*(2*n*DyadicIndex.heightFor n) :=
  ExactKeys.buildRunTables_cubic_cost ExactKeys.initial f n Q _
    (SmallPeriodRuns.cubic_nodup f n Q)
    (fun R h=>((SmallPeriodRuns.cubic_mem f n Q R).mp h).1)
    (fun R h=>((SmallPeriodRuns.cubic_mem f n Q R).mp h).2)

theorem generated_registry_next (f : Nat→Fin σ) (n Q : Nat) :
    (ExactKeys.buildRunTables ExactKeys.initial f (SmallPeriodRuns.cubic f n Q)).registry.next≤
      2*n*DyadicIndex.heightFor n := by
  have h := ExactKeys.buildRunTables_next ExactKeys.initial f (SmallPeriodRuns.cubic f n Q)
  have hb := SmallPeriodRuns.cubic_phase_bound f n Q 0
  simp only [ExactKeys.initial,Nat.zero_add] at h
  simp only [Nat.pow_zero,Nat.one_mul] at hb
  exact Nat.le_trans h hb

theorem generated_counts (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (generated P f n Q).cacheWork≤
      (FullyCachedP2.stateSum P*Q+Q^2)*(2*n*DyadicIndex.heightFor n) ∧
    (generated P f n Q).equalityReads≤9*Q^3*(2*n*DyadicIndex.heightFor n) ∧
    (generated P f n Q).projectionSteps≤
      CountedCachedP1.targetSteps P*3*Q^3*(2*n*DyadicIndex.heightFor n) :=
  ⟨generated_cache_work P f n Q,generated_equality_reads P f n Q,generated_projection_steps P f n Q⟩

end REWB.P1Events
