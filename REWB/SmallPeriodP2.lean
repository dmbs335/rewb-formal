import REWB.SmallPeriodRuns
import REWB.BoundaryContexts
import REWB.LongSourceCoverage
import REWB.CountedCachedP2

/-! A concrete small-period P2 branch. Runs are generated, contexts are
    prepared once for the text, and every phase uses cached equality.
    Soundness is unconditional; completeness is for the stated cubic-run
    long-outer witness class. Counters distinguish enumeration, context
    entries, cache construction, equality reads, solver invocations, and
    actual measured projection/decision operations. -/
namespace REWB.SmallPeriodP2
open REWB.Periodic REWB.RunGeometry
variable {α : Type}

structure Work where
  accepted : Bool := false
  cacheWork : Nat := 0
  equalityReads : Nat := 0
  phaseCalls : Nat := 0
  projectionSteps : Nat := 0
  deriving Repr

def phases (P : SevenDFA α) (n q : Nat) (I : FullyCachedP2.Shared P) :
    List P2Periodic.Five→Work
  | [] => {}
  | v::vs =>
    let t := CountedCachedP2.solveAt P n q I (P2Periodic.extend q v)
    let r := phases P n q I vs
    ⟨t.accepted || r.accepted,0,t.equalityReads+r.equalityReads,r.phaseCalls+1,
      t.projectionSteps+r.projectionSteps⟩

theorem phases_correct (P : SevenDFA α) (n q : Nat) (I : FullyCachedP2.Shared P)
    (vs : List P2Periodic.Five) :
    (phases P n q I vs).accepted=
      vs.any (fun v=>FullyCachedP2.solveAt P n q I (P2Periodic.extend q v)) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [phases,List.any_cons,CountedCachedP2.solveAt_correct,ih]

theorem phases_counts (P : SevenDFA α) (n q : Nat) (I : FullyCachedP2.Shared P)
    (vs : List P2Periodic.Five) :
    (phases P n q I vs).phaseCalls=vs.length ∧
      (phases P n q I vs).equalityReads≤6*vs.length := by
  induction vs with
  | nil => exact ⟨rfl,Nat.le_refl _⟩
  | cons v vs ih =>
    change (phases P n q I vs).phaseCalls+1=vs.length+1 ∧
      (CountedCachedP2.solveAt P n q I (P2Periodic.extend q v)).equalityReads+
        (phases P n q I vs).equalityReads≤6*(vs.length+1)
    have h := CountedCachedP2.solveAt_equalityReads P n q I (P2Periodic.extend q v)
    rw [Nat.mul_succ]
    exact ⟨by omega,by omega⟩

def run [DecidableEq α] (P : SevenDFA α) (f : Nat→α)
    (I : BoundaryContexts.Index P) (R : Bounds) : Work :=
  let c := BoundaryContexts.countedPrepareAt P (shift f R.lo) R.period I R.lo R.hi
  let r := phases P (R.hi-R.lo) R.period c.1 (P2Periodic.choices R.period)
  {r with cacheWork := c.2}

theorem run_correct [DecidableEq α] (P : SevenDFA α) (f : Nat→α) (w : Word α)
    (R : Bounds) (hlo : R.lo≤w.length) (hhi : R.hi≤w.length) :
    (run P f (BoundaryContexts.build P w).1 R).accepted=
      FullyCachedP2.solveFamily P (shift f R.lo) (R.hi-R.lo) R.period
        (w.take R.lo) (w.drop R.hi) := by
  dsimp only [run]
  rw [BoundaryContexts.countedPrepareAt_correct,
    BoundaryContexts.prepareAt_correct P (shift f R.lo) R.period w R.lo R.hi hlo hhi]
  exact phases_correct _ _ _ _ _

theorem run_counts [DecidableEq α] (P : SevenDFA α) (f : Nat→α)
    (I : BoundaryContexts.Index P) (R : Bounds) :
    (run P f I R).cacheWork=R.period*(FullyCachedP2.stateSum P*R.period)+R.period^3 ∧
    (run P f I R).phaseCalls=R.period^5 ∧
    (run P f I R).equalityReads≤6*R.period^5 := by
  have h := phases_counts P (R.hi-R.lo) R.period
    (BoundaryContexts.countedPrepareAt P (shift f R.lo) R.period I R.lo R.hi).1
    (P2Periodic.choices R.period)
  rw [P2Periodic.choices_length] at h
  exact ⟨BoundaryContexts.countedPrepareAt_cost _ _ _ _ _ _,h⟩

def runs [DecidableEq α] (P : SevenDFA α) (f : Nat→α) (I : BoundaryContexts.Index P) :
    List Bounds→Work
  | [] => {}
  | R::Rs =>
    let a := run P f I R
    let b := runs P f I Rs
    ⟨a.accepted || b.accepted,a.cacheWork+b.cacheWork,
      a.equalityReads+b.equalityReads,a.phaseCalls+b.phaseCalls,
      a.projectionSteps+b.projectionSteps⟩

theorem runs_correct [DecidableEq α] (P : SevenDFA α) (f : Nat→α)
    (I : BoundaryContexts.Index P) (Rs : List Bounds) :
    (runs P f I Rs).accepted=Rs.any (fun R=>(run P f I R).accepted) := by
  induction Rs with
  | nil => rfl
  | cons R Rs ih =>
    change ((run P f I R).accepted || (runs P f I Rs).accepted)=_
    rw [ih]
    rfl

theorem runs_counts [DecidableEq α] (P : SevenDFA α) (f : Nat→α)
    (I : BoundaryContexts.Index P) (Rs : List Bounds) :
    (runs P f I Rs).cacheWork=
      FullyCachedP2.stateSum P*RunBudget.phaseWork 1 Rs+RunBudget.phaseWork 2 Rs ∧
    (runs P f I Rs).phaseCalls=RunBudget.phaseWork 4 Rs ∧
    (runs P f I Rs).equalityReads≤6*RunBudget.phaseWork 4 Rs := by
  induction Rs with
  | nil => simp [runs,RunBudget.phaseWork]
  | cons R Rs ih =>
    have h := run_counts P f I R
    have hpow : R.period*(FullyCachedP2.stateSum P*R.period)=
        FullyCachedP2.stateSum P*R.period^(1+1) := by
      simp only [Nat.pow_succ,Nat.pow_zero,Nat.one_mul]
      ac_rfl
    change (run P f I R).cacheWork+(runs P f I Rs).cacheWork=_ ∧
      (run P f I R).phaseCalls+(runs P f I Rs).phaseCalls=_ ∧
      (run P f I R).equalityReads+(runs P f I Rs).equalityReads≤_
    rw [h.1,hpow,ih.1,h.2.1,ih.2.1]
    refine ⟨?_,rfl,?_⟩
    · change FullyCachedP2.stateSum P*R.period^2+R.period^3+
        (FullyCachedP2.stateSum P*RunBudget.phaseWork 1 Rs+RunBudget.phaseWork 2 Rs)=
        FullyCachedP2.stateSum P*(R.period^2+RunBudget.phaseWork 1 Rs)+
          (R.period^3+RunBudget.phaseWork 2 Rs)
      rw [Nat.mul_add]
      omega
    · change (run P f I R).equalityReads+(runs P f I Rs).equalityReads≤
        6*(R.period^5+RunBudget.phaseWork 4 Rs)
      rw [Nat.mul_add]
      have h1 := h.2.2
      have h2 := ih.2.2
      omega

theorem segment_take (f : Nat→α) (a n k : Nat) (hk : k≤n) :
    (segment f a n).take k=segment f a k := by
  induction k generalizing a n with
  | zero => rfl
  | succ k ih =>
    cases n with
    | zero => omega
    | succ n =>
      change f a::(segment f (a+1) n).take k=f a::segment f (a+1) k
      rw [ih (a+1) n (by omega)]

theorem segment_drop (f : Nat→α) (a n k : Nat) (hk : k≤n) :
    (segment f a n).drop k=segment f (a+k) (n-k) := by
  induction k generalizing a n with
  | zero => simp
  | succ k ih =>
    cases n with
    | zero => omega
    | succ n =>
      change (segment f (a+1) n).drop k=segment f (a+(k+1)) (n+1-(k+1))
      rw [ih (a+1) n (by omega)]
      congr 1 <;> omega

theorem text_reconstruct (f : Nat→α) (n lo hi : Nat) (hlo : lo≤hi) (hhi : hi≤n) :
    (segment f 0 n).take lo++segment (shift f lo) 0 (hi-lo)++
      (segment f 0 n).drop hi=segment f 0 n := by
  rw [segment_take f 0 n lo (by omega),segment_drop f 0 n hi hhi,
    LongSourceCoverage.segment_shift]
  simp only [Nat.add_zero,Nat.zero_add]
  have h1 := segment_append f 0 lo (hi-lo)
  have h2 := segment_append f 0 hi (n-hi)
  simp only [Nat.zero_add] at h1 h2
  rw [show lo+(hi-lo)=hi by omega] at h1
  rw [show hi+(n-hi)=n by omega] at h2
  rw [← h1,← h2]

structure Result extends Work where
  runComparisons : Nat := 0
  contextEntries : Nat := 0
  deriving Repr

def solve [DecidableEq α] (P : SevenDFA α) (f : Nat→α) (n Q : Nat) : Result :=
  let contexts := BoundaryContexts.build P (segment f 0 n)
  let enumerated := SmallPeriodRuns.enumerate f n Q
  let Rs := enumerated.1.filter (fun R=>decide (3*R.period≤R.hi-R.lo))
  ⟨runs P f contexts.1 Rs,enumerated.2,contexts.2⟩

theorem solve_sound [DecidableEq α] (P : SevenDFA α) (f : Nat→α) (n Q : Nat)
    (hs : (solve P f n Q).accepted=true) :
    MatchesWithin P.nested2 (segment f 0 n) 2 := by
  change (runs P f (BoundaryContexts.build P (segment f 0 n)).1
    (SmallPeriodRuns.cubic f n Q)).accepted=true at hs
  rw [runs_correct] at hs
  obtain ⟨R,hR,hyes⟩ := List.any_eq_true.mp hs
  have hv := ((SmallPeriodRuns.cubic_mem f n Q R).mp hR).1
  have hlo : R.lo≤(segment f 0 n).length := by
    rw [segment_length]
    have ha := hv.1
    have hb := hv.2.1
    omega
  have hhi : R.hi≤(segment f 0 n).length := by rw [segment_length]; exact hv.2.1
  rw [run_correct P f (segment f 0 n) R hlo hhi] at hyes
  have hmatch := FullyCachedP2.solveFamily_sound P (shift f R.lo) (R.hi-R.lo) R.period
    hv.2.2.2.1 ((segment f 0 n).take R.lo) ((segment f 0 n).drop R.hi) hyes
  rw [text_reconstruct f n R.lo R.hi (by have h := hv.1; omega) hv.2.1] at hmatch
  exact hmatch

/-- Completeness for the small-period cubic branch. The witness class is
    explicit; short, non-cubic or large-period witnesses need other branches. -/
theorem solve_complete [DecidableEq α] (P : SevenDFA α) (f : Nat→α) (n Q : Nat)
    (R : Bounds) (hR : R.Valid f n) (hq : R.period≤Q)
    (hc : 3*R.period≤R.hi-R.lo) (x : P2Periodic.Layout Nat)
    (hw : P2Periodic.Witness P (shift f R.lo) (R.hi-R.lo)
      ((segment f 0 n).take R.lo) ((segment f 0 n).drop R.hi) x)
    (hlong : R.period≤x.e-x.p) : (solve P f n Q).accepted=true := by
  change (runs P f (BoundaryContexts.build P (segment f 0 n)).1
    (SmallPeriodRuns.cubic f n Q)).accepted=true
  rw [runs_correct]
  apply List.any_eq_true.mpr
  refine ⟨R,(SmallPeriodRuns.cubic_mem f n Q R).mpr ⟨hR,hq,hc⟩,?_⟩
  rw [run_correct P f (segment f 0 n) R
    (by rw [segment_length]; have ha := hR.1; have hb := hR.2.1; omega)
    (by rw [segment_length]; exact hR.2.1)]
  exact FullyCachedP2.solveFamily_complete_long P (shift f R.lo) (R.hi-R.lo)
    R.period hR.2.2.2.1 _ _ x hw hlong

theorem solve_counts [DecidableEq α] (P : SevenDFA α) (f : Nat→α) (n Q : Nat) :
    (solve P f n Q).runComparisons≤Q*(n+(n+1)*(2*Q*(Q+1)+1)) ∧
    (solve P f n Q).contextEntries=(n+1)*(1+P.H.stateCount) ∧
    (solve P f n Q).cacheWork≤
      (FullyCachedP2.stateSum P*Q+Q^2)*(2*n*DyadicIndex.heightFor n) ∧
    (solve P f n Q).phaseCalls≤Q^4*(2*n*DyadicIndex.heightFor n) ∧
    (solve P f n Q).equalityReads≤6*(Q^4*(2*n*DyadicIndex.heightFor n)) := by
  have hr := runs_counts P f (BoundaryContexts.build P (segment f 0 n)).1
    (SmallPeriodRuns.cubic f n Q)
  have h1 := SmallPeriodRuns.cubic_phase_bound f n Q 1
  have h2 := SmallPeriodRuns.cubic_phase_bound f n Q 2
  have h4 := SmallPeriodRuns.cubic_phase_bound f n Q 4
  refine ⟨SmallPeriodRuns.enumerate_cost f n Q,?_,?_,?_,?_⟩
  · change (BoundaryContexts.build P (segment f 0 n)).2=_
    rw [BoundaryContexts.build_cost,segment_length]
  · change (runs P f _ (SmallPeriodRuns.cubic f n Q)).cacheWork≤_
    rw [hr.1,Nat.add_mul]
    have hfirst := Nat.mul_le_mul_left (FullyCachedP2.stateSum P) h1
    simpa only [Nat.pow_one,Nat.mul_assoc] using Nat.add_le_add hfirst h2
  · change (runs P f _ (SmallPeriodRuns.cubic f n Q)).phaseCalls≤_
    rw [hr.2.1]
    exact h4
  · exact Nat.le_trans hr.2.2 (Nat.mul_le_mul_left 6 h4)

/-- Each phase executes the instrumented projection and eager decision,
    whose measured work has a pattern-only bound. -/
theorem phases_projection_steps [DecidableEq α] (P : SevenDFA α) (f : Nat→α)
    (n q : Nat) (pre post : Word α) (vs : List P2Periodic.Five) :
    (phases P n q (FullyCachedP2.prepare P f q pre post) vs).projectionSteps≤
      CountedProjection.p2Steps P*vs.length := by
  induction vs with
  | nil => simp [phases]
  | cons v vs ih =>
    have hv := CountedCachedP2.solveAt_projectionSteps P f n q pre post (P2Periodic.extend q v)
    change (CountedCachedP2.solveAt P n q (FullyCachedP2.prepare P f q pre post)
      (P2Periodic.extend q v)).projectionSteps+
      (phases P n q (FullyCachedP2.prepare P f q pre post) vs).projectionSteps≤
        CountedProjection.p2Steps P*(vs.length+1)
    rw [Nat.mul_add,Nat.mul_one]
    omega

theorem run_projection_steps [DecidableEq α] (P : SevenDFA α) (f : Nat→α)
    (w : Word α) (R : Bounds) (hlo : R.lo≤w.length) (hhi : R.hi≤w.length) :
    (run P f (BoundaryContexts.build P w).1 R).projectionSteps≤
      CountedProjection.p2Steps P*R.period^5 := by
  change (phases P (R.hi-R.lo) R.period
    (BoundaryContexts.countedPrepareAt P (shift f R.lo) R.period
      (BoundaryContexts.build P w).1 R.lo R.hi).1
    (P2Periodic.choices R.period)).projectionSteps≤_
  rw [BoundaryContexts.countedPrepareAt_correct,
    BoundaryContexts.prepareAt_correct P (shift f R.lo) R.period w R.lo R.hi hlo hhi]
  have h := phases_projection_steps P (shift f R.lo) (R.hi-R.lo) R.period
    (w.take R.lo) (w.drop R.hi) (P2Periodic.choices R.period)
  rwa [P2Periodic.choices_length] at h

theorem runs_projection_steps [DecidableEq α] (P : SevenDFA α) (f : Nat→α)
    (w : Word α) (Rs : List Bounds)
    (hR : ∀ R,R∈Rs→R.lo≤w.length ∧ R.hi≤w.length) :
    (runs P f (BoundaryContexts.build P w).1 Rs).projectionSteps≤
      CountedProjection.p2Steps P*RunBudget.phaseWork 4 Rs := by
  induction Rs with
  | nil => simp [runs,RunBudget.phaseWork]
  | cons R Rs ih =>
    have h := hR R (by simp)
    have hx := run_projection_steps P f w R h.1 h.2
    have hy := ih (fun r hr=>hR r (by simp [hr]))
    change (run P f (BoundaryContexts.build P w).1 R).projectionSteps+
      (runs P f (BoundaryContexts.build P w).1 Rs).projectionSteps≤
        CountedProjection.p2Steps P*(R.period^5+RunBudget.phaseWork 4 Rs)
    rw [Nat.mul_add]
    exact Nat.add_le_add hx hy

/-- Global projection/decision count for the actual small-period branch.
    C_P is determined solely by the pattern. Run enumeration, cache
    construction and equality reads are accounted for by solve_counts;
    sorting/GC and a concrete bit-level machine remain separate. -/
theorem solve_projection_steps [DecidableEq α] (P : SevenDFA α) (f : Nat→α)
    (n Q : Nat) :
    (solve P f n Q).projectionSteps≤
      CountedProjection.p2Steps P*Q^4*(2*n*DyadicIndex.heightFor n) := by
  have hr := runs_projection_steps P f (segment f 0 n) (SmallPeriodRuns.cubic f n Q)
    (fun R hR=>by
      have hv := ((SmallPeriodRuns.cubic_mem f n Q R).mp hR).1
      rw [segment_length]
      have hlo := hv.1
      have hhi := hv.2.1
      exact ⟨by omega,hhi⟩)
  have hb := Nat.mul_le_mul_left (CountedProjection.p2Steps P)
    (SmallPeriodRuns.cubic_phase_bound f n Q 4)
  change (runs P f (BoundaryContexts.build P (segment f 0 n)).1
    (SmallPeriodRuns.cubic f n Q)).projectionSteps≤_
  simpa only [Nat.mul_assoc] using Nat.le_trans hr hb

end REWB.SmallPeriodP2
