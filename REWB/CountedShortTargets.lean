import REWB.P1ShortTargets
import REWB.CountedCachedP1

/-! Measured short-target generation. Each anchored phase executes one
    measured five-variable projection and three measured decisions of
    its result. Successful decisions read a precomputed full-word rank.

    The returned event lists are exactly P1ShortTargets' lists. Counters
    distinguish cache construction, equality reads, projection operations,
    decision operations, exponent tests, and key-array reads. Descriptor
    construction, initial formula assembly, allocation and bit-level
    arithmetic retain the limitations of the underlying counters. -/
namespace REWB.CountedShortTargets
open REWB.Periodic REWB.RunGeometry REWB.AffineProjection
open REWB.UniformProjection REWB.UniformPhaseBounds
open REWB.P1ShortSources (trueEntry)
variable {α : Type}

structure Result where
  events : List TimedJoin.TimedEntry := []
  cacheWork : Nat := 0
  equalityReads : Nat := 0
  projectionSteps : Nat := 0
  decisionSteps : Nat := 0
  exponentTests : Nat := 0
  keyReads : Nat := 0
  deriving Repr

/-- The measured event work, with cache preparation kept separate. -/
def work (r : Result) : Nat :=
  r.equalityReads+r.projectionSteps+r.decisionSteps+r.exponentTests+r.keyReads

def join (a b : Result) : Result :=
  ⟨a.events++b.events,a.cacheWork+b.cacheWork,a.equalityReads+b.equalityReads,
    a.projectionSteps+b.projectionSteps,a.decisionSteps+b.decisionSteps,
    a.exponentTests+b.exponentTests,a.keyReads+b.keyReads⟩

theorem join_work (a b : Result) : work (join a b)=work a+work b := by
  simp only [work,join]
  omega

def collect {X : Type} (step : X→Result) : List X→Result
  | [] => {}
  | x::xs => join (step x) (collect step xs)

/-- `List.foldr` has a proved array-based runtime implementation. Keep
    the structural proof definition above without consuming one runtime
    stack frame for every anchored target. -/
def collectTR {X : Type} (step : X→Result) (xs : List X) : Result :=
  xs.foldr (fun x r=>join (step x) r) {}

@[csimp] theorem collect_eq_collectTR : @collect=@collectTR := by
  funext X step xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change join (step x) (collect step xs)=join (step x) (collectTR step xs)
    rw [ih]

theorem collect_events {X : Type} (step : X→Result) (xs : List X) :
    (collect step xs).events=xs.flatMap (fun x=>(step x).events) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (step x).events++(collect step xs).events=_
    rw [ih]
    rfl

theorem collect_bound {X : Type} (step : X→Result) (xs : List X)
    (cost : Result→Nat) (hzero : cost {}=0)
    (hadd : ∀ a b,cost (join a b)=cost a+cost b) (B : Nat)
    (h : ∀ x,x∈xs→cost (step x)≤B) : cost (collect step xs)≤B*xs.length := by
  induction xs with
  | nil => simp only [collect,hzero,List.length_nil,Nat.mul_zero,Nat.le_refl]
  | cons x xs ih =>
    rw [collect,hadd,List.length_cons,Nat.mul_succ]
    have hx := h x (by simp)
    have hs := ih (fun y hy=>h y (by simp [hy]))
    omega

theorem collect_constant {X : Type} (step : X→Result) (xs : List X)
    (cost : Result→Nat) (hzero : cost {}=0)
    (hadd : ∀ a b,cost (join a b)=cost a+cost b) (B : Nat)
    (h : ∀ x,x∈xs→cost (step x)=B) : cost (collect step xs)=B*xs.length := by
  induction xs with
  | nil => simpa only [collect,hzero,List.length_nil,Nat.mul_zero]
  | cons x xs ih =>
    rw [collect,hadd,h x (by simp),ih (fun y hy=>h y (by simp [hy])),List.length_cons,Nat.mul_succ]
    omega

/-- Every exponent is tested, and rank lookup happens only when an
    event is emitted. The formula is supplied already projected. -/
def checks (F : Formula) (q lo p : Nat) (v : P1PhaseFamily.Three) (ranks : Array Nat) :
    List Nat→Result
  | [] => {}
  | m::ms =>
    let d := CountedProjection.decide [(m:Int)] F
    let r := checks F q lo p v ranks ms
    {events := if d.1 then
        trueEntry (lo+p) (ranks[P1ShortKeys.index q v.j v.rho m]?.getD 0)::r.events else r.events
     decisionSteps := d.2+r.decisionSteps
     exponentTests := r.exponentTests+1
     keyReads := (if d.1 then 1 else 0)+r.keyReads}

theorem checks_value (F : Formula) (q lo p : Nat) (v : P1PhaseFamily.Three)
    (ranks : Array Nat) (ms : List Nat) :
    (checks F q lo p v ranks ms).events=
      (ms.filter (fun m : Nat=>decideFormula F [(m:Int)])).map
        (fun m=>trueEntry (lo+p) (ranks[P1ShortKeys.index q v.j v.rho m]?.getD 0)) := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    simp only [checks,CountedProjection.decide_value,ih,List.filter_cons]
    split <;> simp

theorem checks_tests (F : Formula) (q lo p : Nat) (v : P1PhaseFamily.Three)
    (ranks : Array Nat) (ms : List Nat) :
    (checks F q lo p v ranks ms).exponentTests=ms.length := by
  induction ms with
  | nil => rfl
  | cons m ms ih => simpa only [checks,List.length_cons] using congrArg (·+1) ih

theorem checks_reads (F : Formula) (q lo p : Nat) (v : P1PhaseFamily.Three)
    (ranks : Array Nat) (ms : List Nat) :
    (checks F q lo p v ranks ms).keyReads≤ms.length := by
  induction ms with
  | nil => exact Nat.le_refl _
  | cons m ms ih =>
    change (if (CountedProjection.decide [(m:Int)] F).1 then 1 else 0)+
      (checks F q lo p v ranks ms).keyReads≤ms.length+1
    have hd : (if (CountedProjection.decide [(m:Int)] F).1 then 1 else 0)≤1 := by
      split <;> decide
    omega

theorem checks_decisions (F : Formula) (q lo p : Nat) (v : P1PhaseFamily.Three)
    (ranks : Array Nat) (ms : List Nat) (B : Nat)
    (h : ∀ m,m∈ms→(CountedProjection.decide [(m:Int)] F).2≤B) :
    (checks F q lo p v ranks ms).decisionSteps≤B*ms.length := by
  induction ms with
  | nil => simp [checks]
  | cons m ms ih =>
    change (CountedProjection.decide [(m:Int)] F).2+
      (checks F q lo p v ranks ms).decisionSteps≤B*(ms.length+1)
    rw [Nat.mul_succ]
    have hm := h m (by simp)
    have hs := ih (fun k hk=>h k (by simp [hk]))
    omega

def choiceTargets (P : SevenDFA α) (n q lo p : Nat) (v : P1PhaseFamily.Three)
    (I : FullyCachedP2.Shared P) (ranks : Array Nat) : Result :=
  let projected := CountedCachedP1.project P n q p v.rho I (P1PhaseFamily.extend q p v)
  let r := checks projected.formula q lo p v ranks (List.range 3)
  {r with equalityReads := projected.equalityReads, projectionSteps := projected.projectionSteps}

theorem choiceTargets_value (P : SevenDFA α) (n q lo p : Nat) (v : P1PhaseFamily.Three)
    (I : FullyCachedP2.Shared P) (ranks : Array Nat) :
    (choiceTargets P n q lo p v I ranks).events=P1ShortTargets.choiceTargets P n q lo p v I ranks := by
  simp only [choiceTargets,checks_value,CountedCachedP1.project_value,
    P1ShortTargets.choiceTargets,CachedP1.countedProjection_correct]

theorem choiceTargets_reads (P : SevenDFA α) (n q lo p : Nat) (v : P1PhaseFamily.Three)
    (I : FullyCachedP2.Shared P) (ranks : Array Nat) :
    (choiceTargets P n q lo p v I ranks).equalityReads≤3 ∧
    (choiceTargets P n q lo p v I ranks).exponentTests=3 ∧
    (choiceTargets P n q lo p v I ranks).keyReads≤3 := by
  refine ⟨CountedCachedP1.project_equalityReads P n q p v.rho I _,?_,?_⟩
  · exact checks_tests _ _ _ _ _ _ _
  · exact checks_reads _ _ _ _ _ _ _

/-- This constant is used only in the bound, not evaluated by the event
    generator. It bounds a decision of any actual projected target. -/
def decisionSteps (P : SevenDFA α) : Nat :=
  CountedProjection.stepsBudget 5 1 (p1TargetFamily P)

theorem decide_project_le_solve (k : Nat) (F : Formula) (env : List Int) :
    (CountedProjection.decide env (AffineProjection.project k F)).2≤
      (CountedProjection.solve k F env).2 := by
  unfold CountedProjection.solve
  dsimp only
  rw [CountedProjection.project_value]
  omega

theorem projected_decision_bound (P : SevenDFA α) (n q p rho : Nat)
    (I : FullyCachedP2.Shared P) (ph : P1Target.Layout Nat)
    (h : Covered (CachedP1.targetFormula P n q p rho I ph) (p1TargetFamily P)) (m : Nat) :
    (CountedProjection.decide [(m:Int)] (CountedCachedP1.project P n q p rho I ph).formula).2≤
      decisionSteps P := by
  rw [CountedCachedP1.project_value]
  change (CountedProjection.decide [(m:Int)]
    (AffineProjection.project 5 (CachedP1.targetFormula P n q p rho I ph))).2≤_
  exact Nat.le_trans (decide_project_le_solve _ _ _)
    (CountedProjection.solve_uniform_steps _ _ _ [(m:Int)] h)

theorem choiceTargets_steps (P : SevenDFA α) (n q lo p : Nat) (v : P1PhaseFamily.Three)
    (I : FullyCachedP2.Shared P) (ranks : Array Nat)
    (h : Covered (CachedP1.targetFormula P n q p v.rho I (P1PhaseFamily.extend q p v))
      (p1TargetFamily P)) :
    (choiceTargets P n q lo p v I ranks).projectionSteps≤CountedCachedP1.targetSteps P ∧
    (choiceTargets P n q lo p v I ranks).decisionSteps≤3*decisionSteps P := by
  refine ⟨CountedCachedP1.project_steps_of_covered P n q p v.rho I _ h,?_⟩
  have hd := checks_decisions
    (CountedCachedP1.project P n q p v.rho I (P1PhaseFamily.extend q p v)).formula
    q lo p v ranks (List.range 3) (decisionSteps P)
    (fun m _=>projected_decision_bound P n q p v.rho I _ h m)
  simpa only [choiceTargets,List.length_range,Nat.mul_comm (decisionSteps P) 3] using hd

def anchorWork (P : SevenDFA α) : Nat :=
  CountedCachedP1.targetSteps P+3*decisionSteps P+9

theorem choiceTargets_work (P : SevenDFA α) (n q lo p : Nat) (v : P1PhaseFamily.Three)
    (I : FullyCachedP2.Shared P) (ranks : Array Nat)
    (h : Covered (CachedP1.targetFormula P n q p v.rho I (P1PhaseFamily.extend q p v))
      (p1TargetFamily P)) : work (choiceTargets P n q lo p v I ranks)≤anchorWork P := by
  obtain ⟨he,ht,hk⟩ := choiceTargets_reads P n q lo p v I ranks
  obtain ⟨hp,hd⟩ := choiceTargets_steps P n q lo p v I ranks h
  unfold work anchorWork
  omega

theorem choiceTargets_covered_at [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (n q p rho : Nat) (w : Word α) (lo hi : Nat) (hlo : lo≤w.length) (hhi : hi≤w.length)
    (ph : P1Target.Layout Nat) :
    Covered (CachedP1.targetFormula P n q p rho
      (BoundaryContexts.prepareAt P s q (BoundaryContexts.build P w).1 lo hi) ph) (p1TargetFamily P) := by
  rw [CachedP1.targetFormulaAt_eq P s n q p rho w lo hi hlo hhi ph]
  exact p1_target_covered P s n q p rho (w.drop hi) ph

def runTargets [DecidableEq α] (P : SevenDFA α) (f : Nat→α)
    (I : BoundaryContexts.Index P) (e : Bounds×Array Nat) : Result :=
  let c := BoundaryContexts.countedPrepareAt P (shift f e.1.lo) e.1.period I e.1.lo e.1.hi
  let r := collect (fun z : Nat×P1PhaseFamily.Three=>
    choiceTargets P (e.1.hi-e.1.lo) e.1.period e.1.lo z.1 z.2 c.1 e.2)
    (P1PhaseFamily.targets e.1.period (e.1.hi-e.1.lo))
  {r with cacheWork := c.2}

theorem runTargets_value [DecidableEq α] (P : SevenDFA α) (f : Nat→α)
    (I : BoundaryContexts.Index P) (e : Bounds×Array Nat) :
    (runTargets P f I e).events=P1ShortTargets.runTargets P f I e := by
  simp only [runTargets,collect_events,choiceTargets_value,
    BoundaryContexts.countedPrepareAt_correct,P1ShortTargets.runTargets]

theorem runTargets_cache [DecidableEq α] (P : SevenDFA α) (f : Nat→α)
    (I : BoundaryContexts.Index P) (e : Bounds×Array Nat) :
    (runTargets P f I e).cacheWork=
      e.1.period*(FullyCachedP2.stateSum P*e.1.period)+e.1.period^3 :=
  BoundaryContexts.countedPrepareAt_cost _ _ _ _ _ _

theorem runTargets_equality_reads [DecidableEq α] (P : SevenDFA α) (f : Nat→α)
    (I : BoundaryContexts.Index P) (e : Bounds×Array Nat) :
    (runTargets P f I e).equalityReads≤
      3*(P1PhaseFamily.targets e.1.period (e.1.hi-e.1.lo)).length := by
  apply collect_bound _ _ Result.equalityReads rfl (fun _ _=>rfl)
  intro z _
  exact (choiceTargets_reads _ _ _ _ _ _ _ _).1

theorem runTargets_tests [DecidableEq α] (P : SevenDFA α) (f : Nat→α)
    (I : BoundaryContexts.Index P) (e : Bounds×Array Nat) :
    (runTargets P f I e).exponentTests=
      3*(P1PhaseFamily.targets e.1.period (e.1.hi-e.1.lo)).length := by
  apply collect_constant _ _ Result.exponentTests rfl (fun _ _=>rfl)
  intro z _
  exact (choiceTargets_reads _ _ _ _ _ _ _ _).2.1

theorem runTargets_key_reads [DecidableEq α] (P : SevenDFA α) (f : Nat→α)
    (I : BoundaryContexts.Index P) (e : Bounds×Array Nat) :
    (runTargets P f I e).keyReads≤
      3*(P1PhaseFamily.targets e.1.period (e.1.hi-e.1.lo)).length := by
  apply collect_bound _ _ Result.keyReads rfl (fun _ _=>rfl)
  intro z _
  exact (choiceTargets_reads _ _ _ _ _ _ _ _).2.2

theorem runTargets_work [DecidableEq α] (P : SevenDFA α) (f : Nat→α) (w : Word α)
    (e : Bounds×Array Nat) (hlo : e.1.lo≤w.length) (hhi : e.1.hi≤w.length) :
    work (runTargets P f (BoundaryContexts.build P w).1 e)≤
      anchorWork P*(P1PhaseFamily.targets e.1.period (e.1.hi-e.1.lo)).length := by
  change work (collect _ _)≤_
  rw [BoundaryContexts.countedPrepareAt_correct]
  apply collect_bound _ _ work rfl join_work
  intro z _
  exact choiceTargets_work _ _ _ _ _ _ _ _
    (choiceTargets_covered_at P (shift f e.1.lo) _ _ _ _ w e.1.lo e.1.hi hlo hhi _)

def targets [DecidableEq α] (P : SevenDFA α) (f : Nat→α)
    (I : BoundaryContexts.Index P) (tables : List (Bounds×Array Nat)) : Result :=
  collect (runTargets P f I) tables

theorem targets_value [DecidableEq α] (P : SevenDFA α) (f : Nat→α)
    (I : BoundaryContexts.Index P) (tables : List (Bounds×Array Nat)) :
    (targets P f I tables).events=P1ShortTargets.targets P f I tables := by
  simp only [targets,collect_events,runTargets_value,P1ShortTargets.targets]

theorem table_collect_bound (step : (Bounds×Array Nat)→Result) (tables : List (Bounds×Array Nat))
    (cost : Result→Nat) (hzero : cost {}=0) (hadd : ∀ a b,cost (join a b)=cost a+cost b)
    (B : Nat) (h : ∀ e,e∈tables→cost (step e)≤
      B*(P1PhaseFamily.targets e.1.period (e.1.hi-e.1.lo)).length) :
    cost (collect step tables)≤B*(P1PhaseFamily.allTargets (tables.map Prod.fst)).length := by
  induction tables with
  | nil => simp only [collect,hzero,List.map_nil,P1PhaseFamily.allTargets,List.length_nil,Nat.mul_zero,Nat.le_refl]
  | cons e es ih =>
    rw [collect,hadd]
    simp only [List.map_cons,P1PhaseFamily.allTargets,List.length_append,List.length_map,Nat.mul_add]
    exact Nat.add_le_add (h e (by simp)) (ih (fun x hx=>h x (by simp [hx])))

theorem targets_equality_reads [DecidableEq α] (P : SevenDFA α) (f : Nat→α)
    (I : BoundaryContexts.Index P) (tables : List (Bounds×Array Nat)) :
    (targets P f I tables).equalityReads≤3*(P1PhaseFamily.allTargets (tables.map Prod.fst)).length :=
  table_collect_bound _ _ Result.equalityReads rfl (fun _ _=>rfl) 3
    (fun e _=>runTargets_equality_reads P f I e)

theorem targets_key_reads [DecidableEq α] (P : SevenDFA α) (f : Nat→α)
    (I : BoundaryContexts.Index P) (tables : List (Bounds×Array Nat)) :
    (targets P f I tables).keyReads≤3*(P1PhaseFamily.allTargets (tables.map Prod.fst)).length :=
  table_collect_bound _ _ Result.keyReads rfl (fun _ _=>rfl) 3
    (fun e _=>runTargets_key_reads P f I e)

theorem targets_work [DecidableEq α] (P : SevenDFA α) (f : Nat→α) (w : Word α)
    (tables : List (Bounds×Array Nat))
    (h : ∀ e,e∈tables→e.1.lo≤w.length ∧ e.1.hi≤w.length) :
    work (targets P f (BoundaryContexts.build P w).1 tables)≤
      anchorWork P*(P1PhaseFamily.allTargets (tables.map Prod.fst)).length :=
  table_collect_bound _ _ work rfl join_work (anchorWork P)
    (fun e he=>runTargets_work P f w e (h e he).1 (h e he).2)

theorem targets_cache [DecidableEq α] (P : SevenDFA α) (f : Nat→α)
    (I : BoundaryContexts.Index P) (tables : List (Bounds×Array Nat)) :
    (targets P f I tables).cacheWork=
      FullyCachedP2.stateSum P*RunBudget.phaseWork 1 (tables.map Prod.fst)+
        RunBudget.phaseWork 2 (tables.map Prod.fst) := by
  induction tables with
  | nil => simp [targets,collect,RunBudget.phaseWork]
  | cons e es ih =>
    change (runTargets P f I e).cacheWork+(targets P f I es).cacheWork=_
    rw [runTargets_cache,ih]
    have he : e.1.period*(FullyCachedP2.stateSum P*e.1.period)=
        FullyCachedP2.stateSum P*e.1.period^2 := by
      simp only [Nat.pow_succ,Nat.pow_zero,Nat.one_mul]
      ac_rfl
    rw [he]
    simp only [List.map_cons,RunBudget.phaseWork,Nat.mul_add,Nat.reduceAdd]
    omega

def generated {σ : Nat} (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat)
    (R : ExactKeys.Registry σ) : Result :=
  targets P f (BoundaryContexts.build P (segment f 0 n)).1
    (P1ShortKeys.buildRunTables R f (SmallPeriodRuns.cubic f n Q)).tables

theorem generated_value {σ : Nat} (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat)
    (R : ExactKeys.Registry σ) :
    (generated P f n Q R).events=P1ShortTargets.targets P f
      (BoundaryContexts.build P (segment f 0 n)).1
      (P1ShortKeys.buildRunTables R f (SmallPeriodRuns.cubic f n Q)).tables := targets_value _ _ _ _

theorem generated_work {σ : Nat} (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat)
    (R : ExactKeys.Registry σ) :
    work (generated P f n Q R)≤anchorWork P*3*Q^3*(2*n*DyadicIndex.heightFor n) := by
  have h := targets_work P f (segment f 0 n)
    (P1ShortKeys.buildRunTables R f (SmallPeriodRuns.cubic f n Q)).tables (by
      intro e he
      have hm : e.1∈SmallPeriodRuns.cubic f n Q := by
        rw [← P1ShortKeys.buildRunTables_runs R f (SmallPeriodRuns.cubic f n Q)]
        exact List.mem_map.mpr ⟨e,he,rfl⟩
      have hv := ((SmallPeriodRuns.cubic_mem f n Q e.1).mp hm).1
      rw [segment_length]
      have hlo := hv.1
      have hhi := hv.2.1
      exact ⟨by omega,hhi⟩)
  rw [P1ShortKeys.buildRunTables_runs] at h
  have hb := Nat.mul_le_mul_left (anchorWork P) (P1PhaseFamily.concrete_target_bound f n Q)
  simpa only [Nat.mul_assoc] using Nat.le_trans h hb

theorem generated_equality_reads {σ : Nat} (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat)
    (R : ExactKeys.Registry σ) :
    (generated P f n Q R).equalityReads≤9*Q^3*(2*n*DyadicIndex.heightFor n) := by
  have h := targets_equality_reads P f (BoundaryContexts.build P (segment f 0 n)).1
    (P1ShortKeys.buildRunTables R f (SmallPeriodRuns.cubic f n Q)).tables
  rw [P1ShortKeys.buildRunTables_runs] at h
  have hb := Nat.mul_le_mul_left 3 (P1PhaseFamily.concrete_target_bound f n Q)
  simpa only [← Nat.mul_assoc] using Nat.le_trans h hb

theorem generated_cache {σ : Nat} (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat)
    (R : ExactKeys.Registry σ) :
    (generated P f n Q R).cacheWork≤
      (FullyCachedP2.stateSum P*Q+Q^2)*(2*n*DyadicIndex.heightFor n) := by
  have hr := targets_cache P f (BoundaryContexts.build P (segment f 0 n)).1
    (P1ShortKeys.buildRunTables R f (SmallPeriodRuns.cubic f n Q)).tables
  rw [P1ShortKeys.buildRunTables_runs] at hr
  change (targets P f _ _).cacheWork≤_
  rw [hr,Nat.add_mul]
  have h1 := SmallPeriodRuns.cubic_phase_bound f n Q 1
  have h2 := SmallPeriodRuns.cubic_phase_bound f n Q 2
  have hfirst := Nat.mul_le_mul_left (FullyCachedP2.stateSum P) h1
  simpa only [Nat.pow_one,Nat.mul_assoc] using Nat.add_le_add hfirst h2

end REWB.CountedShortTargets
