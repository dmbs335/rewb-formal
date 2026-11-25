import REWB.PeriodicActualChoices

/-! A value-preserving executable replacement of the external small-period
P2 branch. The new phase path counts the actual finite-orbit descriptors,
initial DNF construction, projection, eager decision and phase-list work.
Existing run discovery and cache preparation are executed once and retain
their existing comparison/transition counters; this file does not silently
reinterpret those selected counters as a bit-level machine cost. -/
namespace REWB.PeriodicActual.P2
open REWB.Periodic REWB.RunGeometry REWB.PeriodicConstruction
variable {α : Type}

def segment (f : Nat → α) (a : Nat) : Nat → Result (Word α)
  | 0 => ([],1)
  | k+1 =>
    let rest := segment f (a+1) k
    (f a::rest.1,rest.2+3)

theorem segment_value (f : Nat → α) (a n : Nat) :
    (segment f a n).1=Periodic.segment f a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp only [segment,Periodic.segment,ih]

theorem segment_work (f : Nat → α) (a n : Nat) :
    (segment f a n).2=3*n+1 := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp only [segment,ih]; omega

def phases (P : SevenDFA α) (n q : Nat) (I : FullyCachedP2.Shared P) :
    List P2Periodic.Five → Result Bool
  | [] => (false,1)
  | v::vs =>
    let this := Formula.solveP2 P n q I (P2Periodic.extend q v)
    let rest := phases P n q I vs
    (this.1 || rest.1,this.2+rest.2+16)

def phasesTR (P : SevenDFA α) (n q : Nat) (I : FullyCachedP2.Shared P)
    (vs : List P2Periodic.Five) : Result Bool :=
  vs.foldr (fun v rest =>
    let this := Formula.solveP2 P n q I (P2Periodic.extend q v)
    (this.1 || rest.1,this.2+rest.2+16)) (false,1)

@[csimp] theorem phases_eq_phasesTR : @phases=@phasesTR := by
  funext α P n q I vs
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [phases,phasesTR,List.foldr_cons] at ih ⊢
    rw [ih]

theorem phases_value (P : SevenDFA α) (n q : Nat) (I : FullyCachedP2.Shared P)
    (vs : List P2Periodic.Five) :
    (phases P n q I vs).1=(SmallPeriodP2.phases P n q I vs).accepted := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp only [phases,SmallPeriodP2.phases,Formula.solveP2_value,ih]

def phaseBudget (P : SevenDFA α) : Nat :=
  (Formula.p2Budget P P.A.stateCount P.H.stateCount).work+CountedProjection.p2Steps P+36

theorem solveAt_work [DecidableEq α] (P : SevenDFA α) (f : Nat → α)
    (n q : Nat) (w : Word α) (lo hi : Nat) (hlo : lo≤w.length) (hhi : hi≤w.length)
    (ph : P2Periodic.Layout Nat) :
    (Formula.solveP2 P n q
      (BoundaryContexts.prepareAt P f q (BoundaryContexts.build P w).1 lo hi) ph).2+16
      ≤phaseBudget P := by
  have hc : UniformProjection.Covered
      (FullyCachedP2.formula P q n
        (BoundaryContexts.prepareAt P f q (BoundaryContexts.build P w).1 lo hi)
        (P2Periodic.endpoints ph)) (UniformPhaseBounds.p2Family P) := by
    rw [BoundaryContexts.prepareAt_correct P f q w lo hi hlo hhi]
    exact CountedCachedP2.formula_covered P f q n (w.take lo) (w.drop hi) ph
  have hh := Formula.solveP2_work P n q _ ph hc
  change (Formula.solveP2 P n q
      (BoundaryContexts.prepareAt P f q (BoundaryContexts.build P w).1 lo hi) ph).2 ≤
    (Formula.p2Budget P P.A.stateCount P.H.stateCount).work+CountedProjection.p2Steps P+20 at hh
  unfold phaseBudget
  omega

theorem phases_work [DecidableEq α] (P : SevenDFA α) (f : Nat → α)
    (n q : Nat) (w : Word α) (lo hi : Nat) (hlo : lo≤w.length) (hhi : hi≤w.length)
    (vs : List P2Periodic.Five) :
    (phases P n q
      (BoundaryContexts.prepareAt P f q (BoundaryContexts.build P w).1 lo hi) vs).2
      ≤phaseBudget P*vs.length+1 := by
  induction vs with
  | nil => simp [phases]
  | cons v vs ih =>
    have hh := solveAt_work P f n q w lo hi hlo hhi (P2Periodic.extend q v)
    simp only [phases,List.length_cons,Nat.mul_add,Nat.mul_one]
    omega

def run [DecidableEq α] (P : SevenDFA α) (f : Nat → α)
    (I : BoundaryContexts.Index P) (R : Bounds) : Result Bool :=
  let cache := BoundaryContexts.countedPrepareAt P (shift f R.lo) R.period I R.lo R.hi
  let choices := Choices.p2 R.period
  let out := phases P (R.hi-R.lo) R.period cache.1 choices.1
  (out.1,cache.2+choices.2+out.2+10)

theorem run_value [DecidableEq α] (P : SevenDFA α) (f : Nat → α)
    (I : BoundaryContexts.Index P) (R : Bounds) :
    (run P f I R).1=(SmallPeriodP2.run P f I R).accepted := by
  simp only [run,SmallPeriodP2.run,Choices.p2_value,phases_value]

theorem run_work [DecidableEq α] (P : SevenDFA α) (f : Nat → α) (w : Word α)
    (R : Bounds) (hq : 0<R.period) (hlo : R.lo≤w.length) (hhi : R.hi≤w.length) :
    (run P f (BoundaryContexts.build P w).1 R).2 ≤
      (SmallPeriodP2.run P f (BoundaryContexts.build P w).1 R).cacheWork+
      (phaseBudget P+50)*R.period^5 := by
  have hc := (Choices.p2_sized R.period hq).2
  have hp := phases_work P (shift f R.lo) (R.hi-R.lo) R.period w R.lo R.hi hlo hhi
    (Choices.p2 R.period).1
  rw [Choices.p2_value,P2Periodic.choices_length] at hp
  have hpos : 1≤R.period^5 := Nat.pow_pos hq
  unfold run SmallPeriodP2.run
  dsimp only
  rw [BoundaryContexts.countedPrepareAt_correct,Choices.p2_value]
  simp only [Nat.add_mul] at *
  omega

def runs [DecidableEq α] (P : SevenDFA α) (f : Nat → α)
    (I : BoundaryContexts.Index P) : List Bounds → Result Bool
  | [] => (false,1)
  | R::Rs =>
    let this := run P f I R
    let rest := runs P f I Rs
    (this.1 || rest.1,this.2+rest.2+2)

def runsTR [DecidableEq α] (P : SevenDFA α) (f : Nat → α)
    (I : BoundaryContexts.Index P) (Rs : List Bounds) : Result Bool :=
  Rs.foldr (fun R rest =>
    let this := run P f I R
    (this.1 || rest.1,this.2+rest.2+2)) (false,1)

@[csimp] theorem runs_eq_runsTR : @runs=@runsTR := by
  funext α inst P f I Rs
  induction Rs with
  | nil => rfl
  | cons R Rs ih =>
    simp only [runs,runsTR,List.foldr_cons] at ih ⊢
    rw [ih]

theorem runs_value [DecidableEq α] (P : SevenDFA α) (f : Nat → α)
    (I : BoundaryContexts.Index P) (Rs : List Bounds) :
    (runs P f I Rs).1=(SmallPeriodP2.runs P f I Rs).accepted := by
  induction Rs with
  | nil => rfl
  | cons R Rs ih => simp only [runs,SmallPeriodP2.runs,run_value,ih]

theorem runs_work [DecidableEq α] (P : SevenDFA α) (f : Nat → α) (w : Word α)
    (Rs : List Bounds)
    (hv : ∀R,R∈Rs → 0<R.period ∧ R.lo≤w.length ∧ R.hi≤w.length) :
    (runs P f (BoundaryContexts.build P w).1 Rs).2≤
      (SmallPeriodP2.runs P f (BoundaryContexts.build P w).1 Rs).cacheWork+
      (phaseBudget P+52)*RunBudget.phaseWork 4 Rs+1 := by
  induction Rs with
  | nil => simp [runs,SmallPeriodP2.runs,RunBudget.phaseWork]
  | cons R Rs ih =>
    have hr := hv R List.mem_cons_self
    have ht := ih (fun r hh => hv r (List.mem_cons_of_mem R hh))
    have hh := run_work P f w R hr.1 hr.2.1 hr.2.2
    have hp : 1≤R.period^5 := Nat.pow_pos hr.1
    simp only [runs,SmallPeriodP2.runs,RunBudget.phaseWork,Nat.mul_add,Nat.add_mul]
    simp only [show 4+1=5 from rfl]
    simp only [Nat.add_mul] at hh ht
    omega

def solve [DecidableEq α] (P : SevenDFA α) (f : Nat → α) (n Q : Nat) : Result Bool :=
  let text := segment f 0 n
  let contexts := BoundaryContexts.build P text.1
  let enumerated := SmallPeriodRuns.enumerate f n Q
  let cubic := Orbit.filter (fun R : Bounds => (decide (3*R.period≤R.hi-R.lo),3)) enumerated.1
  let out := runs P f contexts.1 cubic.1
  (out.1,text.2+contexts.2+enumerated.2+cubic.2+out.2+8)

theorem solve_value [DecidableEq α] (P : SevenDFA α) (f : Nat → α) (n Q : Nat) :
    (solve P f n Q).1=(SmallPeriodP2.solve P f n Q).accepted := by
  simp only [solve,segment_value,Orbit.filter_value,runs_value,SmallPeriodP2.solve]

theorem length_le_mass (Rs : List Bounds) : Rs.length≤RunBudget.totalMass Rs := by
  induction Rs with
  | nil => exact Nat.le_refl _
  | cons R Rs ih =>
    simp only [List.length_cons,RunBudget.totalMass,RunBudget.mass]
    omega

theorem solve_work [DecidableEq α] (P : SevenDFA α) (f : Nat → α) (n Q : Nat) :
    (solve P f n Q).2≤
      (SmallPeriodP2.solve P f n Q).runComparisons+
      (SmallPeriodP2.solve P f n Q).contextEntries+
      (SmallPeriodP2.solve P f n Q).cacheWork+
      (phaseBudget P+52)*(SmallPeriodP2.solve P f n Q).phaseCalls+
      5*(2*n*DyadicIndex.heightFor n)+3*n+11 := by
  have hv : ∀R,R∈SmallPeriodRuns.cubic f n Q →
      0<R.period ∧ R.lo≤(Periodic.segment f 0 n).length ∧ R.hi≤(Periodic.segment f 0 n).length := by
    intro R hR
    have hh := ((SmallPeriodRuns.cubic_mem f n Q R).mp hR).1
    rw [Periodic.segment_length]
    have hlo := hh.1
    have hhi := hh.2.1
    exact ⟨hh.2.2.2.1.1,by omega,hhi⟩
  have hr := runs_work P f (Periodic.segment f 0 n) (SmallPeriodRuns.cubic f n Q) hv
  have hc := (SmallPeriodP2.runs_counts P f (BoundaryContexts.build P (Periodic.segment f 0 n)).1
    (SmallPeriodRuns.cubic f n Q)).2.1
  have hf := Orbit.filter_work
    (fun R : Bounds => (decide (3*R.period≤R.hi-R.lo),3))
    (SmallPeriodRuns.enumerate f n Q).1 3 (fun _ _ => Nat.le_refl _)
  have hl := Nat.le_trans (length_le_mass (SmallPeriodRuns.enumerate f n Q).1)
    (SmallPeriodRuns.enumerate_mass f n Q)
  have hf' := Nat.le_trans hf (Nat.add_le_add_right (Nat.mul_le_mul_right 5 hl) 1)
  rw [← hc] at hr
  unfold solve SmallPeriodP2.solve
  dsimp only
  rw [segment_value,segment_work,Orbit.filter_value]
  dsimp only
  dsimp only [SmallPeriodRuns.cubic] at hr
  omega

end REWB.PeriodicActual.P2
