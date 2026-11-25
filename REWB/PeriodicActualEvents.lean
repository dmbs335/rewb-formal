import REWB.PeriodicActualP2
import REWB.CountedShortTargets

/-! Concrete long-source P1 event construction with measured descriptors,
DNF assembly, projection, phase schedules, mapping and concatenation.
The run cache is prepared once for both source and target events.
The chronological event values are exactly the frozen `P1Events` values.
Cache transition and run/key discovery ledgers remain separately named;
this module does not replace their established operation models. -/
namespace REWB.PeriodicActual.Events
open REWB.Periodic REWB.RunGeometry REWB.PeriodicConstruction
variable {σ : Nat}

def source (P : SevenDFA (Fin σ)) (Q next : Nat) (R : Bounds) (ranks : Array Nat)
    (I : FullyCachedP2.Shared P) (v : Nat×Nat) : Result TimedJoin.TimedEntry :=
  let rho := P1SourceFamily.residue R.period v.1 v.2
  let F := Formula.source P (R.hi-R.lo) R.period v.1 v.2 rho I
  (⟨R.lo+v.1,⟨P1Events.code Q next R ranks v.2 rho,F.1⟩⟩,F.2+20)

theorem source_value (P : SevenDFA (Fin σ)) (Q next : Nat) (R : Bounds) (ranks : Array Nat)
    (I : FullyCachedP2.Shared P) (v : Nat×Nat) :
    (source P Q next R ranks I v).1=P1Events.source P Q next R ranks I v := by
  simp only [source,P1Events.source,Formula.source_value]

def sourceBudget (P : SevenDFA (Fin σ)) : Nat :=
  (Formula.sourceBudget P.A.stateCount).work+20

theorem source_work (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (Q next : Nat)
    (R : Bounds) (ranks : Array Nat) (I : BoundaryContexts.Index P) (v : Nat×Nat) :
    (source P Q next R ranks (BoundaryContexts.prepareAt P f R.period I R.lo R.hi) v).2
      ≤sourceBudget P := by
  have hh := (Formula.source_covers P (R.hi-R.lo) R.period v.1 v.2
    (P1SourceFamily.residue R.period v.1 v.2)
    (BoundaryContexts.prepareAt P f R.period I R.lo R.hi)).2
  exact Nat.add_le_add_right hh 20

def target (P : SevenDFA (Fin σ)) (Q next : Nat) (R : Bounds) (ranks : Array Nat)
    (I : FullyCachedP2.Shared P) (v : Nat×P1PhaseFamily.Three) : Result TimedJoin.TimedEntry :=
  let F := Formula.projectTarget P (R.hi-R.lo) R.period v.1 v.2.rho I
    (P1PhaseFamily.extend R.period v.1 v.2)
  (⟨R.lo+v.1,⟨P1Events.code Q next R ranks v.2.j v.2.rho,F.1⟩⟩,F.2+20)

theorem target_value (P : SevenDFA (Fin σ)) (Q next : Nat) (R : Bounds) (ranks : Array Nat)
    (I : FullyCachedP2.Shared P) (v : Nat×P1PhaseFamily.Three) :
    (target P Q next R ranks I v).1=P1Events.target P Q next R ranks I v := by
  simp only [target,P1Events.target,P1Events.targetWork,Formula.projectTarget_value]

def targetBudget (P : SevenDFA (Fin σ)) : Nat :=
  (Formula.targetBudget P P.H.stateCount).work+CountedCachedP1.targetSteps P+21

theorem target_work (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (Q next : Nat)
    (w : Word (Fin σ)) (R : Bounds) (ranks : Array Nat) (v : Nat×P1PhaseFamily.Three)
    (hlo : R.lo≤w.length) (hhi : R.hi≤w.length) :
    (target P Q next R ranks
      (BoundaryContexts.prepareAt P f R.period (BoundaryContexts.build P w).1 R.lo R.hi) v).2
      ≤targetBudget P := by
  have hc := CountedShortTargets.choiceTargets_covered_at P f (R.hi-R.lo) R.period
    v.1 v.2.rho w R.lo R.hi hlo hhi (P1PhaseFamily.extend R.period v.1 v.2)
  have hh := Formula.projectTarget_work P (R.hi-R.lo) R.period v.1 v.2.rho _ _ hc
  change (Formula.projectTarget P (R.hi-R.lo) R.period v.1 v.2.rho
    (BoundaryContexts.prepareAt P f R.period (BoundaryContexts.build P w).1 R.lo R.hi)
    (P1PhaseFamily.extend R.period v.1 v.2)).2 ≤
    (Formula.targetBudget P P.H.stateCount).work+CountedCachedP1.targetSteps P+1 at hh
  unfold target targetBudget
  dsimp only
  omega

structure Batch where
  sources : List TimedJoin.TimedEntry := []
  targets : List TimedJoin.TimedEntry := []
  work : Nat := 1

def run (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (I : BoundaryContexts.Index P)
    (Q next : Nat) (e : Bounds×Array Nat) : Batch :=
  let cache := BoundaryContexts.countedPrepareAt P (shift f e.1.lo) e.1.period I e.1.lo e.1.hi
  let sourceChoices := Choices.sources e.1.period (e.1.hi-e.1.lo)
  let targetChoices := Choices.targets e.1.period (e.1.hi-e.1.lo)
  let sources := CountedProjection.map (source P Q next e.1 e.2 cache.1) sourceChoices.1
  let targets := CountedProjection.map (target P Q next e.1 e.2 cache.1) targetChoices.1
  ⟨sources.1,targets.1,cache.2+sourceChoices.2+targetChoices.2+sources.2+targets.2+10⟩

theorem run_sources (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (I : BoundaryContexts.Index P)
    (Q next : Nat) (e : Bounds×Array Nat) :
    (run P f I Q next e).sources=(P1Events.run P f I Q next e).sources := by
  simp only [run,P1Events.run,CountedProjection.map_value,Choices.sources_value,source_value]

theorem run_targets (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (I : BoundaryContexts.Index P)
    (Q next : Nat) (e : Bounds×Array Nat) :
    (run P f I Q next e).targets=(P1Events.run P f I Q next e).targets := by
  simp only [run,P1Events.run,CountedProjection.map_value,Choices.targets_value,target_value,
    P1Events.target,List.map_map,Function.comp_def]

theorem run_work (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (w : Word (Fin σ))
    (Q next : Nat) (e : Bounds×Array Nat)
    (hq : 0<e.1.period) (hlo : e.1.lo≤w.length) (hhi : e.1.hi≤w.length) :
    (run P f (BoundaryContexts.build P w).1 Q next e).work≤
      (P1Events.run P f (BoundaryContexts.build P w).1 Q next e).cacheWork+
      (sourceBudget P+30)*((e.1.hi-e.1.lo+1)*e.1.period)+
      (targetBudget P+36)*((e.1.hi-e.1.lo+1)*e.1.period^3) := by
  let c := BoundaryContexts.countedPrepareAt P (shift f e.1.lo) e.1.period
    (BoundaryContexts.build P w).1 e.1.lo e.1.hi
  have hs := Choices.sources_work e.1.period (e.1.hi-e.1.lo) hq
  have ht := Choices.targets_work e.1.period (e.1.hi-e.1.lo) hq
  have hsm := PeriodicConstruction.map_bound (source P Q next e.1 e.2 c.1)
    (Choices.sources e.1.period (e.1.hi-e.1.lo)).1 (sourceBudget P)
    (fun v _ => source_work P (shift f e.1.lo) Q next e.1 e.2 _ v)
  have htm := PeriodicConstruction.map_bound (target P Q next e.1 e.2 c.1)
    (Choices.targets e.1.period (e.1.hi-e.1.lo)).1 (targetBudget P)
    (fun v _ => target_work P (shift f e.1.lo) Q next w e.1 e.2 v hlo hhi)
  rw [Choices.sources_value,P1SourceFamily.choices_length] at hsm
  rw [Choices.targets_value,P1PhaseFamily.targets_length] at htm
  have hpos : 1≤(e.1.hi-e.1.lo+1)*e.1.period := Nat.mul_pos (by omega) hq
  let S := (e.1.hi-e.1.lo+1)*e.1.period
  let T := (e.1.hi-e.1.lo+1)*e.1.period^3
  change _≤S*(sourceBudget P+1)+1 at hsm
  change _≤T*(targetBudget P+1)+1 at htm
  change c.2+_+_+_+_+10≤c.2+_+_
  change c.2+_+_+_+_+10≤c.2+(sourceBudget P+30)*S+(targetBudget P+36)*T
  rw [Choices.sources_value,Choices.targets_value]
  simp only [Nat.mul_add,Nat.mul_one] at hsm htm
  rw [Nat.mul_comm S (sourceBudget P)] at hsm
  rw [Nat.mul_comm T (targetBudget P)] at htm
  simp only [Nat.add_mul]
  dsimp only [c] at hsm htm
  omega

def runs (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (I : BoundaryContexts.Index P)
    (Q next : Nat) : List (Bounds×Array Nat) → Batch
  | [] => {}
  | e::es =>
    let this := run P f I Q next e
    let rest := runs P f I Q next es
    let sources := CountedProjection.append this.sources rest.sources
    let targets := CountedProjection.append this.targets rest.targets
    ⟨sources.1,targets.1,this.work+rest.work+sources.2+targets.2+6⟩

theorem runs_sources (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (I : BoundaryContexts.Index P)
    (Q next : Nat) (es : List (Bounds×Array Nat)) :
    (runs P f I Q next es).sources=(P1Events.runs P f I Q next es).sources := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [runs,P1Events.runs,CountedProjection.append_value,run_sources,ih]

theorem runs_targets (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (I : BoundaryContexts.Index P)
    (Q next : Nat) (es : List (Bounds×Array Nat)) :
    (runs P f I Q next es).targets=(P1Events.runs P f I Q next es).targets := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [runs,P1Events.runs,CountedProjection.append_value,run_targets,ih]

theorem runs_work (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (w : Word (Fin σ))
    (Q next : Nat) (es : List (Bounds×Array Nat))
    (hv : ∀e,e∈es → 0<e.1.period ∧ e.1.lo≤w.length ∧ e.1.hi≤w.length) :
    (runs P f (BoundaryContexts.build P w).1 Q next es).work≤
      (P1Events.runs P f (BoundaryContexts.build P w).1 Q next es).cacheWork+
      (sourceBudget P+39)*(P1Events.runs P f (BoundaryContexts.build P w).1 Q next es).sources.length+
      (targetBudget P+37)*(P1Events.runs P f (BoundaryContexts.build P w).1 Q next es).targets.length+1 := by
  induction es with
  | nil => simp [runs,P1Events.runs]
  | cons e es ih =>
    have he := hv e List.mem_cons_self
    have ht := ih (fun t hh => hv t (List.mem_cons_of_mem e hh))
    have hh := run_work P f w Q next e he.1 he.2.1 he.2.2
    have hs := P1Events.run_sizes P f (BoundaryContexts.build P w).1 Q next e
    have hpos : 1≤(P1Events.run P f (BoundaryContexts.build P w).1 Q next e).sources.length := by
      rw [hs.1]
      exact Nat.mul_pos (by omega) he.1
    rw [← hs.1,← hs.2] at hh
    simp only [runs,P1Events.runs,CountedProjection.append_steps,run_sources,run_targets,
      List.length_append,Nat.mul_add,Nat.add_mul]
    simp only [Nat.add_mul] at hh ht
    omega

end REWB.PeriodicActual.Events
