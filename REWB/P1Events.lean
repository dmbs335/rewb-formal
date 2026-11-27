import REWB.ExactKeys
import REWB.CachedP1
import REWB.P1SourceFamily
import REWB.CountedCachedP1

/-! Concrete P1 event generation. Each generated run is prepared once;
    all events read its phase-rank array and cached DFA/equality tables.
    The semantic event functions below are specifications, not executable
    calls made by the generator. Long-source coverage and short-source
    dispatch are stated separately in the global completeness theorem. -/
namespace REWB.P1Events
open REWB.Periodic REWB.RunGeometry REWB.AffineProjection
open REWB.UniformPhaseBounds REWB.UniformProjection
variable {σ : Nat}

def code (Q next : Nat) (R : Bounds) (ranks : Array Nat) (phase rho : Nat) : Nat :=
  ExactKeys.keyCode Q next ⟨R.period,ranks[phase]?.getD 0,rho⟩

theorem code_exact (f : Nat→Fin σ) (Rs : List Bounds) (Q : Nat)
    (e t : Bounds×Array Nat)
    (he : e∈(ExactKeys.buildRunTables ExactKeys.initial f Rs).tables)
    (ht : t∈(ExactKeys.buildRunTables ExactKeys.initial f Rs).tables)
    (heq : e.1.period≤Q) (htq : t.1.period≤Q)
    (a b r s : Nat) (ha : a<e.1.period) (hb : b<t.1.period)
    (hr : r<e.1.period) (hs : s<t.1.period) :
    code Q (ExactKeys.buildRunTables ExactKeys.initial f Rs).registry.next e.1 e.2 a r=
      code Q (ExactKeys.buildRunTables ExactKeys.initial f Rs).registry.next t.1 t.2 b s ↔
      e.1.period=t.1.period ∧ r=s ∧
      segment (shift f e.1.lo) a e.1.period=segment (shift f t.1.lo) b t.1.period := by
  obtain ⟨x,hx,hxb,hxl,hxp,hxr⟩ := ExactKeys.buildRunTables_key _ ExactKeys.initial_valid
    f Rs Q e he heq a r ha hr
  obtain ⟨y,hy,hyb,hyl,hyp,hyr⟩ := ExactKeys.buildRunTables_key _ ExactKeys.initial_valid
    f Rs Q t ht htq b s hb hs
  have hxe : x=⟨e.1.period,e.2[a]?.getD 0,r⟩ := by
    unfold ExactKeys.tableKey at hx
    cases hg : e.2[a]? with
    | none => simp [hg] at hx
    | some z => simpa only [hg,Option.map,Option.some.injEq,Option.getD] using hx.symm
  have hye : y=⟨t.1.period,t.2[b]?.getD 0,s⟩ := by
    unfold ExactKeys.tableKey at hy
    cases hg : t.2[b]? with
    | none => simp [hg] at hy
    | some z => simpa only [hg,Option.map,Option.some.injEq,Option.getD] using hy.symm
  have h := ExactKeys.keyCode_exact _ (ExactKeys.buildRunTables_valid _ ExactKeys.initial_valid f Rs)
    Q _ _ x y hxb hyb hxl hyl
  rw [hxp,hyp,hxr,hyr] at h
  simpa only [hxe,hye,code] using h

def source (P : SevenDFA (Fin σ)) (Q next : Nat) (R : Bounds) (ranks : Array Nat)
    (I : FullyCachedP2.Shared P) (v : Nat×Nat) : TimedJoin.TimedEntry :=
  let rho := P1SourceFamily.residue R.period v.1 v.2
  ⟨R.lo+v.1,⟨code Q next R ranks v.2 rho,
    CachedP1.source P (R.hi-R.lo) R.period v.1 v.2 rho I⟩⟩

def targetWork (P : SevenDFA (Fin σ)) (Q next : Nat) (R : Bounds) (ranks : Array Nat)
    (I : FullyCachedP2.Shared P) (v : Nat×P1PhaseFamily.Three) : TimedJoin.TimedEntry×Nat×Nat :=
  let r := CountedCachedP1.project P (R.hi-R.lo) R.period v.1 v.2.rho I
    (P1PhaseFamily.extend R.period v.1 v.2)
  (⟨R.lo+v.1,⟨code Q next R ranks v.2.j v.2.rho,r.formula⟩⟩,r.equalityReads,r.projectionSteps)

def target (P : SevenDFA (Fin σ)) (Q next : Nat) (R : Bounds) (ranks : Array Nat)
    (I : FullyCachedP2.Shared P) (v : Nat×P1PhaseFamily.Three) : TimedJoin.TimedEntry :=
  (targetWork P Q next R ranks I v).1

def sourceSpec (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (Q next : Nat)
    (R : Bounds) (ranks : Array Nat) (v : Nat×Nat) : TimedJoin.TimedEntry :=
  ⟨R.lo+v.1,⟨code Q next R ranks v.2 (P1SourceFamily.residue R.period v.1 v.2),
    P1SourceFamily.formula P f R v.1 v.2⟩⟩

def targetSpec (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q next : Nat)
    (R : Bounds) (ranks : Array Nat) (v : Nat×P1PhaseFamily.Three) : TimedJoin.TimedEntry :=
  ⟨R.lo+v.1,⟨code Q next R ranks v.2.j v.2.rho,
    P1Target.projection P (shift f R.lo) (R.hi-R.lo) R.period v.1 v.2.rho
      (segment f R.hi (n-R.hi)) (P1PhaseFamily.extend R.period v.1 v.2)⟩⟩

theorem source_correct (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q next : Nat)
    (R : Bounds) (ranks : Array Nat) (v : Nat×Nat) (hlo : R.lo≤n) (hhi : R.hi≤n) :
    source P Q next R ranks
      (BoundaryContexts.prepareAt P (shift f R.lo) R.period
        (BoundaryContexts.build P (segment f 0 n)).1 R.lo R.hi) v=
      sourceSpec P f Q next R ranks v := by
  have h := CachedP1.sourceAt_eq P (shift f R.lo) (R.hi-R.lo) R.period v.1 v.2
    (P1SourceFamily.residue R.period v.1 v.2) (segment f 0 n) R.lo R.hi
    (by simpa only [segment_length] using hlo) (by simpa only [segment_length] using hhi)
  rw [SmallPeriodP2.segment_take f 0 n R.lo hlo] at h
  exact congrArg (fun F=>TimedJoin.TimedEntry.mk (R.lo+v.1)
    ⟨code Q next R ranks v.2 (P1SourceFamily.residue R.period v.1 v.2),F⟩) h

theorem target_correct (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q next : Nat)
    (R : Bounds) (ranks : Array Nat) (v : Nat×P1PhaseFamily.Three)
    (hlo : R.lo≤n) (hhi : R.hi≤n) :
    target P Q next R ranks
      (BoundaryContexts.prepareAt P (shift f R.lo) R.period
        (BoundaryContexts.build P (segment f 0 n)).1 R.lo R.hi) v=
      targetSpec P f n Q next R ranks v := by
  have h := CountedCachedP1.project_eq_at P (shift f R.lo) (R.hi-R.lo) R.period v.1 v.2.rho
    (segment f 0 n) R.lo R.hi
    (by simpa only [segment_length] using hlo) (by simpa only [segment_length] using hhi)
    (P1PhaseFamily.extend R.period v.1 v.2)
  rw [SmallPeriodP2.segment_drop f 0 n R.hi hhi] at h
  simp only [Nat.zero_add] at h
  exact congrArg (fun F=>TimedJoin.TimedEntry.mk (R.lo+v.1)
    ⟨code Q next R ranks v.2.j v.2.rho,F⟩) h

structure Batch where
  sources : List TimedJoin.TimedEntry := []
  targets : List TimedJoin.TimedEntry := []
  cacheWork : Nat := 0
  equalityReads : Nat := 0
  projectionSteps : Nat := 0

def run (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (I : BoundaryContexts.Index P)
    (Q next : Nat) (e : Bounds×Array Nat) : Batch :=
  let c := BoundaryContexts.countedPrepareAt P (shift f e.1.lo) e.1.period I e.1.lo e.1.hi
  let ts := (P1PhaseFamily.targets e.1.period (e.1.hi-e.1.lo)).map (targetWork P Q next e.1 e.2 c.1)
  ⟨(P1SourceFamily.choices e.1.period (e.1.hi-e.1.lo)).map (source P Q next e.1 e.2 c.1),
    ts.map Prod.fst,c.2,(ts.map (fun x=>x.2.1)).sum,(ts.map (fun x=>x.2.2)).sum⟩

def runs (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (I : BoundaryContexts.Index P)
    (Q next : Nat) : List (Bounds×Array Nat)→Batch
  | [] => {}
  | e::es =>
    let a := run P f I Q next e
    let b := runs P f I Q next es
    ⟨a.sources++b.sources,a.targets++b.targets,a.cacheWork+b.cacheWork,
      a.equalityReads+b.equalityReads,a.projectionSteps+b.projectionSteps⟩

theorem run_sizes (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (I : BoundaryContexts.Index P)
    (Q next : Nat) (e : Bounds×Array Nat) :
    (run P f I Q next e).sources.length=(e.1.hi-e.1.lo+1)*e.1.period ∧
    (run P f I Q next e).targets.length=(e.1.hi-e.1.lo+1)*e.1.period^3 := by
  simp only [run,List.length_map,P1SourceFamily.choices_length,P1PhaseFamily.targets_length,and_self]

theorem runs_sizes (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (I : BoundaryContexts.Index P)
    (Q next : Nat) (es : List (Bounds×Array Nat)) :
    (runs P f I Q next es).sources.length=(P1SourceFamily.allSources (es.map Prod.fst)).length ∧
    (runs P f I Q next es).targets.length=(P1PhaseFamily.allTargets (es.map Prod.fst)).length := by
  induction es with
  | nil => exact ⟨rfl,rfl⟩
  | cons e es ih =>
    have h := run_sizes P f I Q next e
    simp only [runs,List.length_append,List.map_cons,P1SourceFamily.allSources,
      P1PhaseFamily.allTargets,List.length_map,P1SourceFamily.choices_length,
      P1PhaseFamily.targets_length,h.1,h.2,ih.1,ih.2,and_self]

theorem runs_cache (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (I : BoundaryContexts.Index P)
    (Q next : Nat) (es : List (Bounds×Array Nat)) :
    (runs P f I Q next es).cacheWork=
      FullyCachedP2.stateSum P*RunBudget.phaseWork 1 (es.map Prod.fst)+
      RunBudget.phaseWork 2 (es.map Prod.fst) := by
  induction es with
  | nil => simp [runs,RunBudget.phaseWork]
  | cons e es ih =>
    change (BoundaryContexts.countedPrepareAt P _ _ I _ _).2+
      (runs P f I Q next es).cacheWork=_
    rw [BoundaryContexts.countedPrepareAt_cost,ih]
    simp only [List.map_cons,RunBudget.phaseWork,Nat.mul_add]
    simp only [Nat.pow_succ,Nat.pow_zero,Nat.one_mul]
    ac_rfl

theorem sources_mem (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q next : Nat)
    (es : List (Bounds×Array Nat))
    (hv : ∀ e,e∈es→e.1.lo≤n ∧ e.1.hi≤n) (x : TimedJoin.TimedEntry) :
    x∈(runs P f (BoundaryContexts.build P (segment f 0 n)).1 Q next es).sources ↔
      ∃ e,e∈es ∧ ∃ v,v∈P1SourceFamily.choices e.1.period (e.1.hi-e.1.lo) ∧
        sourceSpec P f Q next e.1 e.2 v=x := by
  induction es with
  | nil => simp [runs]
  | cons e es ih =>
    have he := hv e (by simp)
    have ht := ih (fun z hz=>hv z (by simp [hz]))
    simp only [runs,List.mem_append,run,List.map_map,List.mem_map,BoundaryContexts.countedPrepareAt_correct]
    rw [ht]
    constructor
    · rintro (⟨v,hv,heq⟩|⟨z,hz,v,hv,heq⟩)
      · exact ⟨e,by simp,v,hv,by rw [← source_correct P f n Q next e.1 e.2 v he.1 he.2]; exact heq⟩
      · exact ⟨z,by simp [hz],v,hv,heq⟩
    · rintro ⟨z,hz,v,hmem,heq⟩
      rcases List.mem_cons.mp hz with hsame|hz
      · subst z
        exact Or.inl ⟨v,hmem,by rw [source_correct P f n Q next e.1 e.2 v he.1 he.2]; exact heq⟩
      · exact Or.inr ⟨z,hz,v,hmem,heq⟩

theorem targets_mem (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q next : Nat)
    (es : List (Bounds×Array Nat))
    (hv : ∀ e,e∈es→e.1.lo≤n ∧ e.1.hi≤n) (x : TimedJoin.TimedEntry) :
    x∈(runs P f (BoundaryContexts.build P (segment f 0 n)).1 Q next es).targets ↔
      ∃ e,e∈es ∧ ∃ v,v∈P1PhaseFamily.targets e.1.period (e.1.hi-e.1.lo) ∧
        targetSpec P f n Q next e.1 e.2 v=x := by
  induction es with
  | nil => simp [runs]
  | cons e es ih =>
    have he := hv e (by simp)
    have ht := ih (fun z hz=>hv z (by simp [hz]))
    simp only [runs,List.mem_append,run,List.map_map,List.mem_map,BoundaryContexts.countedPrepareAt_correct]
    rw [ht]
    constructor
    · rintro (⟨v,hv,heq⟩|⟨z,hz,v,hv,heq⟩)
      · exact ⟨e,by simp,v,hv,by rw [← target_correct P f n Q next e.1 e.2 v he.1 he.2]; exact heq⟩
      · exact ⟨z,by simp [hz],v,hv,heq⟩
    · rintro ⟨z,hz,v,hmem,heq⟩
      rcases List.mem_cons.mp hz with hsame|hz
      · subst z
        exact Or.inl ⟨v,hmem,(target_correct P f n Q next e.1 e.2 v he.1 he.2).trans heq⟩
      · exact Or.inr ⟨z,hz,v,hmem,heq⟩

def generated (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) : Batch :=
  let I := BoundaryContexts.build P (segment f 0 n)
  let R := SmallPeriodRuns.cubic f n Q
  let K := ExactKeys.buildRunTables ExactKeys.initial f R
  runs P f I.1 Q K.registry.next K.tables

theorem generated_sizes (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (generated P f n Q).sources.length≤3*Q*(2*n*DyadicIndex.heightFor n) ∧
    (generated P f n Q).targets.length≤3*Q^3*(2*n*DyadicIndex.heightFor n) := by
  have h := runs_sizes P f (BoundaryContexts.build P (segment f 0 n)).1 Q
    (ExactKeys.buildRunTables ExactKeys.initial f (SmallPeriodRuns.cubic f n Q)).registry.next
    (ExactKeys.buildRunTables ExactKeys.initial f (SmallPeriodRuns.cubic f n Q)).tables
  rw [ExactKeys.buildRunTables_runs] at h
  unfold generated
  dsimp only
  rw [h.1,h.2]
  exact ⟨P1SourceFamily.concrete_source_bound f n Q,P1PhaseFamily.concrete_target_bound f n Q⟩

theorem source_choice_bounds (q n : Nat) (v : Nat×Nat)
    (h : v∈P1SourceFamily.choices q n) : v.1≤n ∧ v.2<q := by
  obtain ⟨a,ha,hm⟩ := List.mem_flatMap.mp h
  obtain ⟨p,hp,he⟩ := List.mem_map.mp hm
  cases he
  exact ⟨by have h := List.mem_range.mp ha; omega,List.mem_range.mp hp⟩

theorem target_choice_bounds (q n : Nat) (v : Nat×P1PhaseFamily.Three)
    (h : v∈P1PhaseFamily.targets q n) :
    v.1≤n ∧ v.2.j<q ∧ v.2.e<q ∧ v.2.rho<q := by
  obtain ⟨p,hp,hm⟩ := List.mem_flatMap.mp h
  obtain ⟨u,hu,huv⟩ := List.mem_map.mp hm
  obtain ⟨j,hj,hmj⟩ := List.mem_flatMap.mp hu
  obtain ⟨e,he,hme⟩ := List.mem_flatMap.mp hmj
  obtain ⟨r,hr,hru⟩ := List.mem_map.mp hme
  cases hru
  cases huv
  exact ⟨by have hh := List.mem_range.mp hp; omega,
    List.mem_range.mp hj,List.mem_range.mp he,List.mem_range.mp hr⟩

theorem residue_lt (q a phase : Nat) (hq : 0<q) (hp : phase<q) :
    P1SourceFamily.residue q a phase<q := by
  have ha := Nat.mod_lt a hq
  unfold P1SourceFamily.residue PhaseSolver.tailLen residual PhaseSolver.phaseCoord
    P1Source.start P2Periodic.endEndpoint
  dsimp only [PhaseSolver.Endpoint.phase]
  split <;> omega

theorem table_valid (f : Nat→Fin σ) (n Q : Nat) (e : Bounds×Array Nat)
    (he : e∈(ExactKeys.buildRunTables ExactKeys.initial f (SmallPeriodRuns.cubic f n Q)).tables) :
    e.1.Valid f n ∧ e.1.period≤Q ∧ 3*e.1.period≤e.1.hi-e.1.lo := by
  have hm : e.1∈(ExactKeys.buildRunTables ExactKeys.initial f (SmallPeriodRuns.cubic f n Q)).tables.map Prod.fst :=
    List.mem_map.mpr ⟨e,he,rfl⟩
  rw [ExactKeys.buildRunTables_runs] at hm
  exact (SmallPeriodRuns.cubic_mem f n Q e.1).mp hm

theorem table_boundaries (f : Nat→Fin σ) (n Q : Nat) (e : Bounds×Array Nat)
    (he : e∈(ExactKeys.buildRunTables ExactKeys.initial f (SmallPeriodRuns.cubic f n Q)).tables) :
    e.1.lo≤n ∧ e.1.hi≤n := by
  have h := (table_valid f n Q e he).1
  exact ⟨by have h1 := h.1; have h2 := h.2.1; omega,h.2.1⟩

theorem sourceSpec_good (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q next : Nat)
    (R : Bounds) (ranks : Array Nat) (v : Nat×Nat) (hR : R.Valid f n) :
    ExponentIntervals.Compatible (p1Modulus P) (sourceSpec P f Q next R ranks v).entry.formula := by
  apply compatible_multiple _ _ _
    (projection_compatible 0 _ _
      (UniformJoin.localSource_covered P (shift f R.lo) (R.hi-R.lo) R.period v.1 v.2
        (P1SourceFamily.residue R.period v.1 v.2) (segment f 0 R.lo))
      (UniformJoin.localSource_good P _ _ _ _ _ _ _ hR.2.2.2.1.2.1))
    (Nat.dvd_mul_right _ _)

theorem targetSpec_good (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q next : Nat)
    (R : Bounds) (ranks : Array Nat) (v : Nat×P1PhaseFamily.Three) (hR : R.Valid f n) :
    ExponentIntervals.Compatible (p1Modulus P) (targetSpec P f n Q next R ranks v).entry.formula :=
  p1_target_compatible P (shift f R.lo) (R.hi-R.lo) R.period v.1 v.2.rho
    (segment f R.hi (n-R.hi)) (P1PhaseFamily.extend R.period v.1 v.2) hR.2.2.2.1

theorem generated_good (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    TimedJoin.Good (p1Modulus P) (generated P f n Q).sources ∧
    TimedJoin.Good (p1Modulus P) (generated P f n Q).targets := by
  constructor
  · intro x hx
    obtain ⟨e,he,v,hv,rfl⟩ := (sources_mem P f n Q _ _ (table_boundaries f n Q) x).mp hx
    exact sourceSpec_good P f n Q _ e.1 e.2 v (table_valid f n Q e he).1
  · intro x hx
    obtain ⟨e,he,v,hv,rfl⟩ := (targets_mem P f n Q _ _ (table_boundaries f n Q) x).mp hx
    exact targetSpec_good P f n Q _ e.1 e.2 v (table_valid f n Q e he).1

theorem generated_positions (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (∀ x,x∈(generated P f n Q).sources→x.pos≤n) ∧
    (∀ y,y∈(generated P f n Q).targets→y.pos≤n) := by
  constructor
  · intro x hx
    obtain ⟨e,he,v,hv,rfl⟩ := (sources_mem P f n Q _ _ (table_boundaries f n Q) x).mp hx
    have hb := source_choice_bounds _ _ _ hv
    have h := (table_valid f n Q e he).1
    change e.1.lo+v.1≤n
    have h1 := h.1
    have h2 := h.2.1
    omega
  · intro x hx
    obtain ⟨e,he,v,hv,rfl⟩ := (targets_mem P f n Q _ _ (table_boundaries f n Q) x).mp hx
    have hb := target_choice_bounds _ _ _ hv
    have h := (table_valid f n Q e he).1
    change e.1.lo+v.1≤n
    have h1 := h.1
    have h2 := h.2.1
    omega

def solve (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) : OfflineJoin.Result :=
  let b := generated P f n Q
  OfflineJoin.run P.C (p1Modulus P) n (segment f 0 n) b.sources b.targets

theorem solve_correct (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (solve P f n Q).answer=true ↔ TimedJoin.Match P.C (segment f 0 n) n
      (generated P f n Q).sources (generated P f n Q).targets := by
  have hg := generated_good P f n Q
  have hp := generated_positions P f n Q
  exact OfflineJoin.run_correct P.C (p1Modulus P) n (segment f 0 n) _ _ (p1Modulus_pos P)
    hg.1 hg.2 (by simpa only [segment_length] using hp.1) (by simpa only [segment_length] using hp.2)

end REWB.P1Events
