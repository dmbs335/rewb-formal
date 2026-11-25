import REWB.P1ShortKeys
import REWB.P1ShortSources

/-! Cached target events for short P1 inner copies. Each anchored phase
    computes its projected formula once, tests the three exponents
    m = 0, 1, 2, and emits a constant-formula chronological event for
    every successful test. Its full-word rank is one direct array read.

    One periodic cache is prepared per run. Event generation performs
    no full-word key construction and no exterior-context scan. -/
namespace REWB.P1ShortTargets
open REWB.Periodic REWB.RunGeometry REWB.AffineProjection
open REWB.P1ShortSources (trueEntry)
variable {α : Type}

def choiceTargets (P : SevenDFA α) (n q lo p : Nat) (v : P1PhaseFamily.Three)
    (I : FullyCachedP2.Shared P) (ranks : Array Nat) : List TimedJoin.TimedEntry :=
  let F := (CachedP1.countedProjection P n q p v.rho I (P1PhaseFamily.extend q p v)).1
  ((List.range 3).filter (fun m : Nat=>decideFormula F [(m:Int)])).map fun m=>
    trueEntry (lo+p) (ranks[P1ShortKeys.index q v.j v.rho m]?.getD 0)

theorem choiceTargets_mem (P : SevenDFA α) (n q lo p : Nat)
    (v : P1PhaseFamily.Three) (I : FullyCachedP2.Shared P) (ranks : Array Nat)
    (e : TimedJoin.TimedEntry) :
    e∈choiceTargets P n q lo p v I ranks ↔ ∃ m : Nat,m<3 ∧
      decideFormula (CachedP1.projection P n q p v.rho I (P1PhaseFamily.extend q p v))
        [(m:Int)]=true ∧
      trueEntry (lo+p) (ranks[P1ShortKeys.index q v.j v.rho m]?.getD 0)=e := by
  simp only [choiceTargets,CachedP1.countedProjection_correct,List.mem_map,List.mem_filter,List.mem_range]
  constructor
  · rintro ⟨m,⟨hm,hyes⟩,he⟩
    exact ⟨m,hm,hyes,he⟩
  · rintro ⟨m,hm,hyes,he⟩
    exact ⟨m,⟨hm,hyes⟩,he⟩

theorem choiceTargets_bound (P : SevenDFA α) (n q lo p : Nat)
    (v : P1PhaseFamily.Three) (I : FullyCachedP2.Shared P) (ranks : Array Nat) :
    (choiceTargets P n q lo p v I ranks).length≤3 := by
  unfold choiceTargets
  rw [List.length_map,CachedP1.countedProjection_correct]
  have h := List.length_filter_le
    (fun m : Nat=>decideFormula (CachedP1.projection P n q p v.rho I
      (P1PhaseFamily.extend q p v)) [(m:Int)]) (List.range 3)
  simpa only [List.length_range] using h

theorem choices_bounds (q : Nat) (v : P1PhaseFamily.Three)
    (hv : v∈P1PhaseFamily.choices q) : v.j<q ∧ v.e<q ∧ v.rho<q := by
  obtain ⟨j,hj,hafterj⟩ := List.mem_flatMap.mp hv
  obtain ⟨e,he,haftere⟩ := List.mem_flatMap.mp hafterj
  obtain ⟨rho,hr,hveq⟩ := List.mem_map.mp haftere
  subst v
  exact ⟨List.mem_range.mp hj,List.mem_range.mp he,List.mem_range.mp hr⟩

theorem phaseTargets_mem (q n p : Nat) (v : P1PhaseFamily.Three) :
    (p,v)∈P1PhaseFamily.targets q n ↔ p≤n ∧ v∈P1PhaseFamily.choices q := by
  constructor
  · intro h
    obtain ⟨a,ha,hv⟩ := List.mem_flatMap.mp h
    obtain ⟨z,hz,he⟩ := List.mem_map.mp hv
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
    exact ⟨by have hh := List.mem_range.mp ha; omega,hz⟩
  · rintro ⟨hp,hv⟩
    exact List.mem_flatMap.mpr ⟨p,List.mem_range.mpr (by omega),
      List.mem_map.mpr ⟨v,hv,rfl⟩⟩

def runTargets [DecidableEq α] (P : SevenDFA α) (f : Nat→α)
    (I : BoundaryContexts.Index P) (e : Bounds×Array Nat) : List TimedJoin.TimedEntry :=
  let R := e.1
  let cached := BoundaryContexts.prepareAt P (shift f R.lo) R.period I R.lo R.hi
  (P1PhaseFamily.targets R.period (R.hi-R.lo)).flatMap fun z=>
    choiceTargets P (R.hi-R.lo) R.period R.lo z.1 z.2 cached e.2

theorem runTargets_mem [DecidableEq α] (P : SevenDFA α) (f : Nat→α)
    (I : BoundaryContexts.Index P) (t : Bounds×Array Nat) (e : TimedJoin.TimedEntry) :
    e∈runTargets P f I t ↔ ∃ p v,(p,v)∈P1PhaseFamily.targets t.1.period (t.1.hi-t.1.lo) ∧
      ∃ m : Nat,m<3 ∧ decideFormula
        (CachedP1.projection P (t.1.hi-t.1.lo) t.1.period p v.rho
          (BoundaryContexts.prepareAt P (shift f t.1.lo) t.1.period I t.1.lo t.1.hi)
          (P1PhaseFamily.extend t.1.period p v)) [(m:Int)]=true ∧
        trueEntry (t.1.lo+p)
          (t.2[P1ShortKeys.index t.1.period v.j v.rho m]?.getD 0)=e := by
  simp only [runTargets,List.mem_flatMap,choiceTargets_mem]
  constructor
  · rintro ⟨⟨p,v⟩,hv,m,hm,hyes,he⟩
    exact ⟨p,v,hv,m,hm,hyes,he⟩
  · rintro ⟨p,v,hv,m,hm,hyes,he⟩
    exact ⟨(p,v),hv,m,hm,hyes,he⟩

/-- Cached membership is identical to testing the original projected
    formula with the suffix of the whole text. -/
theorem runTargets_mem_prepared [DecidableEq α] (P : SevenDFA α) (f : Nat→α)
    (w : Word α) (t : Bounds×Array Nat) (hlo : t.1.lo≤w.length) (hhi : t.1.hi≤w.length)
    (e : TimedJoin.TimedEntry) :
    e∈runTargets P f (BoundaryContexts.build P w).1 t ↔
      ∃ p v,(p,v)∈P1PhaseFamily.targets t.1.period (t.1.hi-t.1.lo) ∧
        ∃ m : Nat,m<3 ∧ decideFormula
          (P1Target.projection P (shift f t.1.lo) (t.1.hi-t.1.lo) t.1.period p v.rho
            (w.drop t.1.hi) (P1PhaseFamily.extend t.1.period p v)) [(m:Int)]=true ∧
          trueEntry (t.1.lo+p)
            (t.2[P1ShortKeys.index t.1.period v.j v.rho m]?.getD 0)=e := by
  rw [runTargets_mem]
  have hp : ∀ p (v : P1PhaseFamily.Three),
      CachedP1.projection P (t.1.hi-t.1.lo) t.1.period p v.rho
        (BoundaryContexts.prepareAt P (shift f t.1.lo) t.1.period
          (BoundaryContexts.build P w).1 t.1.lo t.1.hi) (P1PhaseFamily.extend t.1.period p v)=
      P1Target.projection P (shift f t.1.lo) (t.1.hi-t.1.lo) t.1.period p v.rho
        (w.drop t.1.hi) (P1PhaseFamily.extend t.1.period p v) := by
    intro p v
    exact CachedP1.projectionAt_eq P (shift f t.1.lo) (t.1.hi-t.1.lo) t.1.period
      p v.rho w t.1.lo t.1.hi hlo hhi (P1PhaseFamily.extend t.1.period p v)
  simp only [hp]

def targets [DecidableEq α] (P : SevenDFA α) (f : Nat→α)
    (I : BoundaryContexts.Index P) (tables : List (Bounds×Array Nat)) : List TimedJoin.TimedEntry :=
  tables.flatMap (runTargets P f I)

theorem targets_mem_run [DecidableEq α] (P : SevenDFA α) (f : Nat→α)
    (I : BoundaryContexts.Index P) (tables : List (Bounds×Array Nat)) (e : TimedJoin.TimedEntry) :
    e∈targets P f I tables ↔ ∃ t,t∈tables ∧ e∈runTargets P f I t :=
  List.mem_flatMap

theorem targets_mem [DecidableEq α] (P : SevenDFA α) (f : Nat→α) (n : Nat)
    (tables : List (Bounds×Array Nat))
    (h : ∀ t,t∈tables→t.1.lo≤n ∧ t.1.hi≤n) (e : TimedJoin.TimedEntry) :
    e∈targets P f (BoundaryContexts.build P (segment f 0 n)).1 tables ↔
      ∃ R ranks,(R,ranks)∈tables ∧
        ∃ p v,(p,v)∈P1PhaseFamily.targets R.period (R.hi-R.lo) ∧
          ∃ m : Nat,m<3 ∧ decideFormula
            (P1Target.projection P (shift f R.lo) (R.hi-R.lo) R.period p v.rho
              ((segment f 0 n).drop R.hi) (P1PhaseFamily.extend R.period p v)) [(m:Int)]=true ∧
            trueEntry (R.lo+p) (ranks[P1ShortKeys.index R.period v.j v.rho m]?.getD 0)=e := by
  rw [targets_mem_run]
  constructor
  · rintro ⟨⟨R,ranks⟩,ht,he⟩
    obtain ⟨hlo,hhi⟩ := h (R,ranks) ht
    have hh := (runTargets_mem_prepared P f (segment f 0 n) (R,ranks)
      (by simpa only [segment_length] using hlo) (by simpa only [segment_length] using hhi) e).mp he
    exact ⟨R,ranks,ht,hh⟩
  · rintro ⟨R,ranks,ht,he⟩
    obtain ⟨hlo,hhi⟩ := h (R,ranks) ht
    exact ⟨(R,ranks),ht,(runTargets_mem_prepared P f (segment f 0 n) (R,ranks)
      (by simpa only [segment_length] using hlo) (by simpa only [segment_length] using hhi) e).mpr he⟩

theorem flatMap_length_le {X Y : Type} (xs : List X) (f : X→List Y) (c : Nat)
    (h : ∀ x,x∈xs→(f x).length≤c) : (xs.flatMap f).length≤c*xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.flatMap_cons,List.length_append,List.length_cons,Nat.mul_succ]
    have hx := h x (by simp)
    have hs := ih (fun y hy=>h y (by simp [hy]))
    omega

theorem runTargets_bound [DecidableEq α] (P : SevenDFA α) (f : Nat→α)
    (I : BoundaryContexts.Index P) (t : Bounds×Array Nat) :
    (runTargets P f I t).length≤3*(P1PhaseFamily.targets t.1.period (t.1.hi-t.1.lo)).length := by
  unfold runTargets
  apply flatMap_length_le
  intro z _
  exact choiceTargets_bound _ _ _ _ _ _ _ _

theorem targets_bound [DecidableEq α] (P : SevenDFA α) (f : Nat→α)
    (I : BoundaryContexts.Index P) (tables : List (Bounds×Array Nat)) :
    (targets P f I tables).length≤3*(P1PhaseFamily.allTargets (tables.map Prod.fst)).length := by
  induction tables with
  | nil => simp [targets,P1PhaseFamily.allTargets]
  | cons t ts ih =>
    change (runTargets P f I t++targets P f I ts).length≤_
    simp only [List.length_append,List.map_cons,P1PhaseFamily.allTargets,List.length_map,Nat.mul_add]
    exact Nat.add_le_add (runTargets_bound P f I t) ih

theorem targets_formula [DecidableEq α] (P : SevenDFA α) (f : Nat→α)
    (I : BoundaryContexts.Index P) (tables : List (Bounds×Array Nat))
    (e : TimedJoin.TimedEntry) (he : e∈targets P f I tables) : e.entry.formula=[[]] := by
  obtain ⟨t,_,ht⟩ := (targets_mem_run P f I tables e).mp he
  obtain ⟨p,v,_,m,_,_,rfl⟩ := (runTargets_mem P f I t e).mp ht
  rfl

theorem targets_good [DecidableEq α] (P : SevenDFA α) (f : Nat→α)
    (I : BoundaryContexts.Index P) (tables : List (Bounds×Array Nat)) (K : Nat) :
    TimedJoin.Good K (targets P f I tables) := by
  intro e he
  obtain ⟨t,_,ht⟩ := (targets_mem_run P f I tables e).mp he
  obtain ⟨p,v,_,m,_,_,rfl⟩ := (runTargets_mem P f I t e).mp ht
  exact P1ShortSources.trueEntry_good _ _ _

theorem constantFormula_weight (es : List TimedJoin.TimedEntry)
    (h : ∀ e,e∈es→e.entry.formula=[[]]) : TimedJoin.weight es=es.length := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    change e.entry.formula.length+TimedJoin.weight es=es.length+1
    rw [h e (by simp),ih (fun x hx=>h x (by simp [hx]))]
    simp only [List.length_cons,List.length_nil]
    omega

theorem targets_weight [DecidableEq α] (P : SevenDFA α) (f : Nat→α)
    (I : BoundaryContexts.Index P) (tables : List (Bounds×Array Nat)) :
    TimedJoin.weight (targets P f I tables)=(targets P f I tables).length :=
  constantFormula_weight _ (targets_formula P f I tables)

theorem targets_positions [DecidableEq α] (P : SevenDFA α) (f : Nat→α) (n : Nat)
    (I : BoundaryContexts.Index P) (tables : List (Bounds×Array Nat))
    (h : ∀ t,t∈tables→t.1.Valid f n) :
    ∀ e,e∈targets P f I tables→e.pos≤n := by
  intro e he
  obtain ⟨t,ht,he⟩ := (targets_mem_run P f I tables e).mp he
  obtain ⟨p,v,hpv,m,_,_,rfl⟩ := (runTargets_mem P f I t e).mp he
  have hp := ((phaseTargets_mem _ _ _ v).mp hpv).1
  have hv := h t ht
  have hlo := hv.1
  have hhi := hv.2.1
  change t.1.lo+p≤n
  omega

theorem concrete_bound {σ : Nat} (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat)
    (I : BoundaryContexts.Index P) (R : ExactKeys.Registry σ) :
    (targets P f I (P1ShortKeys.buildRunTables R f (SmallPeriodRuns.cubic f n Q)).tables).length≤
      9*Q^3*(2*n*DyadicIndex.heightFor n) := by
  have h := targets_bound P f I (P1ShortKeys.buildRunTables R f (SmallPeriodRuns.cubic f n Q)).tables
  rw [P1ShortKeys.buildRunTables_runs] at h
  have hb := Nat.mul_le_mul_left 3 (P1PhaseFamily.concrete_target_bound f n Q)
  apply Nat.le_trans h
  simpa only [← Nat.mul_assoc] using hb

end REWB.P1ShortTargets
