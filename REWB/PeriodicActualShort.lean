import REWB.PeriodicActualEvents
import REWB.PeriodicActualMeasures

/-! Counted actual short P1 event production. A target phase builds one
projected formula and checks precisely exponents 0, 1 and 2. Successful
checks emit true-formula events, preserving the existing exact word-key
semantics. The phase formula is never rebuilt for each exponent. -/
namespace REWB.PeriodicActual.Short
open REWB.Periodic REWB.RunGeometry REWB.PeriodicConstruction
variable {σ : Nat}

def checks (F : AffineProjection.Formula) (q lo p : Nat) (v : P1PhaseFamily.Three)
    (ranks : Array Nat) : List Nat → Result (List TimedJoin.TimedEntry)
  | [] => ([],1)
  | m::ms =>
    let test := CountedProjection.decide [(m:Int)] F
    let rest := checks F q lo p v ranks ms
    (if test.1 then
      P1ShortSources.trueEntry (lo+p) (ranks[P1ShortKeys.index q v.j v.rho m]?.getD 0)::rest.1
     else rest.1,test.2+rest.2+15)

theorem checks_value (F : AffineProjection.Formula) (q lo p : Nat) (v : P1PhaseFamily.Three)
    (ranks : Array Nat) (ms : List Nat) :
    (checks F q lo p v ranks ms).1=(CountedShortTargets.checks F q lo p v ranks ms).events := by
  induction ms with
  | nil => rfl
  | cons m ms ih => simp only [checks,CountedShortTargets.checks,ih]

theorem checks_work (F : AffineProjection.Formula) (q lo p : Nat) (v : P1PhaseFamily.Three)
    (ranks : Array Nat) (ms : List Nat) (B : Nat)
    (hb : ∀m,m∈ms → (CountedProjection.decide [(m:Int)] F).2≤B) :
    (checks F q lo p v ranks ms).2≤(B+15)*ms.length+1 := by
  induction ms with
  | nil => simp [checks]
  | cons m ms ih =>
    have hm := hb m List.mem_cons_self
    have ht := ih (fun k hk => hb k (List.mem_cons_of_mem m hk))
    simp only [checks,List.length_cons,Nat.mul_add,Nat.mul_one]
    omega

def choice (P : SevenDFA (Fin σ)) (n q lo p : Nat) (v : P1PhaseFamily.Three)
    (I : FullyCachedP2.Shared P) (ranks : Array Nat) : Result (List TimedJoin.TimedEntry) :=
  let projected := Formula.projectTarget P n q p v.rho I (P1PhaseFamily.extend q p v)
  let out := checks projected.1 q lo p v ranks [0,1,2]
  (out.1,projected.2+out.2+20)

theorem choice_value (P : SevenDFA (Fin σ)) (n q lo p : Nat) (v : P1PhaseFamily.Three)
    (I : FullyCachedP2.Shared P) (ranks : Array Nat) :
    (choice P n q lo p v I ranks).1=(CountedShortTargets.choiceTargets P n q lo p v I ranks).events := by
  simp only [choice,Formula.projectTarget_value,checks_value,CountedShortTargets.choiceTargets]
  rfl

theorem choice_length (P : SevenDFA (Fin σ)) (n q lo p : Nat) (v : P1PhaseFamily.Three)
    (I : FullyCachedP2.Shared P) (ranks : Array Nat) :
    (choice P n q lo p v I ranks).1.length≤3 := by
  rw [choice_value,CountedShortTargets.choiceTargets_value]
  exact P1ShortTargets.choiceTargets_bound P n q lo p v I ranks

def choiceBudget (P : SevenDFA (Fin σ)) : Nat :=
  (Formula.targetBudget P P.H.stateCount).work+CountedCachedP1.targetSteps P+
    3*CountedShortTargets.decisionSteps P+67

theorem choice_work (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n q lo p : Nat)
    (v : P1PhaseFamily.Three) (ranks : Array Nat) (w : Word (Fin σ))
    (a b : Nat) (ha : a≤w.length) (hb : b≤w.length) :
    (choice P n q lo p v
      (BoundaryContexts.prepareAt P f q (BoundaryContexts.build P w).1 a b) ranks).2≤choiceBudget P := by
  let I := BoundaryContexts.prepareAt P f q (BoundaryContexts.build P w).1 a b
  have hc := CountedShortTargets.choiceTargets_covered_at P f n q p v.rho w a b ha hb
    (P1PhaseFamily.extend q p v)
  have hp := Formula.projectTarget_work P n q p v.rho I (P1PhaseFamily.extend q p v) hc
  have hd := checks_work (Formula.projectTarget P n q p v.rho I (P1PhaseFamily.extend q p v)).1
    q lo p v ranks [0,1,2] (CountedShortTargets.decisionSteps P) (by
      intro m _
      rw [Formula.projectTarget_value]
      exact CountedShortTargets.projected_decision_bound P n q p v.rho I _ hc m)
  change (Formula.projectTarget P n q p v.rho I (P1PhaseFamily.extend q p v)).2≤
    (Formula.targetBudget P P.H.stateCount).work+CountedCachedP1.targetSteps P+1 at hp
  change _≤(CountedShortTargets.decisionSteps P+15)*3+1 at hd
  change (Formula.projectTarget P n q p v.rho I (P1PhaseFamily.extend q p v)).2+
    (checks (Formula.projectTarget P n q p v.rho I (P1PhaseFamily.extend q p v)).1
      q lo p v ranks [0,1,2]).2+20≤_
  unfold choiceBudget
  omega

def run (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (I : BoundaryContexts.Index P)
    (e : Bounds×Array Nat) : Result (List TimedJoin.TimedEntry) :=
  let cache := BoundaryContexts.countedPrepareAt P (shift f e.1.lo) e.1.period I e.1.lo e.1.hi
  let choices := Choices.targets e.1.period (e.1.hi-e.1.lo)
  let out := CountedProjection.flatMap (fun z : Nat×P1PhaseFamily.Three =>
    choice P (e.1.hi-e.1.lo) e.1.period e.1.lo z.1 z.2 cache.1 e.2) choices.1
  (out.1,cache.2+choices.2+out.2+10)

theorem run_value (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (I : BoundaryContexts.Index P)
    (e : Bounds×Array Nat) :
    (run P f I e).1=(CountedShortTargets.runTargets P f I e).events := by
  simp only [run,CountedProjection.flatMap_value,Choices.targets_value,choice_value,
    CountedShortTargets.runTargets,CountedShortTargets.collect_events]

theorem run_length (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (I : BoundaryContexts.Index P)
    (e : Bounds×Array Nat) :
    (run P f I e).1.length≤3*(P1PhaseFamily.targets e.1.period (e.1.hi-e.1.lo)).length := by
  rw [run_value,CountedShortTargets.runTargets_value]
  exact P1ShortTargets.runTargets_bound P f I e

theorem run_work (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (w : Word (Fin σ))
    (e : Bounds×Array Nat) (hq : 0<e.1.period) (hlo : e.1.lo≤w.length) (hhi : e.1.hi≤w.length) :
    (run P f (BoundaryContexts.build P w).1 e).2≤
      (CountedShortTargets.runTargets P f (BoundaryContexts.build P w).1 e).cacheWork+
      (choiceBudget P+51)*(P1PhaseFamily.targets e.1.period (e.1.hi-e.1.lo)).length := by
  let c := BoundaryContexts.countedPrepareAt P (shift f e.1.lo) e.1.period
    (BoundaryContexts.build P w).1 e.1.lo e.1.hi
  let N := (P1PhaseFamily.targets e.1.period (e.1.hi-e.1.lo)).length
  have hs := Choices.targets_work e.1.period (e.1.hi-e.1.lo) hq
  rw [← P1PhaseFamily.targets_length] at hs
  have hm := PeriodicConstruction.flatMap_bound
    (fun z : Nat×P1PhaseFamily.Three => choice P (e.1.hi-e.1.lo) e.1.period e.1.lo z.1 z.2 c.1 e.2)
    (Choices.targets e.1.period (e.1.hi-e.1.lo)).1 (choiceBudget P) 3
    (fun z _ => choice_work P (shift f e.1.lo) _ _ _ _ _ _ w _ _ hlo hhi)
    (fun z _ => choice_length P _ _ _ _ _ _ _)
  rw [Choices.targets_value] at hm
  have hpos : 1≤N := by
    dsimp [N]
    rw [P1PhaseFamily.targets_length]
    exact Nat.mul_pos (by omega) (Nat.pow_pos hq)
  change _≤N*(choiceBudget P+3+2)+1 at hm
  change c.2+_+_+10≤c.2+(choiceBudget P+51)*N
  rw [Choices.targets_value]
  simp only [Nat.mul_add,Nat.mul_one] at hm
  rw [Nat.mul_comm N (choiceBudget P)] at hm
  simp only [Nat.add_mul]
  dsimp only [c] at hm
  omega

def runs (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (I : BoundaryContexts.Index P) :
    List (Bounds×Array Nat) → Result (List TimedJoin.TimedEntry)
  | [] => ([],1)
  | e::es =>
    let this := run P f I e
    let rest := runs P f I es
    let out := CountedProjection.append this.1 rest.1
    (out.1,this.2+rest.2+out.2+3)

theorem runs_value (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (I : BoundaryContexts.Index P)
    (es : List (Bounds×Array Nat)) :
    (runs P f I es).1=(CountedShortTargets.targets P f I es).events := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [runs,CountedProjection.append_value,run_value,ih,
      CountedShortTargets.targets,CountedShortTargets.collect,CountedShortTargets.join]

theorem runs_work (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (w : Word (Fin σ))
    (es : List (Bounds×Array Nat))
    (hv : ∀e,e∈es → 0<e.1.period ∧ e.1.lo≤w.length ∧ e.1.hi≤w.length) :
    (runs P f (BoundaryContexts.build P w).1 es).2≤
      (CountedShortTargets.targets P f (BoundaryContexts.build P w).1 es).cacheWork+
      (choiceBudget P+58)*(P1PhaseFamily.allTargets (es.map Prod.fst)).length+1 := by
  induction es with
  | nil => simp [runs,CountedShortTargets.targets,CountedShortTargets.collect,P1PhaseFamily.allTargets]
  | cons e es ih =>
    have he := hv e List.mem_cons_self
    have ht := ih (fun t hh => hv t (List.mem_cons_of_mem e hh))
    have hh := run_work P f w e he.1 he.2.1 he.2.2
    have hl := run_length P f (BoundaryContexts.build P w).1 e
    have hp : 1≤(P1PhaseFamily.targets e.1.period (e.1.hi-e.1.lo)).length := by
      rw [P1PhaseFamily.targets_length]
      exact Nat.mul_pos (by omega) (Nat.pow_pos he.1)
    simp only [runs,CountedProjection.append_steps,CountedShortTargets.targets,
      CountedShortTargets.collect,CountedShortTargets.join,List.map_cons,
      P1PhaseFamily.allTargets,List.length_append,List.length_map,Nat.mul_add,Nat.add_mul]
    simp only [Nat.add_mul] at hh ht
    simp only [CountedShortTargets.targets] at ht
    omega

def sources (P : SevenDFA (Fin σ)) (I : BoundaryContexts.Index P) :
    List (P1ShortSources.Token×Nat) → Result (List TimedJoin.TimedEntry)
  | [] => ([],1)
  | z::zs =>
    let rest := sources P I zs
    (if P1ShortSources.prefixOK P I z.1.1 then
      P1ShortSources.trueEntry (z.1.1+z.1.2) z.2::rest.1 else rest.1,rest.2+10)

theorem sources_value (P : SevenDFA (Fin σ)) (I : BoundaryContexts.Index P)
    (xs : List (P1ShortSources.Token×Nat)) :
    (sources P I xs).1=(CountedShortBranch.sourceEvents P I xs).1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [sources,CountedShortBranch.sourceEvents,ih]

theorem sources_work (P : SevenDFA (Fin σ)) (I : BoundaryContexts.Index P)
    (xs : List (P1ShortSources.Token×Nat)) : (sources P I xs).2=10*xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [sources,ih,List.length_cons]; omega

def sourceChoices (n B : Nat) : Result (List P1ShortSources.Token) :=
  let all := Choices.sources B n
  let out := Orbit.filter (fun v : Nat×Nat => (decide (v.1+v.2≤n),2)) all.1
  (out.1,all.2+out.2+2)

theorem sourceChoices_value (n B : Nat) : (sourceChoices n B).1=P1ShortSources.choices n B := by
  simp only [sourceChoices,Orbit.filter_value,Choices.sources_value,
    P1SourceFamily.choices,P1ShortSources.choices]

theorem sourceChoices_work (n B : Nat) :
    (sourceChoices n B).2≤9*((n+1)*B)+7*(n+1)+6 := by
  have ha := Choices.flatRange_work (n+1) (4*B+3) B
    (fun a => Choices.mapRange B (fun phase => (a,phase)))
    (fun a _ => Nat.le_of_eq (Choices.mapRange_work B _))
    (fun a _ => by simp only [Choices.mapRange_value,List.length_map,List.length_range]; exact Nat.le_refl _)
  have hf := Orbit.filter_work (fun v : Nat×Nat => (decide (v.1+v.2≤n),2))
    (Choices.sources B n).1 2 (fun _ _ => Nat.le_refl _)
  rw [Choices.sources_value,P1SourceFamily.choices_length] at hf
  change (Choices.sources B n).2≤_ at ha
  unfold sourceChoices
  dsimp only
  rw [Choices.sources_value]
  have he : (n+1)*(4*B+3+B+4)=5*((n+1)*B)+7*(n+1) := by
    simp only [Nat.mul_add]
    rw [show (n+1)*(4*B)=4*((n+1)*B) by ac_rfl]
    omega
  rw [he] at ha
  omega

end REWB.PeriodicActual.Short
