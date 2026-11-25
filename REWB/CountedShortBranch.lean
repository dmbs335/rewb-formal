import REWB.P1ShortBranch
import REWB.CountedJoin
import REWB.CountedShortTargets

/-! Measured source filtering and chronological sorting for the concrete
    short-inner P1 branch. The complete target projection and decision
    counters are supplied by CountedShortTargets. -/
namespace REWB.CountedShortBranch
open REWB.Periodic REWB.RunGeometry
variable {σ : Nat}

def sourceEvents (P : SevenDFA (Fin σ)) (I : BoundaryContexts.Index P) :
    List (P1ShortSources.Token×Nat)→List TimedJoin.TimedEntry×Nat
  | [] => ([],0)
  | z::zs =>
    let r := sourceEvents P I zs
    (if P1ShortSources.prefixOK P I z.1.1 then
      P1ShortSources.trueEntry (z.1.1+z.1.2) z.2::r.1 else r.1,r.2+1)

def sourceEventsTR (P : SevenDFA (Fin σ)) (I : BoundaryContexts.Index P)
    (es : List (P1ShortSources.Token×Nat)) : List TimedJoin.TimedEntry×Nat :=
  es.foldr (fun z r=>
    (if P1ShortSources.prefixOK P I z.1.1 then
      P1ShortSources.trueEntry (z.1.1+z.1.2) z.2::r.1 else r.1,r.2+1)) ([],0)

@[csimp] theorem sourceEvents_eq_sourceEventsTR : @sourceEvents=@sourceEventsTR := by
  funext σ P I es
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [sourceEvents,sourceEventsTR,List.foldr_cons] at ih ⊢
    rw [ih]

theorem sourceEvents_value (P : SevenDFA (Fin σ)) (I : BoundaryContexts.Index P)
    (es : List (P1ShortSources.Token×Nat)) :
    (sourceEvents P I es).1=P1ShortSources.sourceEvents P I es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [sourceEvents,P1ShortSources.sourceEvents,List.filter_cons]
    cases h : P1ShortSources.prefixOK P I e.1.1 <;>
      simp only [h,Bool.false_eq_true,if_false,if_true,List.map_cons]
    · exact ih
    · rw [ih]
      rfl

theorem sourceEvents_reads (P : SevenDFA (Fin σ)) (I : BoundaryContexts.Index P)
    (es : List (P1ShortSources.Token×Nat)) : (sourceEvents P I es).2=es.length := by
  induction es with
  | nil => rfl
  | cons e es ih => change (sourceEvents P I es).2+1=es.length+1; rw [ih]

def join (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) : CountedJoin.Result :=
  let b := P1ShortBranch.generated P f n Q
  CountedJoin.run P.C 1 0 (segment f 0 n) b.sources b.targets

theorem join_value (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (join P f n Q).value=P1ShortBranch.solve P f n Q :=
  CountedJoin.run_value _ _ _ _ _ _

def eventBudget (P : SevenDFA (Fin σ)) (n Q : Nat) : Nat :=
  (n+1)*(3*Q)+P.C.stateCount*(9*Q^3*(2*n*DyadicIndex.heightFor n))

theorem event_weight (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    CountedJoin.weight P.C 1 (P1ShortBranch.sourceList P f n Q)
      (P1ShortBranch.targetList P f n Q)≤eventBudget P n Q := by
  simp only [CountedJoin.weight,P1ShortBranch.sourceList_weight,
    P1ShortBranch.targetList_weight,Nat.one_mul]
  exact Nat.add_le_add (P1ShortBranch.sourceList_bound P f n Q)
    (Nat.mul_le_mul_left P.C.stateCount (P1ShortBranch.targetList_bound P f n Q))

theorem join_sortSteps (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (join P f n Q).sortSteps≤(DyadicIndex.heightFor n+1)*
      (10*eventBudget P n Q*((eventBudget P n Q).log2+1)) := by
  have hb := event_weight P f n Q
  have h := CountedJoin.run_steps_bound P.C 1 0 (segment f 0 n)
    (P1ShortBranch.sourceList P f n Q) (P1ShortBranch.targetList P f n Q)
    (eventBudget P n Q) hb
  simp only [segment_length] at h
  exact Nat.le_trans h (Nat.mul_le_mul_left _
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 10 hb)))

structure Result extends OfflineJoin.Result where
  sources : List TimedJoin.TimedEntry
  targets : CountedShortTargets.Result
  sortSteps : Nat
  runComparisons : Nat
  contextEntries : Nat
  keyWork : Nat
  registryNext : Nat
  sourcePrefixReads : Nat
  sourceWordCells : Nat

def Result.targetWork (r : Result) : Nat := CountedShortTargets.work r.targets

/-- The executable path uses measured target projection and decisions,
    direct key/context arrays, and the measured chronological sort. -/
def solve (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) : Result :=
  let text := segment f 0 n
  let contexts := BoundaryContexts.build P text
  let enumerated := SmallPeriodRuns.enumerate f n Q
  let runs := enumerated.1.filter (fun R=>decide (3*R.period≤R.hi-R.lo))
  let sk := P1ShortSources.buildKeys ExactKeys.initial f (P1ShortSources.choices n (3*Q))
  let tk := P1ShortKeys.buildRunTables sk.registry f runs
  let src := sourceEvents P contexts.1 sk.entries
  let tgt := CountedShortTargets.targets P f contexts.1 tk.tables
  let joined := CountedJoin.run P.C 1 0 text src.1 tgt.events
  ⟨joined.value,src.1,tgt,joined.sortSteps,enumerated.2,contexts.2,sk.work+tk.work,
    tk.registry.next,src.2,P1ShortSources.cells (P1ShortSources.choices n (3*Q))⟩

theorem solve_sources (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (solve P f n Q).sources=P1ShortBranch.sourceList P f n Q := sourceEvents_value _ _ _

theorem solve_targets (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (solve P f n Q).targets=CountedShortTargets.generated P f n Q
      (P1ShortBranch.sourceKeys f n Q).registry := rfl

theorem solve_target_events (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (solve P f n Q).targets.events=P1ShortBranch.targetList P f n Q :=
  CountedShortTargets.targets_value _ _ _ _

theorem solve_value (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (solve P f n Q).toResult=P1ShortBranch.solve P f n Q := by
  simp only [solve,CountedJoin.run_value,sourceEvents_value,CountedShortTargets.targets_value]
  rfl

theorem solve_answer (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (solve P f n Q).answer=(P1ShortBranch.solve P f n Q).answer :=
  congrArg OfflineJoin.Result.answer (solve_value P f n Q)

theorem solve_sound (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat)
    (h : (solve P f n Q).answer=true) : REWB.MatchesWithin P.nested1 (segment f 0 n) 2 := by
  rw [solve_answer] at h
  exact P1ShortBranch.solve_sound P f n Q h

theorem solve_complete (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat)
    (T : Bounds) (hT : T.Valid f n) (hq : T.period≤Q)
    (hc : 3*T.period≤T.hi-T.lo) (w : P1ShortBranch.ShortWitness P f n T) :
    (solve P f n Q).answer=true := by
  rw [solve_answer]
  exact P1ShortBranch.solve_complete P f n Q T hT hq hc w

theorem solve_sortSteps (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (solve P f n Q).sortSteps≤(DyadicIndex.heightFor n+1)*
      (10*eventBudget P n Q*((eventBudget P n Q).log2+1)) := by
  simp only [solve,sourceEvents_value,CountedShortTargets.targets_value]
  exact join_sortSteps P f n Q

theorem solve_prepare_counts (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (solve P f n Q).runComparisons≤Q*(n+(n+1)*(2*Q*(Q+1)+1)) ∧
    (solve P f n Q).contextEntries=(n+1)*(1+P.H.stateCount) ∧
    (solve P f n Q).keyWork≤
      ((3*σ+1)*(3*Q)+1)*((n+1)*(3*Q))+
      (P1ShortKeys.workConstant σ*Q^2+3*Q)*(2*n*DyadicIndex.heightFor n) ∧
    (solve P f n Q).registryNext≤(n+1)*(3*Q)+3*Q*(2*n*DyadicIndex.heightFor n) ∧
    (solve P f n Q).sourcePrefixReads≤(n+1)*(3*Q) ∧
    (solve P f n Q).sourceWordCells≤(3*Q)*((n+1)*(3*Q)) := by
  refine ⟨SmallPeriodRuns.enumerate_cost f n Q,?_,P1ShortBranch.key_work f n Q,
    P1ShortBranch.key_range f n Q,?_,P1ShortSources.choices_cells n (3*Q)⟩
  · change (BoundaryContexts.build P (segment f 0 n)).2=_
    rw [BoundaryContexts.build_cost,segment_length]
  · change (sourceEvents P _ _).2≤_
    rw [sourceEvents_reads]
    have hl := congrArg List.length (P1ShortSources.buildKeys_tokens ExactKeys.initial f
      (P1ShortSources.choices n (3*Q)))
    simp only [List.length_map] at hl
    rw [hl]
    exact P1ShortSources.choices_bound n (3*Q)

theorem solve_target_counts (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (solve P f n Q).targets.cacheWork≤
      (FullyCachedP2.stateSum P*Q+Q^2)*(2*n*DyadicIndex.heightFor n) ∧
    (solve P f n Q).targetWork≤
      CountedShortTargets.anchorWork P*3*Q^3*(2*n*DyadicIndex.heightFor n) :=
  ⟨CountedShortTargets.generated_cache P f n Q _,CountedShortTargets.generated_work P f n Q _⟩

theorem solve_counts (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (solve P f n Q).tests≤(DyadicIndex.heightFor n+1)*eventBudget P n Q ∧
    (solve P f n Q).eventVisits≤(DyadicIndex.heightFor n+1)*
      ((n+1)*(3*Q)+9*Q^3*(2*n*DyadicIndex.heightFor n)) ∧
    (solve P f n Q).textVisits≤(DyadicIndex.heightFor n+1)*n ∧
    (solve P f n Q).sortSteps≤(DyadicIndex.heightFor n+1)*
      (10*eventBudget P n Q*((eventBudget P n Q).log2+1)) := by
  have h := P1ShortBranch.solve_counts P f n Q
  have hv := solve_value P f n Q
  refine ⟨?_,?_,?_,solve_sortSteps P f n Q⟩
  · change (solve P f n Q).toResult.tests≤_
    rw [hv]
    exact h.1
  · change (solve P f n Q).toResult.eventVisits≤_
    rw [hv]
    exact h.2.1
  · change (solve P f n Q).toResult.textVisits≤_
    rw [hv]
    exact h.2.2

end REWB.CountedShortBranch
