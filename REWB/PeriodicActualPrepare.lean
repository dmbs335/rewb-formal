import REWB.PeriodicActualShort

/-! Actual shared preparation for the two external P1 periodic branches.
Every returned event is built through the measured formula/event path.
The text, run enumeration, contexts, key registry and modulus are each
prepared once; no old event generator is evaluated to recover a ledger.
The established discovery/cache/key primitive ledgers are retained. -/
namespace REWB.PeriodicActual
open REWB.Periodic REWB.RunGeometry REWB.PeriodicConstruction
variable {σ : Nat}

structure Prepared (α : Type) where
  text : Word α
  sources : List TimedJoin.TimedEntry
  targets : List TimedJoin.TimedEntry
  modulus : Nat
  work : Nat

namespace Long

def prepare (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n Q : Nat) : Prepared (Fin σ) :=
  let text := P2.segment f 0 n
  let contexts := BoundaryContexts.build P text.1
  let enumerated := SmallPeriodRuns.enumerate f n Q
  let cubic := Orbit.filter (fun R : Bounds => (decide (3*R.period≤R.hi-R.lo),3)) enumerated.1
  let keys := ExactKeys.buildRunTables ExactKeys.initial f cubic.1
  let events := Events.runs P f contexts.1 Q keys.registry.next keys.tables
  let modulus := ActualModulus.build events.sources events.targets
  ⟨text.1,events.sources,events.targets,modulus.1,
    text.2+contexts.2+enumerated.2+cubic.2+keys.work+events.work+modulus.2+20⟩

theorem prepare_text (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n Q : Nat) :
    (prepare P f n Q).text=Periodic.segment f 0 n := P2.segment_value f 0 n

theorem prepare_sources (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n Q : Nat) :
    (prepare P f n Q).sources=(P1Events.generated P f n Q).sources := by
  simp only [prepare,P2.segment_value,Orbit.filter_value,Events.runs_sources,
    P1Events.generated,SmallPeriodRuns.cubic]

theorem prepare_targets (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n Q : Nat) :
    (prepare P f n Q).targets=(P1Events.generated P f n Q).targets := by
  simp only [prepare,P2.segment_value,Orbit.filter_value,Events.runs_targets,
    P1Events.generated,SmallPeriodRuns.cubic]

theorem prepare_modulus (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n Q : Nat) :
    (prepare P f n Q).modulus=(CountedSmallPeriodP1.solve P f n Q).modulus := by
  simp only [prepare,P2.segment_value,Orbit.filter_value,Events.runs_sources,Events.runs_targets,
    CountedSmallPeriodP1.solve]

theorem prepare_work (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n Q : Nat) :
    (prepare P f n Q).work≤
      (CountedSmallPeriodP1.solve P f n Q).runComparisons+
      (CountedSmallPeriodP1.solve P f n Q).contextEntries+
      (CountedSmallPeriodP1.solve P f n Q).keyWork+
      (CountedSmallPeriodP1.solve P f n Q).cacheWork+
      (CountedSmallPeriodP1.solve P f n Q).modulusSteps+
      (Events.sourceBudget P+39)*(P1Events.generated P f n Q).sources.length+
      (Events.targetBudget P+37)*(P1Events.generated P f n Q).targets.length+
      5*(2*n*DyadicIndex.heightFor n)+3*n+23 := by
  have hv : ∀e,e∈(ExactKeys.buildRunTables ExactKeys.initial f (SmallPeriodRuns.cubic f n Q)).tables →
      0<e.1.period ∧ e.1.lo≤(Periodic.segment f 0 n).length ∧ e.1.hi≤(Periodic.segment f 0 n).length := by
    intro e he
    have hh := (P1Events.table_valid f n Q e he).1
    have hb := P1Events.table_boundaries f n Q e he
    rw [Periodic.segment_length]
    exact ⟨hh.2.2.2.1.1,hb⟩
  have he := Events.runs_work P f (Periodic.segment f 0 n) Q
    (ExactKeys.buildRunTables ExactKeys.initial f (SmallPeriodRuns.cubic f n Q)).registry.next _ hv
  have hf := Orbit.filter_work (fun R : Bounds => (decide (3*R.period≤R.hi-R.lo),3))
    (SmallPeriodRuns.enumerate f n Q).1 3 (fun _ _ => Nat.le_refl _)
  have hl := Nat.le_trans (P2.length_le_mass (SmallPeriodRuns.enumerate f n Q).1)
    (SmallPeriodRuns.enumerate_mass f n Q)
  have hf' := Nat.le_trans hf (Nat.add_le_add_right (Nat.mul_le_mul_right 5 hl) 1)
  unfold prepare CountedSmallPeriodP1.solve CountedSmallPeriodP1.Result.cacheWork P1Events.generated
  dsimp only
  rw [P2.segment_value,P2.segment_work,Orbit.filter_value,Events.runs_sources,Events.runs_targets]
  dsimp only
  dsimp only [SmallPeriodRuns.cubic] at he ⊢
  omega

end Long

namespace Short

/-- The additional word/list-construction ledger accompanies the exact
old key registry result. Assigned ranks and registry order are unchanged. -/
def sourceKeys (R : ExactKeys.Registry σ) (f : Nat → Fin σ) :
    List P1ShortSources.Token → Result (P1ShortSources.KeyBatch σ)
  | [] => (⟨R,[],0⟩,1)
  | v::vs =>
    let word := P2.segment f v.1 v.2
    let assigned := ExactKeys.assign R word.1
    let rest := sourceKeys assigned.registry f vs
    (⟨rest.1.registry,(v,assigned.rank)::rest.1.entries,assigned.work+rest.1.work⟩,
      word.2+rest.2+6)

theorem sourceKeys_value (R : ExactKeys.Registry σ) (f : Nat → Fin σ)
    (xs : List P1ShortSources.Token) :
    (sourceKeys R f xs).1=P1ShortSources.buildKeys R f xs := by
  induction xs generalizing R with
  | nil => rfl
  | cons x xs ih => simp only [sourceKeys,P2.segment_value,P1ShortSources.buildKeys,ih]

theorem sourceKeys_work (R : ExactKeys.Registry σ) (f : Nat → Fin σ)
    (xs : List P1ShortSources.Token) :
    (sourceKeys R f xs).2=3*P1ShortSources.cells xs+7*xs.length+1 := by
  induction xs generalizing R with
  | nil => rfl
  | cons x xs ih =>
    simp only [sourceKeys,ih,P2.segment_work,P1ShortSources.cells,List.length_cons,Nat.mul_add]
    omega

def prepare (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n Q : Nat) : Prepared (Fin σ) :=
  let text := P2.segment f 0 n
  let contexts := BoundaryContexts.build P text.1
  let enumerated := SmallPeriodRuns.enumerate f n Q
  let cubic := Orbit.filter (fun R : Bounds => (decide (3*R.period≤R.hi-R.lo),3)) enumerated.1
  let choices := sourceChoices n (3*Q)
  let sk := sourceKeys ExactKeys.initial f choices.1
  let tk := P1ShortKeys.buildRunTables sk.1.registry f cubic.1
  let src := sources P contexts.1 sk.1.entries
  let tgt := runs P f contexts.1 tk.tables
  ⟨text.1,src.1,tgt.1,1,
    text.2+contexts.2+enumerated.2+cubic.2+choices.2+sk.1.work+sk.2+tk.work+src.2+tgt.2+20⟩

theorem prepare_text (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n Q : Nat) :
    (prepare P f n Q).text=Periodic.segment f 0 n := P2.segment_value f 0 n

theorem prepare_sources (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n Q : Nat) :
    (prepare P f n Q).sources=P1ShortBranch.sourceList P f n Q := by
  simp only [prepare,P2.segment_value,sourceChoices_value,sourceKeys_value,sources_value,
    CountedShortBranch.sourceEvents_value,P1ShortBranch.sourceList,P1ShortBranch.sourceKeys]

theorem prepare_targets (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n Q : Nat) :
    (prepare P f n Q).targets=P1ShortBranch.targetList P f n Q := by
  simp only [prepare,P2.segment_value,sourceChoices_value,sourceKeys_value,runs_value,
    CountedShortTargets.targets_value,Orbit.filter_value,P1ShortBranch.targetList,
    P1ShortBranch.keyTables,P1ShortBranch.sourceKeys,SmallPeriodRuns.cubic]

theorem prepare_modulus (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n Q : Nat) :
    (prepare P f n Q).modulus=1 := rfl

theorem prepare_work (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n Q : Nat) :
    (prepare P f n Q).work≤
      (CountedShortBranch.solve P f n Q).runComparisons+
      (CountedShortBranch.solve P f n Q).contextEntries+
      (CountedShortBranch.solve P f n Q).keyWork+
      (CountedShortBranch.solve P f n Q).targets.cacheWork+
      17*(CountedShortBranch.solve P f n Q).sourcePrefixReads+
      3*(CountedShortBranch.solve P f n Q).sourceWordCells+
      (choiceBudget P+58)*(P1PhaseFamily.allTargets
        ((P1ShortBranch.keyTables f n Q).tables.map Prod.fst)).length+
      9*((n+1)*(3*Q))+5*(2*n*DyadicIndex.heightFor n)+10*n+38 := by
  have hv : ∀e,e∈(P1ShortBranch.keyTables f n Q).tables →
      0<e.1.period ∧ e.1.lo≤(Periodic.segment f 0 n).length ∧ e.1.hi≤(Periodic.segment f 0 n).length := by
    intro e he
    have hh := (P1ShortBranch.table_valid f n Q e he).1
    have hb := P1ShortBranch.table_boundaries f n Q e he
    rw [Periodic.segment_length]
    exact ⟨hh.2.2.2.1.1,hb⟩
  have ht := runs_work P f (Periodic.segment f 0 n) (P1ShortBranch.keyTables f n Q).tables hv
  have hc := sourceChoices_work n (3*Q)
  have hf := Orbit.filter_work (fun R : Bounds => (decide (3*R.period≤R.hi-R.lo),3))
    (SmallPeriodRuns.enumerate f n Q).1 3 (fun _ _ => Nat.le_refl _)
  have hl := Nat.le_trans (P2.length_le_mass (SmallPeriodRuns.enumerate f n Q).1)
    (SmallPeriodRuns.enumerate_mass f n Q)
  have hf' := Nat.le_trans hf (Nat.add_le_add_right (Nat.mul_le_mul_right 5 hl) 1)
  have hkl := congrArg List.length (P1ShortSources.buildKeys_tokens ExactKeys.initial f
    (P1ShortSources.choices n (3*Q)))
  simp only [List.length_map] at hkl
  unfold prepare CountedShortBranch.solve
  dsimp only
  rw [P2.segment_value,P2.segment_work,Orbit.filter_value,sourceChoices_value,sourceKeys_value,
    sourceKeys_work,sources_work,CountedShortBranch.sourceEvents_reads,hkl]
  dsimp only
  dsimp only [P1ShortBranch.keyTables,P1ShortBranch.sourceKeys,SmallPeriodRuns.cubic] at ht ⊢
  omega

end Short
end REWB.PeriodicActual
