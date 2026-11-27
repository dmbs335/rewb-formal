import REWB.CountedSmallPeriodP1
import REWB.CountedShortBranch

/-! Uniform actual event-formula measures used by measured chronological
window construction. Short events contain the literal true DNF; their
generation still performs the separate measured target projection. -/
namespace REWB.PeriodicActual.Measures
open REWB.Periodic REWB.RunGeometry
variable {σ : Nat}

theorem long_sources (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n Q : Nat)
    (e : TimedJoin.TimedEntry) (he : e∈(P1Events.generated P f n Q).sources) :
    UniformProjection.measure e.entry.formula≤UniformPhaseBounds.p1SourceBudget P :=
  (CountedSmallPeriodP1.generated_measures P f n Q).1 e he

theorem long_targets (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n Q : Nat)
    (e : TimedJoin.TimedEntry) (he : e∈(P1Events.generated P f n Q).targets) :
    UniformProjection.measure e.entry.formula≤UniformPhaseBounds.p1TargetBudget P :=
  (CountedSmallPeriodP1.generated_measures P f n Q).2 e he

theorem short_source (P : SevenDFA (Fin σ)) (I : BoundaryContexts.Index P)
    (tokens : List (P1ShortSources.Token×Nat)) (e : TimedJoin.TimedEntry)
    (he : e∈P1ShortSources.sourceEvents P I tokens) :
    UniformProjection.measure e.entry.formula=1 := by
  obtain ⟨z,_,_,rfl⟩ := (P1ShortSources.sourceEvents_mem P I tokens e).mp he
  rfl

theorem short_target (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (I : BoundaryContexts.Index P)
    (tables : List (Bounds×Array Nat)) (e : TimedJoin.TimedEntry)
    (he : e∈P1ShortTargets.targets P f I tables) :
    UniformProjection.measure e.entry.formula=1 := by
  obtain ⟨t,_,ht⟩ := (P1ShortTargets.targets_mem_run P f I tables e).mp he
  obtain ⟨p,v,_,m,_,_,rfl⟩ := (P1ShortTargets.runTargets_mem P f I t e).mp ht
  rfl

theorem short_sources (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n Q : Nat)
    (e : TimedJoin.TimedEntry) (he : e∈P1ShortBranch.sourceList P f n Q) :
    UniformProjection.measure e.entry.formula=1 :=
  short_source P _ _ e he

theorem short_targets (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n Q : Nat)
    (e : TimedJoin.TimedEntry) (he : e∈P1ShortBranch.targetList P f n Q) :
    UniformProjection.measure e.entry.formula=1 :=
  short_target P f _ _ e he

end REWB.PeriodicActual.Measures
