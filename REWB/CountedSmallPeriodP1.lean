import REWB.SmallPeriodP1
import REWB.CountedJoin
import REWB.ActualModulus

/-! A single executable preparation and measured offline join for the
    concrete small-period P1 branch. Enumeration, exact keys, boundary
    contexts, event formulas and the join are each evaluated once. All
    existing semantic answers and measured event counts are preserved. -/
namespace REWB.CountedSmallPeriodP1
open REWB.Periodic REWB.RunGeometry REWB.UniformPhaseBounds
variable {σ : Nat}

structure Result extends OfflineJoin.Result where
  events : P1Events.Batch
  sortSteps : Nat
  runComparisons : Nat
  contextEntries : Nat
  keyWork : Nat
  registryNext : Nat
  modulus : Nat
  modulusSteps : Nat

def Result.cacheWork (r : Result) : Nat := r.events.cacheWork
def Result.equalityReads (r : Result) : Nat := r.events.equalityReads
def Result.projectionSteps (r : Result) : Nat := r.events.projectionSteps

def solve (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) : Result :=
  let text:=segment f 0 n
  let contexts:=BoundaryContexts.build P text
  let enumerated:=SmallPeriodRuns.enumerate f n Q
  let Rs:=enumerated.1.filter (fun R=>decide (3*R.period≤R.hi-R.lo))
  let keys:=ExactKeys.buildRunTables ExactKeys.initial f Rs
  let events:=P1Events.runs P f contexts.1 Q keys.registry.next keys.tables
  let modulus:=ActualModulus.build events.sources events.targets
  let joined:=CountedJoin.run P.C modulus.1 n text events.sources events.targets
  ⟨joined.value,events,joined.sortSteps,enumerated.2,contexts.2,keys.work,keys.registry.next,
    modulus.1,modulus.2⟩

theorem solve_events (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (solve P f n Q).events=P1Events.generated P f n Q := rfl

theorem solve_value (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (solve P f n Q).toResult=OfflineJoin.run P.C
      (ActualModulus.build (P1Events.generated P f n Q).sources (P1Events.generated P f n Q).targets).1
      n (segment f 0 n) (P1Events.generated P f n Q).sources (P1Events.generated P f n Q).targets :=
  CountedJoin.run_value P.C _ n (segment f 0 n) _ _

theorem solve_modulus (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    0<(solve P f n Q).modulus ∧ (solve P f n Q).modulus≤p1Modulus P := by
  have h:=P1Events.generated_good P f n Q
  exact ⟨ActualModulus.build_pos _ _,ActualModulus.build_le _ _ _ (p1Modulus_pos P) h.1 h.2⟩

theorem solve_modulus_steps (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (solve P f n Q).modulusSteps=2*(ActualModulus.eventCells (P1Events.generated P f n Q).sources+
      ActualModulus.eventCells (P1Events.generated P f n Q).targets)+3 :=
  ActualModulus.build_steps _ _

theorem generated_measures (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (∀ e,e∈(P1Events.generated P f n Q).sources→
      UniformProjection.measure e.entry.formula≤p1SourceBudget P) ∧
    (∀ e,e∈(P1Events.generated P f n Q).targets→
      UniformProjection.measure e.entry.formula≤p1TargetBudget P) := by
  constructor
  · intro x hx
    obtain ⟨e,he,v,hv,rfl⟩ := (P1Events.sources_mem P f n Q _ _ (P1Events.table_boundaries f n Q) x).mp hx
    exact UniformProjection.projection_budget 0 _ _
      (UniformJoin.localSource_covered P _ _ _ _ _ _ _)
  · intro x hx
    obtain ⟨e,he,v,hv,rfl⟩ := (P1Events.targets_mem P f n Q _ _ (P1Events.table_boundaries f n Q) x).mp hx
    exact p1_target_bound P _ _ _ _ _ _ _

theorem solve_modulus_steps_bound (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (solve P f n Q).modulusSteps≤2*
      ((p1SourceBudget P+1)*(3*Q*(2*n*DyadicIndex.heightFor n))+
       (p1TargetBudget P+1)*(3*Q^3*(2*n*DyadicIndex.heightFor n)))+3 := by
  have hm:=generated_measures P f n Q
  have h:=ActualModulus.build_steps_bound (P1Events.generated P f n Q).sources
    (P1Events.generated P f n Q).targets (p1SourceBudget P) (p1TargetBudget P) hm.1 hm.2
  have hs:=P1Events.generated_sizes P f n Q
  exact Nat.le_trans h (Nat.add_le_add_right (Nat.mul_le_mul_left 2
    (Nat.add_le_add (Nat.mul_le_mul_left _ hs.1) (Nat.mul_le_mul_left _ hs.2))) 3)

theorem solve_answer (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (solve P f n Q).answer=(P1Events.solve P f n Q).answer := by
  have hg:=P1Events.generated_good P f n Q
  have hm:=ActualModulus.build_good _ _ _ (p1Modulus_pos P) hg.1 hg.2
  have hp:=P1Events.generated_positions P f n Q
  have hv:=CountedJoin.run_correct P.C
    (ActualModulus.build (P1Events.generated P f n Q).sources (P1Events.generated P f n Q).targets).1
    n (segment f 0 n) _ _ (ActualModulus.build_pos _ _) hm.1 hm.2
    (by simpa only [segment_length] using hp.1) (by simpa only [segment_length] using hp.2)
  change (solve P f n Q).answer=true ↔ _ at hv
  have he:=hv.trans (P1Events.solve_correct P f n Q).symm
  cases hs : (solve P f n Q).answer <;> cases ht : (P1Events.solve P f n Q).answer <;> simp_all

theorem solve_sound (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat)
    (h : (solve P f n Q).answer=true) : MatchesWithin P.nested1 (segment f 0 n) 2 := by
  rw [solve_answer] at h
  exact SmallPeriodP1.solve_sound P f n Q h

theorem solve_complete_long (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat)
    (T : Bounds) (hT : T.Valid f n) (hq : T.period≤Q)
    (w : P1GlobalJoin.LongWitness P f n T) : (solve P f n Q).answer=true := by
  rw [solve_answer]
  exact SmallPeriodP1.solve_complete_long P f n Q T hT hq w

def windowBudget (P : SevenDFA (Fin σ)) (n Q : Nat) : Nat :=
  p1Modulus P*(p1SourceBudget P*(3*Q*(2*n*DyadicIndex.heightFor n))+
    P.C.stateCount*(p1TargetBudget P*(3*Q^3*(2*n*DyadicIndex.heightFor n))))

theorem generated_weight (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    CountedJoin.weight P.C (p1Modulus P)
      (P1Events.generated P f n Q).sources (P1Events.generated P f n Q).targets≤windowBudget P n Q := by
  have hw:=SmallPeriodP1.generated_weights P f n Q
  have hs:=P1Events.generated_sizes P f n Q
  have h1:=Nat.le_trans hw.1 (Nat.mul_le_mul_left _ hs.1)
  have h2:=Nat.le_trans hw.2 (Nat.mul_le_mul_left _ hs.2)
  exact Nat.mul_le_mul_left _ (Nat.add_le_add h1 (Nat.mul_le_mul_left _ h2))

theorem actual_weight (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    CountedJoin.weight P.C
      (ActualModulus.build (P1Events.generated P f n Q).sources (P1Events.generated P f n Q).targets).1
      (P1Events.generated P f n Q).sources (P1Events.generated P f n Q).targets≤windowBudget P n Q :=
  Nat.le_trans (Nat.mul_le_mul_right _ (solve_modulus P f n Q).2) (generated_weight P f n Q)

theorem solve_sort_steps (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (solve P f n Q).sortSteps≤(DyadicIndex.heightFor n+1)*
      (10*windowBudget P n Q*((windowBudget P n Q).log2+1)) := by
  have hw:=actual_weight P f n Q
  have h:=CountedJoin.run_steps_bound P.C _ n (segment f 0 n)
    (P1Events.generated P f n Q).sources (P1Events.generated P f n Q).targets
    (windowBudget P n Q) hw
  rw [segment_length] at h
  exact Nat.le_trans h (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 10 hw)))

theorem solve_event_sizes (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (solve P f n Q).events.sources.length≤3*Q*(2*n*DyadicIndex.heightFor n) ∧
    (solve P f n Q).events.targets.length≤3*Q^3*(2*n*DyadicIndex.heightFor n) :=
  P1Events.generated_sizes P f n Q

theorem solve_prepare_counts (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (solve P f n Q).runComparisons≤Q*(n+(n+1)*(2*Q*(Q+1)+1)) ∧
    (solve P f n Q).contextEntries=(n+1)*(1+P.H.stateCount) ∧
    (solve P f n Q).keyWork≤((3*σ+1)*Q+1)*(2*n*DyadicIndex.heightFor n) ∧
    (solve P f n Q).registryNext≤2*n*DyadicIndex.heightFor n ∧
    (solve P f n Q).cacheWork≤(FullyCachedP2.stateSum P*Q+Q^2)*(2*n*DyadicIndex.heightFor n) ∧
    (solve P f n Q).equalityReads≤9*Q^3*(2*n*DyadicIndex.heightFor n) ∧
    (solve P f n Q).projectionSteps≤CountedCachedP1.targetSteps P*3*Q^3*(2*n*DyadicIndex.heightFor n) := by
  refine ⟨SmallPeriodRuns.enumerate_cost f n Q,?_,P1Events.generated_key_work f n Q,
    P1Events.generated_registry_next f n Q,P1Events.generated_cache_work P f n Q,
    P1Events.generated_equality_reads P f n Q,P1Events.generated_projection_steps P f n Q⟩
  change (BoundaryContexts.build P (segment f 0 n)).2=_
  rw [BoundaryContexts.build_cost,segment_length]

theorem solve_counts (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (solve P f n Q).tests≤(DyadicIndex.heightFor n+1)*windowBudget P n Q ∧
    (solve P f n Q).eventVisits≤(DyadicIndex.heightFor n+1)*
      (3*Q*(2*n*DyadicIndex.heightFor n)+3*Q^3*(2*n*DyadicIndex.heightFor n)) ∧
    (solve P f n Q).textVisits≤(DyadicIndex.heightFor n+1)*n ∧
    (solve P f n Q).sortSteps≤(DyadicIndex.heightFor n+1)*
      (10*windowBudget P n Q*((windowBudget P n Q).log2+1)) := by
  have h:=OfflineJoin.solve_cost P.C
    (ActualModulus.build (P1Events.generated P f n Q).sources (P1Events.generated P f n Q).targets).1
    n (DyadicIndex.heightFor n) (segment f 0 n)
    (P1Events.generated P f n Q).sources (P1Events.generated P f n Q).targets
  have hs:=P1Events.generated_sizes P f n Q
  simp only [segment_length] at h
  have hv:=solve_value P f n Q
  simp only [OfflineJoin.run,segment_length] at hv
  refine ⟨?_,?_,?_,solve_sort_steps P f n Q⟩
  · change (solve P f n Q).toResult.tests≤_
    rw [hv]
    exact Nat.le_trans h.1 (Nat.mul_le_mul_left _ (actual_weight P f n Q))
  · change (solve P f n Q).toResult.eventVisits≤_
    rw [hv]
    exact Nat.le_trans h.2.1 (Nat.mul_le_mul_left _ (Nat.add_le_add hs.1 hs.2))
  · change (solve P f n Q).toResult.textVisits≤_
    rw [hv]
    exact h.2.2.1

end REWB.CountedSmallPeriodP1
