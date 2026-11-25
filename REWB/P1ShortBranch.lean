import REWB.P1ShortSources
import REWB.P1ShortKeys
import REWB.P1ShortTargets

/-! The short-inner P1 branch does not require a periodic source. It
    compares full short words in the exact dictionary and freezes the
    target exponent to one of 0,1,2 before the chronological join. -/
namespace REWB.P1ShortBranch
open REWB.Periodic REWB.RunGeometry REWB.AffineProjection
variable {α : Type} {σ : Nat}

theorem phase_factor (s : Nat→α) (n q a L : Nat)
    (h : Period s n q) (hq : 0<q) (hL : a+L≤n) :
    segment s a L=P1Target.keyWord (segment s (a%q) q) (L%q) (L/q) := by
  have hmod : a%q≤a := Nat.mod_le a q
  rw [factor_at_phase h a L hL,compress_factor h (a%q) L (by omega)]
  unfold P1Target.keyWord
  rw [SmallPeriodP2.segment_take s (a%q) q (L%q) (Nat.le_of_lt (Nat.mod_lt _ hq))]

theorem join_sound [DecidableEq α] (P : SevenDFA α) (f : Nat→α) (n : Nat)
    (T : Bounds) (hT : T.Valid f n) (i L p rho m : Nat) (ph : P1Target.Layout Nat)
    (hp : p≤T.hi-T.lo) (horder : i+L≤T.lo+p)
    (hA : P.A.accepts (segment f 0 i))
    (hC : P.C.accepts (Spec.slice (segment f 0 n) (i+L) (T.lo+p)))
    (hword : segment f i L=P1Target.keyWord (segment (shift f T.lo) ph.j T.period) rho m)
    (ht : decideFormula (P1Target.projection P (shift f T.lo) (T.hi-T.lo)
      T.period p rho ((segment f 0 n).drop T.hi) ph) [(m:Int)]=true) :
    MatchesWithin P.nested1 (segment f 0 n) 2 := by
  have htb : T.lo+p≤n := by
    have hh := hT.2.1
    have hl := hT.1
    omega
  have hprefix : segment f 0 i++segment f i L=segment f 0 (i+L) := by
    simpa only [Nat.zero_add] using (segment_append f 0 i L).symm
  have hs : P1Target.SourceOK P (segment f 0 (T.lo+p))
      (P1Target.keyWord (segment (shift f T.lo) ph.j T.period) rho m) := by
    refine ⟨segment f 0 i,Spec.slice (segment f 0 n) (i+L) (T.lo+p),?_,hA,hC⟩
    rw [← hword,hprefix,P1GlobalJoin.prefix_gap f n (i+L) (T.lo+p) horder htb]
  have htlo : T.lo≤n := by
    have hh := hT.2.1
    have hl := hT.1
    omega
  have hpre : (segment f 0 n).take T.lo++P2Periodic.factor (shift f T.lo) 0 p=
      segment f 0 (T.lo+p) := by
    rw [SmallPeriodP2.segment_take f 0 n T.lo htlo]
    simpa only [P2Periodic.factor,Nat.sub_zero] using P1GlobalJoin.prefix_local f T.lo p
  have hj := P1Target.projected_join_sound P (shift f T.lo) (T.hi-T.lo)
    T.period p rho m hT.2.2.2.1 hp ((segment f 0 n).take T.lo)
    ((segment f 0 n).drop T.hi) ph ht (by rwa [hpre])
  rwa [SmallPeriodP2.text_reconstruct f n T.lo T.hi
    (by have hh := hT.1; omega) hT.2.1] at hj

structure ShortWitness (P : SevenDFA α) (f : Nat→α) (n : Nat) (T : Bounds) where
  outerStart : Nat
  target : P1Target.Layout Nat
  earlierStart : Nat
  target_ok : P1Target.Witness P (shift f T.lo) (T.hi-T.lo) outerStart
    ((segment f 0 n).drop T.hi) target
  short_inner : target.t-target.j<3*T.period
  long_outer : T.period≤target.e-outerStart
  earlier : earlierStart+(target.t-target.j)≤T.lo+outerStart
  equal_inner : segment f earlierStart (target.t-target.j)=
    P2Periodic.factor (shift f T.lo) target.j target.t
  prefix_ok : P.A.accepts (segment f 0 earlierStart)
  gap_ok : P.C.accepts (Spec.slice (segment f 0 n)
    (earlierStart+(target.t-target.j)) (T.lo+outerStart))

def ShortWitness.innerLength {P : SevenDFA α} {f : Nat→α} {n : Nat} {T : Bounds}
    (w : ShortWitness P f n T) : Nat := w.target.t-w.target.j

theorem witness_target_complete [DecidableEq α] (P : SevenDFA α) (f : Nat→α)
    (n : Nat) (T : Bounds) (hT : T.Valid f n) (w : ShortWitness P f n T) :
    ∃ v,(w.outerStart,v)∈P1PhaseFamily.targets T.period (T.hi-T.lo) ∧
      w.innerLength/T.period<3 ∧
      decideFormula (P1Target.projection P (shift f T.lo) (T.hi-T.lo)
        T.period w.outerStart v.rho ((segment f 0 n).drop T.hi)
        (P1PhaseFamily.extend T.period w.outerStart v))
        [((w.innerLength/T.period : Nat) : Int)]=true ∧
      segment f w.earlierStart w.innerLength=
        P1Target.keyWord (segment (shift f T.lo) v.j T.period) v.rho
          (w.innerLength/T.period) := by
  obtain ⟨v,hv,hph,hr⟩ := P1PhaseFamily.phase_family P (shift f T.lo) (T.hi-T.lo)
    T.period w.outerStart hT.2.2.2.1 ((segment f 0 n).drop T.hi) w.target
    w.target_ok w.long_outer
  have ht := P1PhaseFamily.projection_complete P (shift f T.lo) (T.hi-T.lo)
    T.period w.outerStart hT.2.2.2.1 ((segment f 0 n).drop T.hi) w.target w.target_ok
  obtain ⟨h1,h2,h3,h4,h5,h6,_⟩ := w.target_ok
  have hm : w.innerLength/T.period<3 := by
    have hmul := Nat.div_mul_le_self w.innerLength T.period
    have hl := w.short_inner
    change w.innerLength<3*T.period at hl
    by_cases hm : w.innerLength/T.period<3
    · exact hm
    · have hh := Nat.mul_le_mul_right T.period (show 3≤w.innerLength/T.period by omega)
      omega
  refine ⟨v,List.mem_flatMap.mpr ⟨w.outerStart,List.mem_range.mpr (by omega),
    List.mem_map.mpr ⟨v,hv,rfl⟩⟩,hm,?_,?_⟩
  · rw [hph,hr]
    exact ht
  · have hvj : v.j=w.target.j%T.period := congrArg P1Target.Layout.j hph
    rw [hvj,hr]
    have hh := phase_factor (shift f T.lo) (T.hi-T.lo) T.period w.target.j w.innerLength
      hT.2.2.2.1.2.1 hT.2.2.2.1.1 (by dsimp only [ShortWitness.innerLength]; omega)
    exact w.equal_inner.trans hh

def sourceKeys (f : Nat→Fin σ) (n Q : Nat) : P1ShortSources.KeyBatch σ :=
  P1ShortSources.buildKeys ExactKeys.initial f (P1ShortSources.choices n (3*Q))

def keyTables (f : Nat→Fin σ) (n Q : Nat) : P1ShortKeys.RunTables σ :=
  P1ShortKeys.buildRunTables (sourceKeys f n Q).registry f (SmallPeriodRuns.cubic f n Q)

theorem sourceKeys_valid (f : Nat→Fin σ) (n Q : Nat) : (sourceKeys f n Q).registry.Valid :=
  P1ShortSources.buildKeys_valid ExactKeys.initial ExactKeys.initial_valid f _

theorem keyTables_valid (f : Nat→Fin σ) (n Q : Nat) : (keyTables f n Q).registry.Valid :=
  P1ShortKeys.buildRunTables_valid _ (sourceKeys_valid f n Q) f _

theorem table_valid (f : Nat→Fin σ) (n Q : Nat) (e : Bounds×Array Nat)
    (he : e∈(keyTables f n Q).tables) :
    e.1.Valid f n ∧ e.1.period≤Q ∧ 3*e.1.period≤e.1.hi-e.1.lo := by
  have hm : e.1∈SmallPeriodRuns.cubic f n Q := by
    rw [← P1ShortKeys.buildRunTables_runs (sourceKeys f n Q).registry f
      (SmallPeriodRuns.cubic f n Q)]
    exact List.mem_map.mpr ⟨e,he,rfl⟩
  exact (SmallPeriodRuns.cubic_mem f n Q e.1).mp hm

theorem table_boundaries (f : Nat→Fin σ) (n Q : Nat) (e : Bounds×Array Nat)
    (he : e∈(keyTables f n Q).tables) : e.1.lo≤n ∧ e.1.hi≤n := by
  have hv := (table_valid f n Q e he).1
  have hlo := hv.1
  have hhi := hv.2.1
  exact ⟨by omega,hhi⟩

theorem table_exists (f : Nat→Fin σ) (n Q : Nat) (T : Bounds)
    (hT : T∈SmallPeriodRuns.cubic f n Q) : ∃ ranks,(T,ranks)∈(keyTables f n Q).tables := by
  have hm : T∈(keyTables f n Q).tables.map Prod.fst := by
    simpa only [keyTables,P1ShortKeys.buildRunTables_runs] using hT
  obtain ⟨⟨R,ranks⟩,hr,he⟩ := List.mem_map.mp hm
  dsimp only at he
  subst R
  exact ⟨ranks,hr⟩

theorem source_lookup (f : Nat→Fin σ) (n Q i L rank : Nat)
    (h : ExactKeys.lookup (sourceKeys f n Q).registry.tree (segment f i L)=some rank) :
    ExactKeys.lookup (keyTables f n Q).registry.tree (segment f i L)=some rank :=
  P1ShortKeys.buildRunTables_preserves _ f _ _ rank h

theorem table_lookup (f : Nat→Fin σ) (n Q : Nat) (e : Bounds×Array Nat)
    (he : e∈(keyTables f n Q).tables) (phase rho m : Nat)
    (hp : phase<e.1.period) (hr : rho<e.1.period) (hm : m<3) :
    ExactKeys.lookup (keyTables f n Q).registry.tree
      (P1Target.keyWord (segment (shift f e.1.lo) phase e.1.period) rho m)=
        some (e.2[P1ShortKeys.index e.1.period phase rho m]?.getD 0) := by
  obtain ⟨rank,hget,hlookup⟩ := P1ShortKeys.buildRunTables_exact (sourceKeys f n Q).registry f
    (SmallPeriodRuns.cubic f n Q) e he phase rho m hp hr hm
  simpa only [hget,Option.getD] using hlookup

def sourceList (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    List TimedJoin.TimedEntry :=
  P1ShortSources.sourceEvents P (BoundaryContexts.build P (segment f 0 n)).1
    (sourceKeys f n Q).entries

theorem sourceList_good (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q K : Nat) :
    TimedJoin.Good K (sourceList P f n Q) := P1ShortSources.sourceEvents_good _ _ _ _

theorem sourceList_positions (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    ∀ e,e∈sourceList P f n Q→e.pos≤n :=
  P1ShortSources.sourceEvents_positions P f n (3*Q) ExactKeys.initial

theorem sourceList_bound (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (sourceList P f n Q).length≤(n+1)*(3*Q) := by
  have hs := P1ShortSources.sourceEvents_bound P (BoundaryContexts.build P (segment f 0 n)).1
    (sourceKeys f n Q).entries
  have hl := congrArg List.length (P1ShortSources.buildKeys_tokens ExactKeys.initial f
    (P1ShortSources.choices n (3*Q)))
  simp only [List.length_map] at hl
  exact Nat.le_trans (by simpa only [sourceKeys,hl] using hs)
    (P1ShortSources.choices_bound n (3*Q))

theorem sourceList_weight (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    TimedJoin.weight (sourceList P f n Q)=(sourceList P f n Q).length :=
  P1ShortSources.sourceEvents_weight _ _ _

theorem key_work (f : Nat→Fin σ) (n Q : Nat) :
    (sourceKeys f n Q).work+(keyTables f n Q).work≤
      ((3*σ+1)*(3*Q)+1)*((n+1)*(3*Q))+
      (P1ShortKeys.workConstant σ*Q^2+3*Q)*(2*n*DyadicIndex.heightFor n) :=
  Nat.add_le_add (P1ShortSources.generated_source_cost ExactKeys.initial f n Q)
    (P1ShortKeys.concrete_cost (sourceKeys f n Q).registry f n Q)

theorem key_range (f : Nat→Fin σ) (n Q : Nat) :
    (keyTables f n Q).registry.next≤
      (n+1)*(3*Q)+3*Q*(2*n*DyadicIndex.heightFor n) := by
  have hs := P1ShortSources.buildKeys_next ExactKeys.initial f
    (P1ShortSources.choices n (3*Q))
  change (sourceKeys f n Q).registry.next≤0+(P1ShortSources.choices n (3*Q)).length at hs
  have ht := P1ShortKeys.concrete_next (sourceKeys f n Q).registry f n Q
  have hc := P1ShortSources.choices_bound n (3*Q)
  exact Nat.le_trans ht (Nat.add_le_add_right (Nat.le_trans (by simpa using hs) hc) _)

def targetList (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    List TimedJoin.TimedEntry :=
  P1ShortTargets.targets P f (BoundaryContexts.build P (segment f 0 n)).1 (keyTables f n Q).tables

theorem targetList_good (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q K : Nat) :
    TimedJoin.Good K (targetList P f n Q) := P1ShortTargets.targets_good _ _ _ _ _

theorem targetList_positions (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    ∀ e,e∈targetList P f n Q→e.pos≤n :=
  P1ShortTargets.targets_positions P f n _ _ (fun t ht=>(table_valid f n Q t ht).1)

theorem targetList_bound (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (targetList P f n Q).length≤9*Q^3*(2*n*DyadicIndex.heightFor n) :=
  P1ShortTargets.concrete_bound P f n Q _ _

theorem targetList_weight (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    TimedJoin.weight (targetList P f n Q)=(targetList P f n Q).length :=
  P1ShortTargets.targets_weight _ _ _ _

structure Batch where
  sources : List TimedJoin.TimedEntry
  targets : List TimedJoin.TimedEntry
  keyWork : Nat
  wordCells : Nat

/-- One source registry, one continuation through all target key tables,
    and one shared exterior-context index. -/
def generated (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) : Batch :=
  let I := BoundaryContexts.build P (segment f 0 n)
  let S := sourceKeys f n Q
  let T := P1ShortKeys.buildRunTables S.registry f (SmallPeriodRuns.cubic f n Q)
  ⟨P1ShortSources.sourceEvents P I.1 S.entries,P1ShortTargets.targets P f I.1 T.tables,
    S.work+T.work,P1ShortSources.cells (P1ShortSources.choices n (3*Q))⟩

theorem generated_sources (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (generated P f n Q).sources=sourceList P f n Q := rfl

theorem generated_targets (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (generated P f n Q).targets=targetList P f n Q := rfl

def solve (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) : OfflineJoin.Result :=
  let b := generated P f n Q
  OfflineJoin.run P.C 1 0 (segment f 0 n) b.sources b.targets

theorem solve_correct (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (solve P f n Q).answer=true ↔
      TimedJoin.Match P.C (segment f 0 n) 0 (sourceList P f n Q) (targetList P f n Q) := by
  apply OfflineJoin.run_correct P.C 1 0 (segment f 0 n) _ _ (by decide)
    (sourceList_good P f n Q 1) (targetList_good P f n Q 1)
  · intro e he
    simpa only [segment_length] using sourceList_positions P f n Q e he
  · intro e he
    simpa only [segment_length] using targetList_positions P f n Q e he

theorem solve_sound (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat)
    (h : (solve P f n Q).answer=true) : MatchesWithin P.nested1 (segment f 0 n) 2 := by
  obtain ⟨x,hx,y,hy,horder,_,hkey,hC,_,_,_,_⟩ := (solve_correct P f n Q).mp h
  obtain ⟨i,L,hi,hL,hpos,_,hA,hlookup⟩ :=
    P1ShortSources.sourceEvents_sound P f n (3*Q) ExactKeys.initial x hx
  obtain ⟨T,ranks,htab,p,v,hpv,m,hm,ht,rfl⟩ :=
    (P1ShortTargets.targets_mem P f n _ (table_boundaries f n Q) y).mp hy
  have hT := (table_valid f n Q (T,ranks) htab).1
  obtain ⟨hp,hv⟩ := (P1ShortTargets.phaseTargets_mem _ _ _ v).mp hpv
  obtain ⟨hvj,_,hvr⟩ := P1ShortTargets.choices_bounds T.period v hv
  have hsword := source_lookup f n Q i L x.entry.key hlookup
  have htword := table_lookup f n Q (T,ranks) htab v.j v.rho m hvj hvr hm
  have heword := (ExactKeys.rank_eq_iff (keyTables f n Q).registry (keyTables_valid f n Q)
    (segment f i L) (P1Target.keyWord (segment (shift f T.lo) v.j T.period) v.rho m)
    _ _ hsword htword).mp hkey
  rw [hpos] at horder hC
  exact join_sound P f n T hT i L p v.rho m (P1PhaseFamily.extend T.period p v)
    hp horder hA hC heword ht

theorem solve_complete (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat)
    (T : Bounds) (hT : T.Valid f n) (hq : T.period≤Q)
    (hc : 3*T.period≤T.hi-T.lo) (w : ShortWitness P f n T) :
    (solve P f n Q).answer=true := by
  obtain ⟨v,hpv,hm,ht,hword⟩ := witness_target_complete P f n T hT w
  obtain ⟨hp,hv⟩ := (P1ShortTargets.phaseTargets_mem _ _ _ v).mp hpv
  obtain ⟨hvj,_,hvr⟩ := P1ShortTargets.choices_bounds T.period v hv
  have htpos : T.lo+w.outerStart≤n := by
    have hlo := hT.1
    have hhi := hT.2.1
    omega
  have hi : w.earlierStart+w.innerLength≤n := Nat.le_trans w.earlier htpos
  have hL : w.innerLength<3*Q :=
    Nat.lt_of_lt_of_le w.short_inner (Nat.mul_le_mul_left 3 hq)
  obtain ⟨rank,hsrc,hlookup⟩ := P1ShortSources.sourceEvents_complete P f n (3*Q)
    w.earlierStart w.innerLength ExactKeys.initial hi hL w.prefix_ok
  obtain ⟨ranks,htab⟩ := table_exists f n Q T
    ((SmallPeriodRuns.cubic_mem f n Q T).mpr ⟨hT,hq,hc⟩)
  let src := P1ShortSources.trueEntry (w.earlierStart+w.innerLength) rank
  let tgt := P1ShortSources.trueEntry (T.lo+w.outerStart)
    (ranks[P1ShortKeys.index T.period v.j v.rho (w.innerLength/T.period)]?.getD 0)
  have htgt : tgt∈targetList P f n Q :=
    (P1ShortTargets.targets_mem P f n _ (table_boundaries f n Q) tgt).mpr
      ⟨T,ranks,htab,w.outerStart,v,hpv,w.innerLength/T.period,hm,ht,rfl⟩
  have hsword := source_lookup f n Q w.earlierStart w.innerLength rank hlookup
  have htword := table_lookup f n Q (T,ranks) htab v.j v.rho (w.innerLength/T.period) hvj hvr hm
  have hkey : src.entry.key=tgt.entry.key := by
    exact (ExactKeys.rank_eq_iff (keyTables f n Q).registry (keyTables_valid f n Q)
      _ _ _ _ hsword htword).mpr hword
  apply (solve_correct P f n Q).mpr
  exact ⟨src,hsrc,tgt,htgt,w.earlier,by simpa only [segment_length] using htpos,
    hkey,w.gap_ok,0,Nat.le_refl _,P1ShortSources.trueEntry_satisfies _ _ _,
    P1ShortSources.trueEntry_satisfies _ _ _⟩

theorem solve_counts (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (solve P f n Q).tests≤(DyadicIndex.heightFor n+1)*
      ((n+1)*(3*Q)+P.C.stateCount*(9*Q^3*(2*n*DyadicIndex.heightFor n))) ∧
    (solve P f n Q).eventVisits≤(DyadicIndex.heightFor n+1)*
      ((n+1)*(3*Q)+9*Q^3*(2*n*DyadicIndex.heightFor n)) ∧
    (solve P f n Q).textVisits≤(DyadicIndex.heightFor n+1)*n := by
  have h := OfflineJoin.solve_cost P.C 1 0 (DyadicIndex.heightFor n)
    (segment f 0 n) (sourceList P f n Q) (targetList P f n Q)
  simp only [segment_length,Nat.one_mul,sourceList_weight,targetList_weight] at h
  have hs := sourceList_bound P f n Q
  have ht := targetList_bound P f n Q
  simp only [solve,OfflineJoin.run,generated_sources,generated_targets,segment_length]
  refine ⟨Nat.le_trans h.1 ?_,Nat.le_trans h.2.1 ?_,h.2.2.1⟩
  · exact Nat.mul_le_mul_left _ (Nat.add_le_add hs (Nat.mul_le_mul_left _ ht))
  · exact Nat.mul_le_mul_left _ (Nat.add_le_add hs ht)

end REWB.P1ShortBranch
