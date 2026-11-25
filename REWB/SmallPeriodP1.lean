import REWB.P1Events
import REWB.P1EventCounts
import REWB.P1GlobalJoin

/-! End-to-end semantic and generated-event guarantees for the concrete
    small-period P1 join. Completeness here concerns a long inner source;
    short inner sources are handled by a separate exact-word dispatch. -/
namespace REWB.SmallPeriodP1
open REWB.Periodic REWB.RunGeometry REWB.AffineProjection
open REWB.P1Events REWB.UniformPhaseBounds
variable {σ : Nat}

theorem solve_sound (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat)
    (h : (P1Events.solve P f n Q).answer=true) :
    MatchesWithin P.nested1 (segment f 0 n) 2 := by
  obtain ⟨x,hx,y,hy,horder,hyb,hkey,hC,m,hm,hs,ht⟩ :=
    (P1Events.solve_correct P f n Q).mp h
  obtain ⟨e,he,v,hv,rfl⟩ := (sources_mem P f n Q _ _ (table_boundaries f n Q) x).mp hx
  obtain ⟨t,htab,z,hz,rfl⟩ := (targets_mem P f n Q _ _ (table_boundaries f n Q) y).mp hy
  have hev := table_valid f n Q e he
  have htv := table_valid f n Q t htab
  have hvb := source_choice_bounds _ _ _ hv
  have hzb := target_choice_bounds _ _ _ hz
  have hk := (code_exact f (SmallPeriodRuns.cubic f n Q) Q e t he htab
    hev.2.1 htv.2.1 v.2 z.2.j (P1SourceFamily.residue e.1.period v.1 v.2) z.2.rho
    hvb.2 hzb.2.1 (residue_lt _ _ _ hev.1.2.2.2.1.1 hvb.2) hzb.2.2.2).mp hkey
  have hsb : decideFormula (P1SourceFamily.formula P f e.1 v.1 v.2) [(m:Int)]=true :=
    (decideFormula_correct _ _ (UniformJoin.localSource_good P _ _ _ _ _ _ _
      hev.1.2.2.2.1.2.1)).mpr hs
  have htb : decideFormula (P1Target.projection P (shift f t.1.lo) (t.1.hi-t.1.lo)
      t.1.period z.1 z.2.rho (segment f t.1.hi (n-t.1.hi))
      (P1PhaseFamily.extend t.1.period z.1 z.2)) [(m:Int)]=true :=
    (decideFormula_correct _ _ (project_good 5 _
      (P1Target.formula_good P _ _ _ _ _ htv.1.2.2.2.1 _ _))).mpr ht
  have hpost : (segment f 0 n).drop t.1.hi=segment f t.1.hi (n-t.1.hi) := by
    simpa only [Nat.zero_add] using SmallPeriodP2.segment_drop f 0 n t.1.hi htv.1.2.1
  rw [← hpost] at htb
  exact P1GlobalJoin.join_sound P f n e.1 t.1 hev.1 htv.1 v.1 v.2 z.1 z.2.rho m
    (P1PhaseFamily.extend t.1.period z.1 z.2) hzb.1 horder hk.2.1 hk.2.2 hsb htb hC

theorem table_exists (f : Nat→Fin σ) (n Q : Nat) (R : Bounds)
    (hR : R∈SmallPeriodRuns.cubic f n Q) :
    ∃ ranks,(R,ranks)∈(ExactKeys.buildRunTables ExactKeys.initial f
      (SmallPeriodRuns.cubic f n Q)).tables := by
  have hm : R∈(ExactKeys.buildRunTables ExactKeys.initial f
      (SmallPeriodRuns.cubic f n Q)).tables.map Prod.fst := by
    rwa [ExactKeys.buildRunTables_runs]
  obtain ⟨e,he,hr⟩ := List.mem_map.mp hm
  rcases e with ⟨S,ranks⟩
  dsimp only at hr
  subst S
  exact ⟨ranks,he⟩

theorem solve_complete_long (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat)
    (T : Bounds) (hT : T.Valid f n) (hq : T.period≤Q)
    (w : P1GlobalJoin.LongWitness P f n T) :
    (P1Events.solve P f n Q).answer=true := by
  obtain ⟨L⟩ := P1GlobalJoin.long_complete P f n Q T hT hq w
  obtain ⟨rs,hrs⟩ := table_exists f n Q L.source L.source_mem
  obtain ⟨rt,hrt⟩ := table_exists f n Q T L.target_mem
  let next := (ExactKeys.buildRunTables ExactKeys.initial f (SmallPeriodRuns.cubic f n Q)).registry.next
  let a := w.earlierStart+w.innerLength-L.source.lo
  let phase := (w.earlierStart-L.source.lo)%T.period
  let src := sourceSpec P f Q next L.source rs (a,phase)
  let tgt := targetSpec P f n Q next T rt (w.outerStart,L.phases)
  have hsrc : src∈(generated P f n Q).sources :=
    (sources_mem P f n Q next _ (table_boundaries f n Q) src).mpr
      ⟨(L.source,rs),hrs,(a,phase),L.source_choice,rfl⟩
  have htgt : tgt∈(generated P f n Q).targets :=
    (targets_mem P f n Q next _ (table_boundaries f n Q) tgt).mpr
      ⟨(T,rt),hrt,(w.outerStart,L.phases),L.target_choice,rfl⟩
  have hspos : src.pos=w.earlierStart+w.innerLength := by
    change L.source.lo+(w.earlierStart+w.innerLength-L.source.lo)=_
    have hl := L.left
    omega
  have hsp := source_choice_bounds _ _ _ L.source_choice
  have htp := target_choice_bounds _ _ _ L.target_choice
  have htpos : tgt.pos≤n := (generated_positions P f n Q).2 tgt htgt
  have hkey : src.entry.key=tgt.entry.key := by
    apply (code_exact f (SmallPeriodRuns.cubic f n Q) Q (L.source,rs) (T,rt) hrs hrt
      (by rw [L.period]; exact hq) hq phase L.phases.j
      (P1SourceFamily.residue L.source.period a phase) L.phases.rho hsp.2 htp.2.1
      (residue_lt _ _ _ L.valid.2.2.2.1.1 hsp.2) htp.2.2.2).mpr
    exact ⟨L.period,L.residue,L.word⟩
  have hs : Satisfies src.entry.formula [((w.innerLength/T.period : Nat) : Int)] :=
    (decideFormula_correct _ _ (UniformJoin.localSource_good P _ _ _ _ _ _ _
      L.valid.2.2.2.1.2.1)).mp L.source_accepted
  have ht : Satisfies tgt.entry.formula [((w.innerLength/T.period : Nat) : Int)] := by
    have hb := L.target_accepted
    rw [SmallPeriodP2.segment_drop f 0 n T.hi hT.2.1] at hb
    simp only [Nat.zero_add] at hb
    exact (decideFormula_correct _ _ (project_good 5 _
      (P1Target.formula_good P _ _ _ _ _ hT.2.2.2.1 _ _))).mp hb
  apply (P1Events.solve_correct P f n Q).mpr
  refine ⟨src,hsrc,tgt,htgt,?_,by simpa only [segment_length] using htpos,hkey,?_,
    w.innerLength/T.period,?_,hs,ht⟩
  · rw [hspos]
    exact w.earlier
  · rw [hspos]
    exact w.gap_ok
  · have hl : w.innerLength≤n := by
      have ho : w.earlierStart+w.innerLength≤T.lo+w.outerStart := w.earlier
      have hn : T.lo+w.outerStart≤n := htpos
      omega
    exact Nat.le_trans (Nat.div_le_self _ _) hl

theorem weight_bound (es : List TimedJoin.TimedEntry) (C : Nat)
    (h : ∀ e,e∈es→e.entry.formula.length≤C) : TimedJoin.weight es≤C*es.length := by
  induction es with
  | nil => simp [TimedJoin.weight]
  | cons e es ih =>
    have he := h e (by simp)
    have ht := ih (fun x hx=>h x (by simp [hx]))
    simp only [TimedJoin.weight,List.length_cons,Nat.mul_succ]
    omega

theorem generated_weights (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    TimedJoin.weight (generated P f n Q).sources≤p1SourceBudget P*(generated P f n Q).sources.length ∧
    TimedJoin.weight (generated P f n Q).targets≤p1TargetBudget P*(generated P f n Q).targets.length := by
  constructor
  · apply weight_bound
    intro x hx
    obtain ⟨e,he,v,hv,rfl⟩ := (sources_mem P f n Q _ _ (table_boundaries f n Q) x).mp hx
    exact UniformProjection.projection_branches 0 _ _
      (UniformJoin.localSource_covered P _ _ _ _ _ _ _)
  · apply weight_bound
    intro x hx
    obtain ⟨e,he,v,hv,rfl⟩ := (targets_mem P f n Q _ _ (table_boundaries f n Q) x).mp hx
    exact p1_target_branches P _ _ _ _ _ _ _

theorem solve_counts (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (P1Events.solve P f n Q).tests≤(DyadicIndex.heightFor n+1)*
      (p1Modulus P*(p1SourceBudget P*(3*Q*(2*n*DyadicIndex.heightFor n))+
        P.C.stateCount*(p1TargetBudget P*(3*Q^3*(2*n*DyadicIndex.heightFor n))))) ∧
    (P1Events.solve P f n Q).eventVisits≤(DyadicIndex.heightFor n+1)*
      (3*Q*(2*n*DyadicIndex.heightFor n)+3*Q^3*(2*n*DyadicIndex.heightFor n)) ∧
    (P1Events.solve P f n Q).textVisits≤(DyadicIndex.heightFor n+1)*n := by
  have h := OfflineJoin.solve_cost P.C (p1Modulus P) n (DyadicIndex.heightFor n)
    (segment f 0 n) (generated P f n Q).sources (generated P f n Q).targets
  have hw := generated_weights P f n Q
  have hs := generated_sizes P f n Q
  simp only [segment_length] at h
  have hs1 := Nat.le_trans hw.1 (Nat.mul_le_mul_left _ hs.1)
  have hs2 := Nat.le_trans hw.2 (Nat.mul_le_mul_left _ hs.2)
  simp only [P1Events.solve,OfflineJoin.run,segment_length]
  refine ⟨Nat.le_trans h.1 ?_,Nat.le_trans h.2.1 ?_,h.2.2.1⟩
  · exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
      (Nat.add_le_add hs1 (Nat.mul_le_mul_left _ hs2)))
  · exact Nat.mul_le_mul_left _ (Nat.add_le_add hs.1 hs.2)

end REWB.SmallPeriodP1
