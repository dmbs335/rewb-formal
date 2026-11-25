import REWB.MaskedClusterMutableStoreInstall

/-! Counters for the actual located repair. One request performs at most
    one bank compilation and one slot replacement. Source fanout work is
    counted separately and added back in the combined bound. The per-bank
    bound uses actual compiler geometry and maintained source-tree height,
    not a supplied query-cost oracle. Fixed-pattern formula/catalog/action
    construction retains the separate accounting of the base compiler.
-/
namespace REWB.MaskedCluster.Mutable.Store
variable {α : Type} {h : Nat}

theorem rebuild_counts (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (target : Array Bool) (first : Nat) (st : State C E) :
    (rebuild C E book prepared ci ei target first st).rebuilds≤st.rebuilds+1 ∧
      (rebuild C E book prepared ci ei target first st).writes≤st.writes+1 ∧
      (rebuild C E book prepared ci ei target first st).slots.size=st.slots.size := by
  unfold rebuild
  split
  · exact ⟨Nat.le_refl _,Nat.le_refl _,by simp only [Array.size_setIfInBounds]⟩
  · dsimp only
    exact ⟨by omega,by omega,rfl⟩

theorem eraseSource_counts (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (partition : MaskedClusterLeaders.State h) (capacity : Nat) (target : Array Bool) (p : Nat)
    (st : State C E) :
    (eraseSource C E book prepared ci ei partition capacity target p st).rebuilds≤st.rebuilds+1 ∧
      (eraseSource C E book prepared ci ei partition capacity target p st).writes≤st.writes+1 ∧
      (eraseSource C E book prepared ci ei partition capacity target p st).slots.size=st.slots.size := by
  cases ho : (MaskedClusterDescriptor.locate partition capacity p).1 with
  | none =>
    simp only [eraseSource,ho]
    exact ⟨by omega,by omega,True.intro⟩
  | some first => simpa only [eraseSource,ho] using (rebuild_counts C E book prepared ci ei target first
      {st with
        sources:=MaskedMutableProgression.Batch.eraseSource p st.sources
        repairWork:=st.repairWork+(MaskedClusterDescriptor.locate partition capacity p).2+2})

/-- Proof-only name for the one compilation actually selected by the
    locator and stored entry. This is not a second executable traversal. -/
def selectedBankWork (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (partition : MaskedClusterLeaders.State h) (capacity : Nat) (target : Array Bool) (p : Nat)
    (st : State C E) : Nat :=
  match (MaskedClusterDescriptor.locate partition capacity p).1 with
  | none => 0
  | some first =>
    match st.slots[first]? with
    | some (some entry) => (compile C E book prepared ci ei (MaskedMutableProgression.Batch.eraseSource p st.sources)
        target entry.config).2
    | _ => 0

theorem eraseSource_work (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (partition : MaskedClusterLeaders.State h) (capacity : Nat) (target : Array Bool) (p : Nat)
    (st : State C E) :
    (eraseSource C E book prepared ci ei partition capacity target p st).repairWork≤
      st.repairWork+(11*h+19)+selectedBankWork C E book prepared ci ei partition capacity target p st := by
  have hl:=MaskedClusterDescriptor.locate_work partition capacity p
  cases ho : (MaskedClusterDescriptor.locate partition capacity p).1 with
  | none => simp only [eraseSource,selectedBankWork,ho]; omega
  | some first =>
    simp only [eraseSource,selectedBankWork,ho,rebuild]
    cases hs : st.slots[first]? with
    | none => simp only [hs]; omega
    | some slot => cases slot <;> simp only [hs] <;> omega

structure Geometry (cfg : Config) (n : Nat) : Prop where
  current : cfg.length≤cfg.anchor
  period : cfg.descriptor.repetitions≠0→cfg.descriptor.period≤cfg.anchor
  penultimate : cfg.descriptor.repetitions≠0→
    cfg.descriptor.first+(cfg.descriptor.repetitions-1)*cfg.descriptor.period+cfg.anchor≤cfg.descriptor.nextAt n
  separated : cfg.descriptor.first+cfg.descriptor.repetitions*cfg.descriptor.period<cfg.descriptor.nextAt n
  nextBound : cfg.descriptor.nextAt n≤n
  endBound : cfg.descriptor.first+cfg.descriptor.repetitions*cfg.descriptor.period+cfg.anchor≤n
  incoming : cfg.incomingEnabled=true→cfg.descriptor.first<cfg.incoming ∧
    cfg.incoming≤if cfg.descriptor.repetitions=0 then cfg.descriptor.nextAt n else cfg.descriptor.first+cfg.descriptor.period

theorem rowBudget_mono (C E : DFA α) (K a b : Nat) (hab : a≤b) :
    Mutable.rowBudget C E K a≤Mutable.rowBudget C E K b := by
  have hh:=Nat.mul_le_mul_right (K*(max C.stateCount E.stateCount*max C.stateCount E.stateCount))
    (show 7*a+73≤7*b+73 by omega)
  unfold Mutable.rowBudget cellBudget
  apply Nat.max_le.mpr
  constructor
  · exact Nat.le_trans (by omega) (Nat.le_max_left _ _)
  · exact Nat.le_trans (by omega) (Nat.le_max_right _ _)

theorem denseBankBudget_mono (C E : DFA α) (K a b : Nat) (hab : a≤b) :
    denseBankBudget C E K a≤denseBankBudget C E K b := by
  have hr:=rowBudget_mono C E K a b hab
  have hm:=Nat.mul_le_mul_left 4 (Nat.mul_le_mul_left (1+C.stateCount+E.stateCount)
    (Nat.mul_le_mul_left (1+C.stateCount+E.stateCount) (Nat.add_le_add_right hr 1)))
  unfold denseBankBudget
  apply Nat.mul_le_mul_left
  omega

theorem pointBankBudget_mono (C E : DFA α) (a b : Nat) (hab : a≤b) :
    pointBankBudget C E a≤pointBankBudget C E b := by
  have hm:=Nat.mul_le_mul_left 4 (Nat.mul_le_mul_left (1+C.stateCount+E.stateCount)
    (Nat.mul_le_mul_left (1+C.stateCount+E.stateCount) (show 4*a+31≤4*b+31 by omega)))
  unfold pointBankBudget
  apply Nat.mul_le_mul_left
  omega

def bankLimit (C E : DFA α) (K n : Nat) : Nat :=
  2*denseRowPrepBudget C E n+2*pointRowPrepBudget C E n+
    (C.stateCount+E.stateCount+16*(Nat.log2 n+2)+6)+
    denseBankBudget C E K (MaskedMutableProgression.height (n+1))+
    pointBankBudget C E (MaskedMutableProgression.height (n+1))+21

theorem compile_work (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount) (w : Word α)
    (source : Array Bool) (removed : List Nat) (sources : Batch.Sources)
    (hv : MaskedMutableProgression.Batch.Valid source removed sources) (hn : sources.n=w.length)
    (target : Array Bool) (cfg : Config) (hg : Geometry cfg w.length) :
    (compile C E book prepared (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
      sources target cfg).2≤bankLimit C E prepared.K w.length := by
  by_cases hm : cfg.descriptor.repetitions=0
  · have hs : cfg.descriptor.first<cfg.descriptor.nextAt w.length := by
      have hh:=hg.separated
      simpa only [hm,Nat.zero_mul,Nat.add_zero] using hh
    have hb : cfg.descriptor.first+cfg.anchor≤w.length := by
      have hh:=hg.endBound
      simpa only [hm,Nat.zero_mul,Nat.add_zero] using hh
    have hin : cfg.incomingEnabled=true→cfg.descriptor.first<cfg.incoming ∧ cfg.incoming≤cfg.descriptor.nextAt w.length := by
      intro he
      simpa only [hm,if_true] using hg.incoming he
    have hw:=Batch.compileSingleton_work C E book w sources cfg.descriptor.first cfg.length cfg.anchor
      (cfg.descriptor.nextAt w.length) cfg.incoming cfg.incomingEnabled target cfg.window hg.current hs hg.nextBound hb hin
    rw [hv.singleton.sized,hv.singleton.len_eq,hn] at hw
    simp only [compile,hm,if_true,hn]
    unfold bankLimit
    omega
  · simp only [compile,hm,if_false,hn]
    cases hid : cfg.runId with
    | none => simp only; unfold bankLimit; omega
    | some id =>
      simp only
      cases hR : sources.runs[id]? with
      | none => simp only [hR]; unfold bankLimit; omega
      | some R =>
        simp only [hR]
        by_cases hc : R.period=cfg.descriptor.period ∧ R.lo≤cfg.descriptor.first ∧ cfg.descriptor.last+cfg.anchor≤R.hi+1
        · simp only [hc,if_true,true_and]
          by_cases hK : sources.modulus=prepared.K
          · obtain ⟨idx,hidx,ht⟩:=hv.rows id R hR
            rw [Batch.compileRun_lookup C E book prepared _ _ sources id cfg.descriptor.first cfg.descriptor.repetitions
              cfg.length cfg.anchor (cfg.descriptor.nextAt w.length) cfg.incoming cfg.incomingEnabled target cfg.targetCounts
              cfg.window R idx hK hR hidx]
            have hp : R.period≤cfg.anchor := by rw [hc.1]; exact hg.period hm
            have hpen : cfg.descriptor.first+(cfg.descriptor.repetitions-1)*R.period+cfg.anchor≤cfg.descriptor.nextAt w.length := by
              rw [hc.1]; exact hg.penultimate hm
            have hsep : cfg.descriptor.first+cfg.descriptor.repetitions*R.period<cfg.descriptor.nextAt w.length := by
              rw [hc.1]; exact hg.separated
            have hend : cfg.descriptor.first+cfg.descriptor.repetitions*R.period+cfg.anchor≤w.length := by
              rw [hc.1]; exact hg.endBound
            have hin : cfg.incomingEnabled=true→cfg.descriptor.first<cfg.incoming ∧ cfg.incoming≤cfg.descriptor.first+R.period := by
              intro he
              simpa only [hm,if_false,hc.1] using hg.incoming he
            have hw:=Mutable.compileDenseBank_work C E book prepared w cfg.descriptor.first R.period cfg.descriptor.repetitions
              cfg.length cfg.anchor (cfg.descriptor.nextAt w.length) cfg.incoming cfg.incomingEnabled idx target cfg.targetCounts
              cfg.window hp (by omega) hg.current hpen hsep hg.nextBound hend hin
            have hheight:=hv.rowsHeight id idx hidx
            rw [hn] at hheight
            have hcap:=denseBankBudget_mono C E prepared.K idx.levels (MaskedMutableProgression.height (w.length+1)) hheight
            simp only [true_and,if_true]
            unfold bankLimit
            omega
          · simp only [Batch.compileRun,hK,if_false,true_and,if_true]; unfold bankLimit; omega
        · simp only [hc,if_false]; unfold bankLimit; omega

theorem selectedBankWork_bound (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount) (w : Word α)
    (partition : MaskedClusterLeaders.State h) (capacity : Nat) (target : Array Bool) (p : Nat) (st : State C E)
    (source : Array Bool) (removed : List Nat) (hv : MaskedMutableProgression.Batch.Valid source removed st.sources)
    (hn : st.sources.n=w.length)
    (hg : ∀(first : Nat) (entry : Entry C E),st.slots[first]?=some (some entry)→Geometry entry.config w.length) :
    selectedBankWork C E book prepared (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
      partition capacity target p st≤bankLimit C E prepared.K w.length := by
  cases ho : (MaskedClusterDescriptor.locate partition capacity p).1 with
  | none => simp only [selectedBankWork,ho]; exact Nat.zero_le _
  | some first =>
    simp only [selectedBankWork,ho]
    cases hs : st.slots[first]? with
    | none => exact Nat.zero_le _
    | some slot =>
      cases slot with
      | none => exact Nat.zero_le _
      | some entry =>
        exact compile_work C E book prepared w source (p::removed) _ (MaskedMutableProgression.Batch.eraseSource_valid hv p)
          hn target entry.config (hg first entry hs)

theorem eraseSource_combined_work (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount) (w : Word α)
    (partition : MaskedClusterLeaders.State h) (capacity : Nat) (target : Array Bool) (p : Nat) (st : State C E)
    (source : Array Bool) (removed : List Nat) (hv : MaskedMutableProgression.Batch.Valid source removed st.sources)
    (hn : st.sources.n=w.length)
    (hg : ∀(first : Nat) (entry : Entry C E),st.slots[first]?=some (some entry)→Geometry entry.config w.length) :
    let next:=eraseSource C E book prepared (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
      partition capacity target p st
    next.repairWork+next.sources.updateWork≤st.repairWork+st.sources.updateWork+
      (11*h+19)+bankLimit C E prepared.K w.length+MaskedMutableProgression.Batch.requestBudget w.length+
      (MaskedSourceFanout.take p st.sources.sources).1.count*MaskedMutableProgression.Batch.rowBudget w.length := by
  have hw:=eraseSource_work C E book prepared (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
    partition capacity target p st
  have hb:=selectedBankWork_bound C E book prepared w partition capacity target p st source removed hv hn hg
  have hs:=MaskedMutableProgression.Batch.eraseSource_work hv p
  rw [hn] at hs
  dsimp only
  rw [eraseSource_sources]
  omega

end REWB.MaskedCluster.Mutable.Store
