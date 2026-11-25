import REWB.MaskedClusterMutableBatch

/-! Physical correctness of actual batch row selection after an arbitrary
    erase history. The returned bank is about original source membership
    minus that history and the unchanged target mask. Local geometry and
    once-prepared immutable target counts remain explicit inputs.
-/
namespace REWB.MaskedCluster.Mutable.Batch
open REWB.RunGeometry
open REWB.MaskedPeriodic.Batch (span)
variable {α : Type}

theorem compileRun_current (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount) (w : Word α) (fallback : α)
    (source : Array Bool) (removed : List Nat) (sources : Sources)
    (hv : MaskedMutableProgression.Batch.Valid source removed sources)
    (id : Nat) (R : Bounds) (hR : sources.runs[id]?=some R) (hK : sources.modulus=prepared.K)
    (classBase L : Nat) (copies : List Nat) (s m H next incoming : Nat) (previous following : Option Nat)
    (enabled gate inMode outMode : Bool) (target : Array Bool) (window : SourceWindow)
    (i j : Fin (MaskedClusterStage.dfa C E).stateCount)
    (cert : MaskedLocalAnchor.Certificate (ArrayText.read w.toArray fallback) w.length
      classBase L copies (s+m*R.period) next previous following H)
    (hm : 0<m) (hd : 2*R.period≤L) (hmem : ∀k,k≤m→s+k*R.period∈copies)
    (hprev : previous=some (s+(m-1)*R.period)) (hsep : s+m*R.period<next) (hnext : next≤w.length)
    (hin : enabled=true→s<incoming ∧ incoming≤s+R.period)
    (hbase : R.lo≤s) (hend : s+m*R.period+H≤R.hi+1) :
    (compileRun C E book prepared (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
      sources id s m L H next incoming enabled target
      (MaskedProgression.build target R.lo (span R) (prepared.K*R.period)).counts window).1.any
      (fun bank=>bank.view (code _ gate (ReplayMaps.encode (ReplayMaps.one C.stateCount E.stateCount)))
        (code _ inMode i) (code _ outMode j))=true ↔
      CursorStep C E w s R.period m L H next incoming enabled inMode outMode source removed target (window.gate gate)
        (MaskedClusterStage.decode C E i) (MaskedClusterStage.decode C E j) := by
  obtain ⟨idx,hidx,hs⟩:=hv.rows id R hR
  have hb:=hv.bounds id R hR
  have hstep : idx.step=prepared.K*R.period := by rw [hs.step_eq,hK]
  have hbase' : idx.base≤s := by rw [hs.base_eq]; exact hbase
  have hend' : s+m*R.period+H≤idx.base+idx.len := by
    rw [hs.base_eq,hs.len_eq]
    unfold span
    omega
  rw [compileRun_lookup C E book prepared _ _ sources id s m L H next incoming enabled target _ window R idx hK hR hidx]
  simp only [Option.any_some]
  have hc:=Mutable.compileDenseBank_current C E book prepared w fallback classBase L copies s R.period m H next incoming
    previous following enabled gate inMode outMode idx hs.good target window i j cert hb.2.2 hm hd hmem hprev hsep hnext
    hin hbase' hend' hstep
  rw [hs.base_eq,hs.len_eq] at hc
  apply hc.trans
  apply cursor_current C E w s R.period m L H next incoming enabled inMode outMode source removed target (window.gate gate)
    idx R.lo (span R) (sources.modulus*R.period) hs
  intro k hk
  have hkm:=Nat.mul_le_mul_right R.period hk
  have hLH:=cert.current
  unfold span
  constructor <;> omega

theorem compileSingleton_current (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (w : Word α) (fallback : α) (source : Array Bool) (removed : List Nat) (sources : Sources)
    (hv : MaskedMutableProgression.Batch.Valid source removed sources)
    (classBase L : Nat) (copies : List Nat) (s H next incoming : Nat) (previous following : Option Nat)
    (enabled gate inMode outMode : Bool) (target : Array Bool) (window : SourceWindow)
    (i j : Fin (MaskedClusterStage.dfa C E).stateCount)
    (cert : MaskedLocalAnchor.Certificate (ArrayText.read w.toArray fallback) w.length
      classBase L copies s next previous following H)
    (hsep : s<next) (hnext : next≤w.length) (hin : enabled=true→s<incoming ∧ incoming≤next)
    (hsource : s≤sources.n) :
    (compileSingleton C E book (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
      sources s L H next incoming enabled target window).1.view
      (code _ gate (ReplayMaps.encode (ReplayMaps.one C.stateCount E.stateCount)))
      (code _ inMode i) (code _ outMode j)=true ↔
      CursorStep C E w s 1 0 L H next incoming enabled inMode outMode source removed target (window.gate gate)
        (MaskedClusterStage.decode C E i) (MaskedClusterStage.decode C E j) := by
  unfold compileSingleton
  rw [Mutable.compilePointBank_current C E book w fallback classBase L copies s H next incoming previous following
    enabled gate inMode outMode sources.singleton target window i j cert hsep hnext hin]
  apply cursor_current C E w s 1 0 L H next incoming enabled inMode outMode source removed target (window.gate gate)
    sources.singleton 0 (sources.n+1) 1 hv.singleton
  intro k hk
  have hk0 : k=0 := by omega
  subst k
  simp only [Nat.zero_mul,Nat.add_zero,Nat.zero_add]
  exact ⟨Nat.zero_le _,by omega⟩

/-- Two lookups and scalar checks add nine units to the actually chosen
    current bank compiler; there is no scan over runs or source positions. -/
theorem compileRun_work (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount) (w : Word α)
    (source : Array Bool) (removed : List Nat) (sources : Sources)
    (hv : MaskedMutableProgression.Batch.Valid source removed sources)
    (id : Nat) (R : Bounds) (hR : sources.runs[id]?=some R) (hK : sources.modulus=prepared.K)
    (s m L H next incoming : Nat) (enabled : Bool) (target : Array Bool)
    (targetCounts : Array Nat) (window : SourceWindow)
    (hq : R.period≤H) (hm : 0<m) (hLH : L≤H) (hpen : s+(m-1)*R.period+H≤next)
    (hsep : s+m*R.period<next) (hnext : next≤w.length) (hbound : s+m*R.period+H≤w.length)
    (hin : enabled=true→s<incoming ∧ incoming≤s+R.period) :
    ∃idx,sources.indexes[id]?=some idx ∧ idx.LogSized ∧
      (compileRun C E book prepared (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
        sources id s m L H next incoming enabled target targetCounts window).2≤
        2*denseRowPrepBudget C E w.length+(C.stateCount+E.stateCount+16*(Nat.log2 w.length+2)+6)+
          denseBankBudget C E prepared.K idx.levels+12 := by
  obtain ⟨idx,hidx,hs⟩:=hv.rows id R hR
  refine ⟨idx,hidx,hs.sized,?_⟩
  rw [compileRun_lookup C E book prepared _ _ sources id s m L H next incoming enabled target targetCounts window R idx hK hR hidx]
  have hw:=Mutable.compileDenseBank_work C E book prepared w s R.period m L H next incoming enabled idx target targetCounts
    window hq hm hLH hpen hsep hnext hbound hin
  simp only
  omega

theorem compileSingleton_work (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (w : Word α) (sources : Sources) (s L H next incoming : Nat) (enabled : Bool)
    (target : Array Bool) (window : SourceWindow)
    (hLH : L≤H) (hsep : s<next) (hnext : next≤w.length) (hbound : s+H≤w.length)
    (hin : enabled=true→s<incoming ∧ incoming≤next) :
    (compileSingleton C E book (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
      sources s L H next incoming enabled target window).2≤
      2*pointRowPrepBudget C E w.length+(C.stateCount+E.stateCount+16*(Nat.log2 w.length+2)+6)+
        pointBankBudget C E sources.singleton.levels+4 := by
  have hw:=Mutable.compilePointBank_work C E book w s L H next incoming enabled sources.singleton target window
    hLH hsep hnext hbound hin
  simp only [compileSingleton]
  omega

end REWB.MaskedCluster.Mutable.Batch
