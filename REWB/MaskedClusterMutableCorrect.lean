import REWB.MaskedClusterMutableBank

/-! Physical correctness for rebuilt mutable-source banks and their
    shared-cut length queries. The source snapshot is explicit; neither
    theorem assumes that an old cached bank changes after an erase.
-/
namespace REWB.MaskedCluster.Mutable
variable {α : Type}

theorem compileDenseBank_current (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (w : Word α) (fallback : α) (classBase L : Nat) (copies : List Nat)
    (s q m H next incoming : Nat) (previous following : Option Nat)
    (enabled gate inMode outMode : Bool) (idx : Index) (hv : idx.Valid) (target : Array Bool) (window : SourceWindow)
    (i j : Fin (MaskedClusterStage.dfa C E).stateCount)
    (cert : MaskedLocalAnchor.Certificate (ArrayText.read w.toArray fallback) w.length
      classBase L copies (s+m*q) next previous following H)
    (hq : 0<q) (hm : 0<m) (hd : 2*q≤L) (hmem : ∀ k,k≤m→s+k*q∈copies)
    (hprev : previous=some (s+(m-1)*q)) (hsep : s+m*q<next) (hnext : next≤w.length)
    (hin : enabled=true→s<incoming ∧ incoming≤s+q) (hbase : idx.base≤s) (hend : s+m*q+H≤idx.base+idx.len)
    (hstep : idx.step=prepared.K*q) :
    (compileDenseBank C E book prepared (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
      s q m L H next incoming enabled idx target
      (MaskedProgression.build target idx.base idx.len (prepared.K*q)).counts window).1.view
      (code _ gate (ReplayMaps.encode (ReplayMaps.one C.stateCount E.stateCount)))
      (code _ inMode i) (code _ outMode j)=true ↔
        CursorStep C E w s q m L H next incoming enabled inMode outMode idx target (window.gate gate)
          (MaskedClusterStage.decode C E i) (MaskedClusterStage.decode C E j) := by
  rw [compileDenseBank_snapshot C E book prepared _ _ s q m L H next incoming enabled idx hv target _ window hq hstep,hstep]
  exact (REWB.MaskedCluster.compileDenseBank_current C E book prepared w fallback classBase L copies s q m H next incoming
    previous following enabled gate inMode outMode (snapshot idx) target idx.base idx.len window i j cert
    hq hm hd hmem hprev hsep hnext hin hbase hend).trans
    (cursorStep_snapshot C E w s q m L H next incoming enabled inMode outMode idx target (window.gate gate) _ _)

theorem compilePointBank_current (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (w : Word α) (fallback : α) (classBase L : Nat) (copies : List Nat)
    (s H next incoming : Nat) (previous following : Option Nat)
    (enabled gate inMode outMode : Bool) (idx : Index) (target : Array Bool) (window : SourceWindow)
    (i j : Fin (MaskedClusterStage.dfa C E).stateCount)
    (cert : MaskedLocalAnchor.Certificate (ArrayText.read w.toArray fallback) w.length
      classBase L copies s next previous following H)
    (hsep : s<next) (hnext : next≤w.length) (hin : enabled=true→s<incoming ∧ incoming≤next) :
    (compilePointBank C E book (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
      s L H next incoming enabled idx target window).1.view
      (code _ gate (ReplayMaps.encode (ReplayMaps.one C.stateCount E.stateCount)))
      (code _ inMode i) (code _ outMode j)=true ↔
        CursorStep C E w s 1 0 L H next incoming enabled inMode outMode idx target (window.gate gate)
          (MaskedClusterStage.decode C E i) (MaskedClusterStage.decode C E j) := by
  rw [compilePointBank_snapshot]
  exact (REWB.MaskedCluster.compilePointBank_current C E book w fallback classBase L copies s H next incoming previous following
    enabled gate inMode outMode (snapshot idx) target window i j cert hsep hnext hin).trans
    (cursorStep_snapshot C E w s 1 0 L H next incoming enabled inMode outMode idx target (window.gate gate) _ _)

theorem query_denseBank_correct (B C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount) (w : Word α) (fallback : α)
    (representative classBase lo hi old : Nat) (copies : List Nat)
    (s q m H next incoming : Nat) (previous following : Option Nat)
    (enabled gate inMode outMode : Bool) (idx : Index) (hv : idx.Valid) (target : Array Bool) (window : SourceWindow)
    (i j : Fin (MaskedClusterStage.dfa C E).stateCount)
    (cert : MaskedLocalAnchor.Certificate (ArrayText.read w.toArray fallback) w.length
      classBase old copies (s+m*q) next previous following H)
    (hlo : lo≤hi) (hhi : hi≤old) (hrep : representative+old≤w.length)
    (hcopy : Spec.slice w representative (representative+old)=Spec.slice w s (s+old))
    (hmode : ∀ L,lo≤L→L≤hi→(next<s+m*q+old ↔ next<s+m*q+L))
    (hq : 0<q) (hm : 0<m) (hd : 2*q≤lo) (hmem : ∀ k,k≤m→s+k*q∈copies)
    (hprev : previous=some (s+(m-1)*q)) (hsep : s+m*q<next) (hnext : next≤w.length)
    (hin : enabled=true→s<incoming ∧ incoming≤s+q) (hbase : idx.base≤s) (hend : s+m*q+H≤idx.base+idx.len)
    (hstep : idx.step=prepared.K*q) :
    (Cut.queryBank B C E (Cut.build B C E w)
      (compileDenseBank C E book prepared (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
        s q m old H next incoming enabled idx target
        (MaskedProgression.build target idx.base idx.len (prepared.K*q)).counts window).1
      gate representative lo hi old (code _ inMode i) (code _ outMode j)).1.answer=true ↔
        ∃ L,lo≤L ∧ L≤hi ∧ B.accepts (Spec.slice w representative (representative+L)) ∧
          CursorStep C E w s q m L H next incoming enabled inMode outMode idx target (window.gate gate)
            (MaskedClusterStage.decode C E i) (MaskedClusterStage.decode C E j) := by
  rw [compileDenseBank_snapshot C E book prepared _ _ s q m old H next incoming enabled idx hv target _ window hq hstep,hstep]
  have hh:=Cut.query_denseBank_correct B C E book prepared w fallback representative classBase lo hi old copies s q m H next
    incoming previous following enabled gate inMode outMode (snapshot idx) target idx.base idx.len window i j cert hlo hhi hrep
    hcopy hmode hq hm hd hmem hprev hsep hnext hin hbase hend
  simpa only [cursorStep_snapshot] using hh

theorem query_pointBank_correct (B C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (w : Word α) (fallback : α) (representative classBase lo hi old : Nat) (copies : List Nat)
    (s H next incoming : Nat) (previous following : Option Nat)
    (enabled gate inMode outMode : Bool) (idx : Index) (target : Array Bool) (window : SourceWindow)
    (i j : Fin (MaskedClusterStage.dfa C E).stateCount)
    (cert : MaskedLocalAnchor.Certificate (ArrayText.read w.toArray fallback) w.length
      classBase old copies s next previous following H)
    (hlo : lo≤hi) (hhi : hi≤old) (hrep : representative+old≤w.length)
    (hcopy : Spec.slice w representative (representative+old)=Spec.slice w s (s+old))
    (hmode : ∀ L,lo≤L→L≤hi→(next<s+old ↔ next<s+L))
    (hsep : s<next) (hnext : next≤w.length) (hin : enabled=true→s<incoming ∧ incoming≤next) :
    (Cut.queryBank B C E (Cut.build B C E w)
      (compilePointBank C E book (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
        s old H next incoming enabled idx target window).1
      gate representative lo hi old (code _ inMode i) (code _ outMode j)).1.answer=true ↔
        ∃ L,lo≤L ∧ L≤hi ∧ B.accepts (Spec.slice w representative (representative+L)) ∧
          CursorStep C E w s 1 0 L H next incoming enabled inMode outMode idx target (window.gate gate)
            (MaskedClusterStage.decode C E i) (MaskedClusterStage.decode C E j) := by
  rw [compilePointBank_snapshot]
  have hh:=Cut.query_pointBank_correct B C E book w fallback representative classBase lo hi old copies s H next incoming
    previous following enabled gate inMode outMode (snapshot idx) target window i j cert hlo hhi hrep hcopy hmode hsep hnext hin
  simpa only [cursorStep_snapshot] using hh

end REWB.MaskedCluster.Mutable
