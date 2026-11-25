import REWB.MaskedClusterCut

/-! The shared-cut selector applied to actual dense and singleton
    cursor banks. One unchanged-geometry interval has one old local
    anchor, one immutable pair of masks, and one representative old word.
    Every shorter L uses its own physical skip and the B prefix from that
    very same cut. This is local cursor semantics, not yet a theorem that
    an arbitrary assembled cluster sequence covers every masked match.
-/
namespace REWB.MaskedCluster.Cut
open REWB.MaskedFiniteAction
variable {α : Type} {m : Nat}

/-- The second returned counter is the actual number of written replay
    vector entries when projecting the chosen source component. -/
def queryBank (B C E : DFA α) (idx : Shared B C E)
    (bank : Table (2*ReplayMaps.count C.stateCount E.stateCount) m) (gate : Bool)
    (representative lo hi old : Nat) (i j : Fin m) : Result×Nat :=
  let component:=bankComponent bank gate
  (query B C E idx component.1 representative lo hi old i j,component.2)

theorem queryBank_entries (B C E : DFA α) (idx : Shared B C E)
    (bank : Table (2*ReplayMaps.count C.stateCount E.stateCount) m) (gate : Bool)
    (representative lo hi old : Nat) (i j : Fin m) :
    (queryBank B C E idx bank gate representative lo hi old i j).2=ReplayMaps.count C.stateCount E.stateCount := rfl

theorem queryBank_correct (B C E : DFA α) (w : Word α)
    (bank : Table (2*ReplayMaps.count C.stateCount E.stateCount) m) (gate : Bool)
    (representative lo hi old : Nat) (i j : Fin m)
    (hlo : lo≤hi) (hhi : hi≤old) (hn : representative+old≤w.length) :
    (queryBank B C E (build B C E w) bank gate representative lo hi old i j).1.answer=true ↔
      ∃ L,lo≤L ∧ L≤hi ∧ B.accepts (Spec.slice w representative (representative+L)) ∧
        bank.view (code _ gate (ReplayMaps.encode (ReplayMaps.word C E
          (Spec.slice w (representative+L) (representative+old))))) i j=true := by
  simpa only [queryBank,bankComponent_view] using
    query_correct B C E w (bankComponent bank gate).1 representative lo hi old i j hlo hhi hn

theorem queryBank_bounds (B C E : DFA α) (w : Word α)
    (bank : Table (2*ReplayMaps.count C.stateCount E.stateCount) m) (gate : Bool)
    (representative lo hi old : Nat) (i j : Fin m) :
    (queryBank B C E (build B C E w) bank gate representative lo hi old i j).1.products≤3 ∧
    (queryBank B C E (build B C E w) bank gate representative lo hi old i j).1.visits≤3*(Nat.log2 w.length+2) ∧
    (queryBank B C E (build B C E w) bank gate representative lo hi old i j).1.tupleProbes≤
      (MaskedCut.DFAIndex.jointEnum B C E).elems.length*(MaskedCut.DFAIndex.jointEnum B C E).elems.length ∧
    (queryBank B C E (build B C E w) bank gate representative lo hi old i j).1.arithmetic≤8 :=
  query_bounds B C E w (bankComponent bank gate).1 representative lo hi old i j

theorem query_denseBank_correct (B C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount) (w : Word α) (fallback : α)
    (representative classBase lo hi old : Nat) (copies : List Nat)
    (s q m H next incoming : Nat) (previous following : Option Nat)
    (enabled gate inMode outMode : Bool) (source target : Array Bool) (base len : Nat) (window : SourceWindow)
    (i j : Fin (MaskedClusterStage.dfa C E).stateCount)
    (cert : MaskedLocalAnchor.Certificate (ArrayText.read w.toArray fallback) w.length
      classBase old copies (s+m*q) next previous following H)
    (hlo : lo≤hi) (hhi : hi≤old) (hrep : representative+old≤w.length)
    (hcopy : Spec.slice w representative (representative+old)=Spec.slice w s (s+old))
    (hmode : ∀ L,lo≤L→L≤hi→(next<s+m*q+old ↔ next<s+m*q+L))
    (hq : 0<q) (hm : 0<m) (hd : 2*q≤lo) (hmem : ∀ k,k≤m→s+k*q∈copies)
    (hprev : previous=some (s+(m-1)*q)) (hsep : s+m*q<next) (hnext : next≤w.length)
    (hin : enabled=true→s<incoming ∧ incoming≤s+q) (hbase : base≤s) (hend : s+m*q+H≤base+len) :
    (queryBank B C E (build B C E w)
      (compileDenseBank C E book prepared (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
        s q m old H next incoming enabled source target
        (MaskedProgression.build source base len (prepared.K*q)).counts
        (MaskedProgression.build target base len (prepared.K*q)).counts base window).1
      gate representative lo hi old (code _ inMode i) (code _ outMode j)).1.answer=true ↔
        ∃ L,lo≤L ∧ L≤hi ∧ B.accepts (Spec.slice w representative (representative+L)) ∧
          CursorStep C E w s q m L H next incoming enabled inMode outMode source target (window.gate gate)
            (MaskedClusterStage.decode C E i) (MaskedClusterStage.decode C E j) := by
  rw [queryBank_correct B C E w _ gate representative lo hi old _ _ hlo hhi hrep]
  have hstart : s+H≤w.length := by have hh:=cert.lastBound; omega
  have hcell (L : Nat) (hl : lo≤L) (hh : L≤hi) :
      (compileDenseBank C E book prepared (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
        s q m old H next incoming enabled source target
        (MaskedProgression.build source base len (prepared.K*q)).counts
        (MaskedProgression.build target base len (prepared.K*q)).counts base window).1.view
        (code _ gate (ReplayMaps.encode (ReplayMaps.word C E (Spec.slice w (representative+L) (representative+old)))))
        (code _ inMode i) (code _ outMode j)=true ↔
      CursorStep C E w s q m L H next incoming enabled inMode outMode source target (window.gate gate)
        (MaskedClusterStage.decode C E i) (MaskedClusterStage.decode C E j) := by
    rw [compileDenseBank_select_shorter C E book prepared w representative s q m L old H next incoming enabled gate
      source target _ _ base window _ _ (by omega) cert.current hrep hstart hcopy]
    exact compileDenseBank_current C E book prepared w fallback classBase L copies s q m H next incoming previous following
      enabled gate inMode outMode source target base len window i j
      (MaskedLocalAnchor.shorten _ _ classBase old L copies _ _ previous following H cert (by omega) (hmode L hl hh))
      hq hm (by omega) hmem hprev hsep hnext hin hbase hend
  constructor
  · rintro ⟨L,hl,hh,hB,hcell'⟩
    exact ⟨L,hl,hh,hB,(hcell L hl hh).mp hcell'⟩
  · rintro ⟨L,hl,hh,hB,hcell'⟩
    exact ⟨L,hl,hh,hB,(hcell L hl hh).mpr hcell'⟩

theorem query_pointBank_correct (B C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (w : Word α) (fallback : α) (representative classBase lo hi old : Nat) (copies : List Nat)
    (s H next incoming : Nat) (previous following : Option Nat)
    (enabled gate inMode outMode : Bool) (source target : Array Bool) (window : SourceWindow)
    (i j : Fin (MaskedClusterStage.dfa C E).stateCount)
    (cert : MaskedLocalAnchor.Certificate (ArrayText.read w.toArray fallback) w.length
      classBase old copies s next previous following H)
    (hlo : lo≤hi) (hhi : hi≤old) (hrep : representative+old≤w.length)
    (hcopy : Spec.slice w representative (representative+old)=Spec.slice w s (s+old))
    (hmode : ∀ L,lo≤L→L≤hi→(next<s+old ↔ next<s+L))
    (hsep : s<next) (hnext : next≤w.length) (hin : enabled=true→s<incoming ∧ incoming≤next) :
    (queryBank B C E (build B C E w)
      (compilePointBank C E book (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
        s old H next incoming enabled source target window).1
      gate representative lo hi old (code _ inMode i) (code _ outMode j)).1.answer=true ↔
        ∃ L,lo≤L ∧ L≤hi ∧ B.accepts (Spec.slice w representative (representative+L)) ∧
          CursorStep C E w s 1 0 L H next incoming enabled inMode outMode source target (window.gate gate)
            (MaskedClusterStage.decode C E i) (MaskedClusterStage.decode C E j) := by
  rw [queryBank_correct B C E w _ gate representative lo hi old _ _ hlo hhi hrep]
  have hcell (L : Nat) (hl : lo≤L) (hh : L≤hi) :
      (compilePointBank C E book (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
        s old H next incoming enabled source target window).1.view
        (code _ gate (ReplayMaps.encode (ReplayMaps.word C E (Spec.slice w (representative+L) (representative+old)))))
        (code _ inMode i) (code _ outMode j)=true ↔
      CursorStep C E w s 1 0 L H next incoming enabled inMode outMode source target (window.gate gate)
        (MaskedClusterStage.decode C E i) (MaskedClusterStage.decode C E j) := by
    rw [compilePointBank_select_shorter C E book w representative s L old H next incoming enabled gate source target
      window _ _ (by omega) cert.current hrep cert.lastBound hcopy]
    exact compilePointBank_current C E book w fallback classBase L copies s H next incoming previous following
      enabled gate inMode outMode source target window i j
      (MaskedLocalAnchor.shorten _ _ classBase old L copies _ _ previous following H cert (by omega) (hmode L hl hh))
      hsep hnext hin
  constructor
  · rintro ⟨L,hl,hh,hB,hcell'⟩
    exact ⟨L,hl,hh,hB,(hcell L hl hh).mp hcell'⟩
  · rintro ⟨L,hl,hh,hB,hcell'⟩
    exact ⟨L,hl,hh,hB,(hcell L hl hh).mpr hcell'⟩

end REWB.MaskedCluster.Cut
