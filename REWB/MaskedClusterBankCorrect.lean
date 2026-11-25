import REWB.MaskedClusterBank

/-! Real-text instances of the replay bank. Preparation reads the two
    cursor rows and the old local tail once; a fresh length is selected
    through the common representative's newly exposed suffix map.
    The statements retain actual local-anchor certificates and fixed
    immutable source/target masks. They do not assert a global repair
    policy or maintenance of already-reported-source deletions.
-/
namespace REWB.MaskedCluster
open REWB.MaskedFiniteAction
variable {α : Type}

def compileDenseBank (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (s q m L H next incoming : Nat) (enabled : Bool) (source target : Array Bool)
    (sourceCounts targetCounts : Array Nat) (base : Nat) (window : SourceWindow) :
    Table (2*ReplayMaps.count C.stateCount E.stateCount) (2*(MaskedClusterStage.dfa C E).stateCount)×Nat :=
  let rows:=prepareRows C E ci ei s q m H next incoming enabled
  let tail:=replay C E ci ei s L H
  let out:=denseBank C E book prepared rows.1 tail.maps source target sourceCounts targetCounts base window
  (out.1,rows.2+tail.work+out.2+3)

def compilePointBank (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (s L H next incoming : Nat) (enabled : Bool) (source target : Array Bool) (window : SourceWindow) :
    Table (2*ReplayMaps.count C.stateCount E.stateCount) (2*(MaskedClusterStage.dfa C E).stateCount)×Nat :=
  let rows:=preparePointRows C E ci ei s H next incoming enabled
  let tail:=replay C E ci ei s L H
  let out:=pointBank C E book rows.1 tail.maps source target window
  (out.1,rows.2+tail.work+out.2+3)

theorem compileDenseBank_current (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (w : Word α) (fallback : α) (classBase L : Nat) (copies : List Nat)
    (s q m H next incoming : Nat) (previous following : Option Nat)
    (enabled gate inMode outMode : Bool) (source target : Array Bool) (base len : Nat) (window : SourceWindow)
    (i j : Fin (MaskedClusterStage.dfa C E).stateCount)
    (cert : MaskedLocalAnchor.Certificate (ArrayText.read w.toArray fallback) w.length
      classBase L copies (s+m*q) next previous following H)
    (hq : 0<q) (hm : 0<m) (hd : 2*q≤L) (hmem : ∀ k,k≤m→s+k*q∈copies)
    (hprev : previous=some (s+(m-1)*q)) (hsep : s+m*q<next) (hnext : next≤w.length)
    (hin : enabled=true→s<incoming ∧ incoming≤s+q) (hbase : base≤s) (hend : s+m*q+H≤base+len) :
    (compileDenseBank C E book prepared (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
      s q m L H next incoming enabled source target
      (MaskedProgression.build source base len (prepared.K*q)).counts
      (MaskedProgression.build target base len (prepared.K*q)).counts base window).1.view
      (code _ gate (ReplayMaps.encode (ReplayMaps.one C.stateCount E.stateCount)))
      (code _ inMode i) (code _ outMode j)=true ↔
        CursorStep C E w s q m L H next incoming enabled inMode outMode source target (window.gate gate)
          (MaskedClusterStage.decode C E i) (MaskedClusterStage.decode C E j) := by
  simp only [compileDenseBank,denseBank,tabulate_select,ReplayMaps.one_mul]
  exact compileDense_correct C E prepared w fallback classBase L copies s q m H next incoming previous following
    enabled source target base len (window.gate gate) cert hq hm hd hmem hprev hsep hnext hin hbase hend
    inMode outMode i j

theorem compilePointBank_current (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (w : Word α) (fallback : α) (classBase L : Nat) (copies : List Nat)
    (s H next incoming : Nat) (previous following : Option Nat)
    (enabled gate inMode outMode : Bool) (source target : Array Bool) (window : SourceWindow)
    (i j : Fin (MaskedClusterStage.dfa C E).stateCount)
    (cert : MaskedLocalAnchor.Certificate (ArrayText.read w.toArray fallback) w.length
      classBase L copies s next previous following H)
    (hsep : s<next) (hnext : next≤w.length) (hin : enabled=true→s<incoming ∧ incoming≤next) :
    (compilePointBank C E book (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
      s L H next incoming enabled source target window).1.view
      (code _ gate (ReplayMaps.encode (ReplayMaps.one C.stateCount E.stateCount)))
      (code _ inMode i) (code _ outMode j)=true ↔
        CursorStep C E w s 1 0 L H next incoming enabled inMode outMode source target (window.gate gate)
          (MaskedClusterStage.decode C E i) (MaskedClusterStage.decode C E j) := by
  simp only [compilePointBank,pointBank,tabulate_select,ReplayMaps.one_mul]
  exact compilePoint_correct C E w fallback classBase L copies s H next incoming previous following enabled
    source target (window.gate gate) cert hsep hnext hin inMode outMode i j

theorem compileDenseBank_reindex (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount) (w : Word α)
    (representative s q m fresh old H next incoming : Nat) (enabled : Bool)
    (source target : Array Bool) (sourceCounts targetCounts : Array Nat) (base : Nat) (window : SourceWindow)
    (hnew : fresh≤old) (hH : old≤H) (hrep : representative+old≤w.length) (hstart : s+H≤w.length)
    (hcopy : Spec.slice w representative (representative+old)=Spec.slice w s (s+old)) :
    (Counted.reindex (bankAction
      (replay C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w) representative fresh old).maps)
      (compileDenseBank C E book prepared (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
        s q m old H next incoming enabled source target sourceCounts targetCounts base window).1).1.view=
      (compileDenseBank C E book prepared (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
        s q m fresh H next incoming enabled source target sourceCounts targetCounts base window).1.view := by
  simp only [compileDenseBank,denseBank_reindex]
  rw [←ReplayMaps.replay_common_shortening C E w representative s fresh old H hnew hH hrep hstart hcopy]

theorem compilePointBank_reindex (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount) (w : Word α)
    (representative s fresh old H next incoming : Nat) (enabled : Bool)
    (source target : Array Bool) (window : SourceWindow)
    (hnew : fresh≤old) (hH : old≤H) (hrep : representative+old≤w.length) (hstart : s+H≤w.length)
    (hcopy : Spec.slice w representative (representative+old)=Spec.slice w s (s+old)) :
    (Counted.reindex (bankAction
      (replay C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w) representative fresh old).maps)
      (compilePointBank C E book (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
        s old H next incoming enabled source target window).1).1.view=
      (compilePointBank C E book (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
        s fresh H next incoming enabled source target window).1.view := by
  simp only [compilePointBank,pointBank_reindex]
  rw [←ReplayMaps.replay_common_shortening C E w representative s fresh old H hnew hH hrep hstart hcopy]

theorem reindex_select_one {c e m : Nat} (a : Table (2*ReplayMaps.count c e) m)
    (z : ReplayMaps.Value c e) (gate : Bool) (i j : Fin m) :
    (Counted.reindex (bankAction z) a).1.view
      (code _ gate (ReplayMaps.encode (ReplayMaps.one c e))) i j=
      a.view (code _ gate (ReplayMaps.encode z)) i j := by
  simp only [Counted.reindex_view,View.reindex,bankAction_get,codeMode_code,codeState_code,
    ReplayMaps.rightAction_get,ReplayMaps.decode_encode,ReplayMaps.one_mul]

/-- Selecting a common newly exposed prefix in the old bank is exactly
    the same cell as selecting identity in the freshly shortened bank. -/
theorem compileDenseBank_select_shorter (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount) (w : Word α)
    (representative s q m fresh old H next incoming : Nat) (enabled gate : Bool)
    (source target : Array Bool) (sourceCounts targetCounts : Array Nat) (base : Nat) (window : SourceWindow)
    (i j : Fin (2*(MaskedClusterStage.dfa C E).stateCount))
    (hnew : fresh≤old) (hH : old≤H) (hrep : representative+old≤w.length) (hstart : s+H≤w.length)
    (hcopy : Spec.slice w representative (representative+old)=Spec.slice w s (s+old)) :
    (compileDenseBank C E book prepared (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
      s q m old H next incoming enabled source target sourceCounts targetCounts base window).1.view
      (code _ gate (ReplayMaps.encode (ReplayMaps.word C E (Spec.slice w (representative+fresh) (representative+old))))) i j=
    (compileDenseBank C E book prepared (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
      s q m fresh H next incoming enabled source target sourceCounts targetCounts base window).1.view
      (code _ gate (ReplayMaps.encode (ReplayMaps.one C.stateCount E.stateCount))) i j := by
  have he:=compileDenseBank_reindex C E book prepared w representative s q m fresh old H next incoming enabled
    source target sourceCounts targetCounts base window hnew hH hrep hstart hcopy
  have hh:=congrFun (congrFun (congrFun he
    (code _ gate (ReplayMaps.encode (ReplayMaps.one C.stateCount E.stateCount)))) i) j
  rw [reindex_select_one,replay_value C E w representative fresh old hnew hrep] at hh
  exact hh

theorem compilePointBank_select_shorter (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (w : Word α) (representative s fresh old H next incoming : Nat) (enabled gate : Bool)
    (source target : Array Bool) (window : SourceWindow) (i j : Fin (2*(MaskedClusterStage.dfa C E).stateCount))
    (hnew : fresh≤old) (hH : old≤H) (hrep : representative+old≤w.length) (hstart : s+H≤w.length)
    (hcopy : Spec.slice w representative (representative+old)=Spec.slice w s (s+old)) :
    (compilePointBank C E book (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
      s old H next incoming enabled source target window).1.view
      (code _ gate (ReplayMaps.encode (ReplayMaps.word C E (Spec.slice w (representative+fresh) (representative+old))))) i j=
    (compilePointBank C E book (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
      s fresh H next incoming enabled source target window).1.view
      (code _ gate (ReplayMaps.encode (ReplayMaps.one C.stateCount E.stateCount))) i j := by
  have he:=compilePointBank_reindex C E book w representative s fresh old H next incoming enabled
    source target window hnew hH hrep hstart hcopy
  have hh:=congrFun (congrFun (congrFun he
    (code _ gate (ReplayMaps.encode (ReplayMaps.one C.stateCount E.stateCount)))) i) j
  rw [reindex_select_one,replay_value C E w representative fresh old hnew hrep] at hh
  exact hh

end REWB.MaskedCluster
