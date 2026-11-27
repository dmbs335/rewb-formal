import REWB.MaskedTraversalAggregateWindow

/-! Selecting one common replay key in an actual stored mutable bank is
exactly the current physical transition at the shorter length. This
lifts the dense/point compiler laws through the real run/slot adapters,
including their rejection branches; it does not posit a coherent-bank
answer oracle. Geometry and retained anchor certificates remain explicit.
-/
namespace REWB.MaskedTraversalAggregate
open REWB.MaskedCluster REWB.MaskedFiniteAction
variable {α : Type}

theorem dense_select_shorter (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount) (w : Word α)
    (representative s q m fresh old H next incoming : Nat) (enabled gate : Bool)
    (idx : Mutable.Index) (target : Array Bool) (targetCounts : Array Nat) (window : SourceWindow)
    (i j : Fin (2*(MaskedClusterStage.dfa C E).stateCount))
    (hnew : fresh≤old) (hH : old≤H) (hrep : representative+old≤w.length) (hstart : s+H≤w.length)
    (hcopy : Spec.slice w representative (representative+old)=Spec.slice w s (s+old)) :
    (Mutable.compileDenseBank C E book prepared (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
      s q m old H next incoming enabled idx target targetCounts window).1.view
      (code _ gate (ReplayMaps.encode (ReplayMaps.word C E (Spec.slice w (representative+fresh) (representative+old))))) i j=
    (Mutable.compileDenseBank C E book prepared (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
      s q m fresh H next incoming enabled idx target targetCounts window).1.view
      (code _ gate (ReplayMaps.encode (ReplayMaps.one C.stateCount E.stateCount))) i j := by
  have he:=Mutable.compileDenseBank_reindex C E book prepared w representative s q m fresh old H next incoming
    enabled idx target targetCounts window hnew hH hrep hstart hcopy
  have hh:=congrFun (congrFun (congrFun he
    (code _ gate (ReplayMaps.encode (ReplayMaps.one C.stateCount E.stateCount)))) i) j
  rw [reindex_select_one,replay_value C E w representative fresh old hnew hrep] at hh
  exact hh

theorem point_select_shorter (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (w : Word α) (representative s fresh old H next incoming : Nat) (enabled gate : Bool)
    (idx : Mutable.Index) (target : Array Bool) (window : SourceWindow)
    (i j : Fin (2*(MaskedClusterStage.dfa C E).stateCount))
    (hnew : fresh≤old) (hH : old≤H) (hrep : representative+old≤w.length) (hstart : s+H≤w.length)
    (hcopy : Spec.slice w representative (representative+old)=Spec.slice w s (s+old)) :
    (Mutable.compilePointBank C E book (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
      s old H next incoming enabled idx target window).1.view
      (code _ gate (ReplayMaps.encode (ReplayMaps.word C E (Spec.slice w (representative+fresh) (representative+old))))) i j=
    (Mutable.compilePointBank C E book (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
      s fresh H next incoming enabled idx target window).1.view
      (code _ gate (ReplayMaps.encode (ReplayMaps.one C.stateCount E.stateCount))) i j := by
  have he:=Mutable.compilePointBank_reindex C E book w representative s fresh old H next incoming
    enabled idx target window hnew hH hrep hstart hcopy
  have hh:=congrFun (congrFun (congrFun he
    (code _ gate (ReplayMaps.encode (ReplayMaps.one C.stateCount E.stateCount)))) i) j
  rw [reindex_select_one,replay_value C E w representative fresh old hnew hrep] at hh
  exact hh

def withLength (cfg : Mutable.Store.Config) (fresh : Nat) : Mutable.Store.Config :=
  {cfg with length:=fresh}

theorem store_select_shorter (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount) (w : Word α)
    (sources : Mutable.Batch.Sources) (target : Array Bool) (cfg : Mutable.Store.Config)
    (representative fresh : Nat) (gate : Bool) (i j : Fin (2*(MaskedClusterStage.dfa C E).stateCount))
    (hnew : fresh≤cfg.length) (hH : cfg.length≤cfg.anchor)
    (hrep : representative+cfg.length≤w.length) (hstart : cfg.descriptor.first+cfg.anchor≤w.length)
    (hcopy : Spec.slice w representative (representative+cfg.length)=
      Spec.slice w cfg.descriptor.first (cfg.descriptor.first+cfg.length)) :
    (Mutable.Store.compile C E book prepared (BoundaryApplication.Range.build C w)
      (BoundaryApplication.Range.build E w) sources target cfg).1.any
      (fun bank=>bank.view
        (code _ gate (ReplayMaps.encode (ReplayMaps.word C E (Spec.slice w (representative+fresh) (representative+cfg.length))))) i j)=
    (Mutable.Store.compile C E book prepared (BoundaryApplication.Range.build C w)
      (BoundaryApplication.Range.build E w) sources target (withLength cfg fresh)).1.any
      (fun bank=>bank.view (code _ gate (ReplayMaps.encode (ReplayMaps.one C.stateCount E.stateCount))) i j) := by
  by_cases hm : cfg.descriptor.repetitions=0
  · simp only [Mutable.Store.compile,withLength,hm,if_true,Mutable.Batch.compileSingleton,Option.any_some]
    exact point_select_shorter C E book w representative cfg.descriptor.first fresh cfg.length cfg.anchor
      (cfg.descriptor.nextAt sources.n) cfg.incoming cfg.incomingEnabled gate sources.singleton target cfg.window
      i j hnew hH hrep hstart hcopy
  · simp only [Mutable.Store.compile,withLength,hm,if_false]
    cases hid : cfg.runId with
    | none => simp only [Option.any_none]
    | some id =>
      simp only
      cases hR : sources.runs[id]? with
      | none => simp only [hR,Option.any_none]
      | some R =>
        simp only [hR]
        by_cases hcover : R.period=cfg.descriptor.period ∧ R.lo≤cfg.descriptor.first ∧
            cfg.descriptor.last+cfg.anchor≤R.hi+1
        · simp only [hcover,true_and,if_true,Mutable.Batch.compileRun]
          by_cases hK : sources.modulus=prepared.K
          · simp only [hK,if_true,hR]
            cases hidx : sources.indexes[id]? with
            | none => simp only [hidx,Option.any_none]
            | some idx =>
              simp only [hidx,Option.any_some]
              exact dense_select_shorter C E book prepared w representative cfg.descriptor.first R.period
                cfg.descriptor.repetitions fresh cfg.length cfg.anchor (cfg.descriptor.nextAt sources.n)
                cfg.incoming cfg.incomingEnabled gate idx target cfg.targetCounts cfg.window i j
                hnew hH hrep hstart hcopy
          · simp only [hK,if_false,Option.any_none]
        · simp only [hcover,if_false,Option.any_none]

theorem store_shorter_current (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount) (w : Word α) (fallback : α)
    (source target : Array Bool) (removed : List Nat) (sources : Mutable.Batch.Sources)
    (hv : MaskedMutableProgression.Batch.Valid source removed sources) (hn : sources.n=w.length)
    (hK : sources.modulus=prepared.K) (cfg : Mutable.Store.Config) (representative fresh : Nat)
    (hnew : fresh≤cfg.length) (hH : cfg.length≤cfg.anchor)
    (hrep : representative+cfg.length≤w.length) (hstart : cfg.descriptor.first+cfg.anchor≤w.length)
    (hcopy : Spec.slice w representative (representative+cfg.length)=
      Spec.slice w cfg.descriptor.first (cfg.descriptor.first+cfg.length))
    (fullBase anchorBase : Nat) (fullCopies copies : List Nat)
    (hg : MaskedClusterDescriptor.Geometry (ArrayText.read w.toArray fallback) w.length
      fullBase fresh fullCopies cfg.descriptor)
    (cert : MaskedLocalAnchor.Certificate (ArrayText.read w.toArray fallback) w.length
      anchorBase fresh copies cfg.descriptor.last (cfg.descriptor.nextAt w.length)
      cfg.descriptor.previous cfg.descriptor.following cfg.anchor)
    (hmem : ∀k,k≤cfg.descriptor.repetitions→cfg.descriptor.first+k*cfg.descriptor.period∈copies)
    (hr : MaskedTraversalContext.RunBacked sources target prepared.K cfg)
    (hin : cfg.incomingEnabled=true→cfg.descriptor.first<cfg.incoming ∧
      cfg.incoming≤if cfg.descriptor.repetitions=0 then cfg.descriptor.nextAt w.length else cfg.descriptor.first+cfg.descriptor.period)
    (gate inMode outMode : Bool) (i j : Fin (MaskedClusterStage.dfa C E).stateCount) :
    (Mutable.Store.compile C E book prepared (BoundaryApplication.Range.build C w)
      (BoundaryApplication.Range.build E w) sources target cfg).1.any
      (fun bank=>bank.view
        (code _ gate (ReplayMaps.encode (ReplayMaps.word C E (Spec.slice w (representative+fresh) (representative+cfg.length)))))
        (code _ inMode i) (code _ outMode j))=true ↔
      Mutable.Batch.CursorStep C E w cfg.descriptor.first cfg.descriptor.period cfg.descriptor.repetitions
        fresh cfg.anchor (cfg.descriptor.nextAt w.length) cfg.incoming cfg.incomingEnabled
        inMode outMode source removed target (cfg.window.gate gate)
        (MaskedClusterStage.decode C E i) (MaskedClusterStage.decode C E j) := by
  rw [store_select_shorter C E book prepared w sources target cfg representative fresh gate _ _
    hnew hH hrep hstart hcopy]
  exact MaskedTraversalContext.store_current C E book prepared w fallback source target removed sources hv hn hK
    (withLength cfg fresh) fullBase anchorBase fullCopies copies hg cert hmem hr hin gate inMode outMode i j

end REWB.MaskedTraversalAggregate
