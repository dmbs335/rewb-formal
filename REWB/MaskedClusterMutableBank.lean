import REWB.MaskedClusterMutableSemantics
import REWB.MaskedClusterBankBudget

/-! Actual replay banks rebuilt against one current source-index
    snapshot. The target array remains immutable. Uniform shortening is
    valid while that snapshot and the cluster geometry remain fixed.
    Erasing a source changes the required bank; this file does not claim
    that a previously cached bank is automatically repaired.
-/
namespace REWB.MaskedCluster.Mutable
open REWB.MaskedFiniteAction
variable {α : Type}

theorem table_eq {k m : Nat} (a b : Table k m) (h : a.view=b.view) : a=b := by
  cases a with
  | mk ac =>
    cases b with
    | mk bc =>
      congr 1
      apply Vector.ext
      intro key hk
      change ac.get ⟨key,hk⟩=bc.get ⟨key,hk⟩
      apply Vector.ext
      intro i hi
      change (ac.get ⟨key,hk⟩).get ⟨i,hi⟩=(bc.get ⟨key,hk⟩).get ⟨i,hi⟩
      apply Vector.ext
      intro j hj
      exact congrFun (congrFun (congrFun h ⟨key,hk⟩) ⟨i,hi⟩) ⟨j,hj⟩

def denseBank (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount) (rows : Option (RowContext C E)×Option (RowContext C E))
    (tail : Replay C E) (idx : Index) (target : Array Bool) (targetCounts : Array Nat) (window : SourceWindow) :
    Table (2*ReplayMaps.count C.stateCount E.stateCount) (2*(MaskedClusterStage.dfa C E).stateCount)×Nat :=
  tabulate book (fun enabled value=>blocks C E prepared rows value idx target targetCounts (window.gate enabled)) tail

def pointBank (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (rows : Option (RowContext C E)×Option (RowContext C E)) (tail : Replay C E)
    (idx : Index) (target : Array Bool) (window : SourceWindow) :
    Table (2*ReplayMaps.count C.stateCount E.stateCount) (2*(MaskedClusterStage.dfa C E).stateCount)×Nat :=
  tabulate book (fun enabled value=>pointBlocks C E rows value idx target (window.gate enabled)) tail

theorem denseBank_snapshot (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount) (rows : Option (RowContext C E)×Option (RowContext C E))
    (tail : Replay C E) (idx : Index) (hv : idx.Valid) (target : Array Bool) (targetCounts : Array Nat) (window : SourceWindow)
    (ha : ∀ row,rows.1=some row→0<row.step ∧ idx.step=prepared.K*row.step)
    (hb : ∀ row,rows.2=some row→0<row.step ∧ idx.step=prepared.K*row.step) :
    (denseBank C E book prepared rows tail idx target targetCounts window).1=
      (REWB.MaskedCluster.denseBank C E book prepared rows tail (snapshot idx) target
        (MaskedProgression.build (snapshot idx) idx.base idx.len idx.step).counts targetCounts idx.base window).1 := by
  apply table_eq
  funext key i j
  simp only [denseBank,REWB.MaskedCluster.denseBank,tabulate_view]
  rw [←code_decode i,←code_decode j,flatten_get,flatten_get]
  exact blocks_snapshot C E prepared rows _ idx hv target targetCounts _ _ _ _ _ ha hb

theorem pointBank_snapshot (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (rows : Option (RowContext C E)×Option (RowContext C E)) (tail : Replay C E)
    (idx : Index) (target : Array Bool) (window : SourceWindow) :
    (pointBank C E book rows tail idx target window).1=
      (REWB.MaskedCluster.pointBank C E book rows tail (snapshot idx) target window).1 := by
  apply table_eq
  funext key i j
  simp only [pointBank,REWB.MaskedCluster.pointBank,tabulate_view]
  rw [←code_decode i,←code_decode j,flatten_get,flatten_get]
  exact pointBlocks_snapshot C E rows _ idx target _ _ _ _ _

theorem denseBank_reindex (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount) (rows : Option (RowContext C E)×Option (RowContext C E))
    (tail z : Replay C E) (idx : Index) (target : Array Bool) (targetCounts : Array Nat) (window : SourceWindow) :
    (Counted.reindex (bankAction z) (denseBank C E book prepared rows tail idx target targetCounts window).1).1.view=
      (denseBank C E book prepared rows (ReplayMaps.mul z tail) idx target targetCounts window).1.view :=
  tabulate_reindex book _ tail z

theorem pointBank_reindex (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (rows : Option (RowContext C E)×Option (RowContext C E)) (tail z : Replay C E)
    (idx : Index) (target : Array Bool) (window : SourceWindow) :
    (Counted.reindex (bankAction z) (pointBank C E book rows tail idx target window).1).1.view=
      (pointBank C E book rows (ReplayMaps.mul z tail) idx target window).1.view :=
  tabulate_reindex book _ tail z

def compileDenseBank (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (s q m L H next incoming : Nat) (enabled : Bool) (idx : Index)
    (target : Array Bool) (targetCounts : Array Nat) (window : SourceWindow) :
    Table (2*ReplayMaps.count C.stateCount E.stateCount) (2*(MaskedClusterStage.dfa C E).stateCount)×Nat :=
  let rows:=prepareRows C E ci ei s q m H next incoming enabled
  let tail:=replay C E ci ei s L H
  let out:=denseBank C E book prepared rows.1 tail.maps idx target targetCounts window
  (out.1,rows.2+tail.work+out.2+3)

def compilePointBank (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (s L H next incoming : Nat) (enabled : Bool) (idx : Index) (target : Array Bool) (window : SourceWindow) :
    Table (2*ReplayMaps.count C.stateCount E.stateCount) (2*(MaskedClusterStage.dfa C E).stateCount)×Nat :=
  let rows:=preparePointRows C E ci ei s H next incoming enabled
  let tail:=replay C E ci ei s L H
  let out:=pointBank C E book rows.1 tail.maps idx target window
  (out.1,rows.2+tail.work+out.2+3)

theorem compileDenseBank_snapshot (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (s q m L H next incoming : Nat) (enabled : Bool) (idx : Index) (hv : idx.Valid)
    (target : Array Bool) (targetCounts : Array Nat) (window : SourceWindow)
    (hq : 0<q) (hstep : idx.step=prepared.K*q) :
    (compileDenseBank C E book prepared ci ei s q m L H next incoming enabled idx target targetCounts window).1=
      (REWB.MaskedCluster.compileDenseBank C E book prepared ci ei s q m L H next incoming enabled
        (snapshot idx) target (MaskedProgression.build (snapshot idx) idx.base idx.len idx.step).counts
        targetCounts idx.base window).1 := by
  apply denseBank_snapshot C E book prepared _ _ idx hv target targetCounts window
  · intro row hr
    have he:=prepareRow_step C E ci ei s q m H next incoming enabled false row hr
    exact ⟨by rw [he]; exact hq,by rw [he]; exact hstep⟩
  · intro row hr
    have he:=prepareRow_step C E ci ei s q m H next incoming enabled true row hr
    exact ⟨by rw [he]; exact hq,by rw [he]; exact hstep⟩

theorem compilePointBank_snapshot (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (s L H next incoming : Nat) (enabled : Bool) (idx : Index) (target : Array Bool) (window : SourceWindow) :
    (compilePointBank C E book ci ei s L H next incoming enabled idx target window).1=
      (REWB.MaskedCluster.compilePointBank C E book ci ei s L H next incoming enabled (snapshot idx) target window).1 :=
  pointBank_snapshot C E book _ _ idx target window

theorem compileDenseBank_reindex (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount) (w : Word α)
    (representative s q m fresh old H next incoming : Nat) (enabled : Bool) (idx : Index)
    (target : Array Bool) (targetCounts : Array Nat) (window : SourceWindow)
    (hnew : fresh≤old) (hH : old≤H) (hrep : representative+old≤w.length) (hstart : s+H≤w.length)
    (hcopy : Spec.slice w representative (representative+old)=Spec.slice w s (s+old)) :
    (Counted.reindex (bankAction
      (replay C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w) representative fresh old).maps)
      (compileDenseBank C E book prepared (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
        s q m old H next incoming enabled idx target targetCounts window).1).1.view=
      (compileDenseBank C E book prepared (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
        s q m fresh H next incoming enabled idx target targetCounts window).1.view := by
  simp only [compileDenseBank,denseBank_reindex]
  rw [←ReplayMaps.replay_common_shortening C E w representative s fresh old H hnew hH hrep hstart hcopy]

theorem compilePointBank_reindex (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount) (w : Word α)
    (representative s fresh old H next incoming : Nat) (enabled : Bool) (idx : Index)
    (target : Array Bool) (window : SourceWindow)
    (hnew : fresh≤old) (hH : old≤H) (hrep : representative+old≤w.length) (hstart : s+H≤w.length)
    (hcopy : Spec.slice w representative (representative+old)=Spec.slice w s (s+old)) :
    (Counted.reindex (bankAction
      (replay C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w) representative fresh old).maps)
      (compilePointBank C E book (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
        s old H next incoming enabled idx target window).1).1.view=
      (compilePointBank C E book (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
        s fresh H next incoming enabled idx target window).1.view := by
  simp only [compilePointBank,pointBank_reindex]
  rw [←ReplayMaps.replay_common_shortening C E w representative s fresh old H hnew hH hrep hstart hcopy]

end REWB.MaskedCluster.Mutable
