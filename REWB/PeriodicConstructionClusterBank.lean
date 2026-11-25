import REWB.PeriodicConstructionClusterMatrix
import REWB.MaskedClusterMutableBank

/-! Drop-in measured dense-bank compiler. Each replay key is compiled
once; its original table/counter and full construction counter are
read from that one stored result. The new local overhead has an explicit
fixed-pattern bound and is absorbable into the old returned bank cost.
Pattern-catalog preparation and action-table factories remain separate.
-/
namespace REWB.PeriodicConstruction.Cluster
open REWB.PeriodicConstruction REWB.MaskedCluster REWB.MaskedFiniteAction
variable {α : Type} {c e m : Nat}

def tabulate (book : ReplayMaps.Prepared c e)
    (f : Bool→ReplayMaps.Value c e→Result (CursorBlocks m)) (tail : ReplayMaps.Value c e) :
    Result (Table (2*ReplayMaps.count c e) (2*m)×Nat) :=
  let results:=Vector.ofFn fun key : Fin (2*ReplayMaps.count c e)=>
    let mixed:=ReplayMaps.mulCounted (book.values.get (codeState _ key)) tail
    let compiled:=f (codeMode _ key) mixed.1
    let flat:=flattenResult compiled.1
    (flat.cells,mixed.2+compiled.1.work+flat.work+6,
      3*mixed.2+compiled.2+2*flat.work+16)
  let cells:=Vector.ofFn fun key=>(results.get key).1
  let oldWork:=(List.ofFn fun key=>(results.get key).2.1+1).sum
  let fullWork:=(List.ofFn fun key=>(results.get key).2.2+8).sum
  ((⟨cells⟩,oldWork),fullWork+4*(2*ReplayMaps.count c e)+3)

theorem tabulate_value (book : ReplayMaps.Prepared c e)
    (f : Bool→ReplayMaps.Value c e→Result (CursorBlocks m)) (tail : ReplayMaps.Value c e) :
    (tabulate book f tail).1=MaskedCluster.tabulate book (fun enabled v=>(f enabled v).1) tail := by
  simp only [tabulate,MaskedCluster.tabulate,BoundaryIndex.Counted.rowWork,BoundaryIndex.Table.get_ofFn]

def tabulateExtra (c e m C : Nat) : Nat :=
  (2*ReplayMaps.count c e)*(C+2*(c+e)+(2*m)*((2*m)*11)+22)+4*(2*ReplayMaps.count c e)+3

theorem tabulate_extra (book : ReplayMaps.Prepared c e)
    (f : Bool→ReplayMaps.Value c e→Result (CursorBlocks m)) (tail : ReplayMaps.Value c e)
    (C : Nat) (hc : ∀enabled v,(f enabled v).2≤(f enabled v).1.work+C) :
    (tabulate book f tail).2≤
      (MaskedCluster.tabulate book (fun enabled v=>(f enabled v).1) tail).2+tabulateExtra c e m C := by
  have h:=sum_le_sum_add (2*ReplayMaps.count c e)
    (fun key=>let mixed:=ReplayMaps.mulCounted (book.values.get (codeState _ key)) tail
      let compiled:=f (codeMode _ key) mixed.1
      3*mixed.2+compiled.2+2*(flattenResult compiled.1).work+16+8)
    (fun key=>let mixed:=ReplayMaps.mulCounted (book.values.get (codeState _ key)) tail
      let compiled:=f (codeMode _ key) mixed.1
      mixed.2+compiled.1.work+(flattenResult compiled.1).work+6+1)
    (C+2*(c+e)+(2*m)*((2*m)*11)+22) (by
      intro key
      dsimp only
      have hh:=hc (codeMode _ key) (ReplayMaps.mulCounted (book.values.get (codeState _ key)) tail).1
      simp only [ReplayMaps.mulCounted_steps,flattenResult_work]
      omega)
  simp only [tabulate,MaskedCluster.tabulate,BoundaryIndex.Counted.rowWork,
    BoundaryIndex.Table.get_ofFn,tabulateExtra]
  dsimp only at h
  omega

def denseBank (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount) (rows : Option (RowContext C E)×Option (RowContext C E))
    (tail : Replay C E) (idx : Mutable.Index) (target : Array Bool) (targetCounts : Array Nat) (window : SourceWindow) :
    Result (Table (2*ReplayMaps.count C.stateCount E.stateCount) (2*(MaskedClusterStage.dfa C E).stateCount)×Nat) :=
  tabulate book (fun enabled value=>blocks C E prepared rows value idx target targetCounts (window.gate enabled)) tail

def denseBankExtra (c e K : Nat) : Nat := tabulateExtra c e (1+c+e) (blocksExtra c e K)

theorem denseBank_value (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount) (rows : Option (RowContext C E)×Option (RowContext C E))
    (tail : Replay C E) (idx : Mutable.Index) (target : Array Bool) (targetCounts : Array Nat) (window : SourceWindow) :
    (denseBank C E book prepared rows tail idx target targetCounts window).1=
      Mutable.denseBank C E book prepared rows tail idx target targetCounts window := by
  simp only [denseBank,tabulate_value,blocks_value,Mutable.denseBank]

theorem denseBank_extra (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount) (rows : Option (RowContext C E)×Option (RowContext C E))
    (tail : Replay C E) (idx : Mutable.Index) (target : Array Bool) (targetCounts : Array Nat) (window : SourceWindow) :
    (denseBank C E book prepared rows tail idx target targetCounts window).2≤
      (Mutable.denseBank C E book prepared rows tail idx target targetCounts window).2+
      denseBankExtra C.stateCount E.stateCount prepared.K := by
  have h:=tabulate_extra book
    (fun enabled value=>blocks C E prepared rows value idx target targetCounts (window.gate enabled)) tail
    (blocksExtra C.stateCount E.stateCount prepared.K) (by
      intro enabled value
      rw [blocks_value]
      exact blocks_extra C E prepared rows value idx target targetCounts (window.gate enabled))
  simpa only [blocks_value,denseBank,Mutable.denseBank,denseBankExtra,MaskedClusterStage.dfa_size] using h

theorem denseBank_inflate (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount) (rows : Option (RowContext C E)×Option (RowContext C E))
    (tail : Replay C E) (idx : Mutable.Index) (target : Array Bool) (targetCounts : Array Nat) (window : SourceWindow) :
    (denseBank C E book prepared rows tail idx target targetCounts window).2≤
      (denseBankExtra C.stateCount E.stateCount prepared.K+1)*
      ((Mutable.denseBank C E book prepared rows tail idx target targetCounts window).2+1) :=
  Nat.le_trans (denseBank_extra C E book prepared rows tail idx target targetCounts window) (Masked.inflate _ _)

def compileDenseBank (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (s q m L H next incoming : Nat) (enabled : Bool) (idx : Mutable.Index)
    (target : Array Bool) (targetCounts : Array Nat) (window : SourceWindow) :
    Result (Table (2*ReplayMaps.count C.stateCount E.stateCount) (2*(MaskedClusterStage.dfa C E).stateCount)×Nat) :=
  let rows:=prepareRows C E ci ei s q m H next incoming enabled
  let tail:=replay C E ci ei s L H
  let out:=denseBank C E book prepared rows.1 tail.maps idx target targetCounts window
  ((out.1.1,rows.2+tail.work+out.1.2+3),rows.2+tail.work+out.2+6)

theorem compileDenseBank_value (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (s q m L H next incoming : Nat) (enabled : Bool) (idx : Mutable.Index)
    (target : Array Bool) (targetCounts : Array Nat) (window : SourceWindow) :
    (compileDenseBank C E book prepared ci ei s q m L H next incoming enabled idx target targetCounts window).1=
      Mutable.compileDenseBank C E book prepared ci ei s q m L H next incoming enabled idx target targetCounts window := by
  simp only [compileDenseBank,denseBank_value,Mutable.compileDenseBank]

theorem compileDenseBank_extra (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (s q m L H next incoming : Nat) (enabled : Bool) (idx : Mutable.Index)
    (target : Array Bool) (targetCounts : Array Nat) (window : SourceWindow) :
    (compileDenseBank C E book prepared ci ei s q m L H next incoming enabled idx target targetCounts window).2≤
      (Mutable.compileDenseBank C E book prepared ci ei s q m L H next incoming enabled idx target targetCounts window).2+
      denseBankExtra C.stateCount E.stateCount prepared.K+3 := by
  have h:=denseBank_extra C E book prepared (prepareRows C E ci ei s q m H next incoming enabled).1
    (replay C E ci ei s L H).maps idx target targetCounts window
  simp only [compileDenseBank,Mutable.compileDenseBank]
  omega

theorem compileDenseBank_inflate (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (s q m L H next incoming : Nat) (enabled : Bool) (idx : Mutable.Index)
    (target : Array Bool) (targetCounts : Array Nat) (window : SourceWindow) :
    (compileDenseBank C E book prepared ci ei s q m L H next incoming enabled idx target targetCounts window).2≤
      (denseBankExtra C.stateCount E.stateCount prepared.K+4)*
      ((Mutable.compileDenseBank C E book prepared ci ei s q m L H next incoming enabled idx target targetCounts window).2+1) := by
  exact Nat.le_trans (compileDenseBank_extra C E book prepared ci ei s q m L H next incoming enabled idx target targetCounts window)
    (by simpa only [Nat.add_assoc] using (Masked.inflate
      (Mutable.compileDenseBank C E book prepared ci ei s q m L H next incoming enabled idx target targetCounts window).2
      (denseBankExtra C.stateCount E.stateCount prepared.K+3)))

end REWB.PeriodicConstruction.Cluster
