import REWB.PeriodicConstructionClusterBank
import REWB.MaskedTraversalBankReady
import REWB.MaskedTraversalContext

/-! Reimplemented after the 2026-11-25 environment interruption.
This is a new source implementation, not a byte-exact recovered file.
The actual measured dense compiler is substituted at run, store, leader,
and context interfaces. Each call retains the entire original result and
old counter while returning the executed construction work separately. -/
namespace REWB.MaskedAllStart.FullCost.Bank
open REWB.MaskedCluster REWB.MaskedFiniteAction
variable {α : Type} {h h' n : Nat}

abbrev Result (X : Type) := X×Nat

def extra (C E : DFA α) (K : Nat) : Nat :=
  PeriodicConstruction.Cluster.denseBankExtra C.stateCount E.stateCount K+3

def compileRun (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (sources : Mutable.Batch.Sources) (id s m L H next incoming : Nat) (enabled : Bool)
    (target : Array Bool) (targetCounts : Array Nat) (window : SourceWindow) :
    Result (Option (Mutable.Store.Bank C E)×Nat) :=
  if sources.modulus=prepared.K then
    match sources.runs[id]?,sources.indexes[id]? with
    | some R,some idx=>
      let ⟨⟨bank,oldWork⟩,fullWork⟩:=PeriodicConstruction.Cluster.compileDenseBank C E book prepared ci ei
        s R.period m L H next incoming enabled idx target targetCounts window
      ((some bank,oldWork+9),fullWork+9)
    | _,_=>((none,5),5)
  else ((none,2),2)

theorem compileRun_value (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (sources : Mutable.Batch.Sources) (id s m L H next incoming : Nat) (enabled : Bool)
    (target : Array Bool) (targetCounts : Array Nat) (window : SourceWindow) :
    (compileRun C E book prepared ci ei sources id s m L H next incoming enabled target targetCounts window).1=
      Mutable.Batch.compileRun C E book prepared ci ei sources id s m L H next incoming enabled target targetCounts window := by
  unfold compileRun Mutable.Batch.compileRun
  split
  · cases hr : sources.runs[id]? <;> cases hi : sources.indexes[id]? <;>
      simp only [PeriodicConstruction.Cluster.compileDenseBank_value]
  · rfl

theorem compileRun_extra (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (sources : Mutable.Batch.Sources) (id s m L H next incoming : Nat) (enabled : Bool)
    (target : Array Bool) (targetCounts : Array Nat) (window : SourceWindow) :
    (compileRun C E book prepared ci ei sources id s m L H next incoming enabled target targetCounts window).2≤
      (Mutable.Batch.compileRun C E book prepared ci ei sources id s m L H next incoming enabled target targetCounts window).2+
        extra C E prepared.K := by
  unfold compileRun Mutable.Batch.compileRun
  split
  · cases hr : sources.runs[id]? with
    | none=>simp only; omega
    | some R=>
      cases hi : sources.indexes[id]? with
      | none=>simp only; omega
      | some idx=>
        have hh:=PeriodicConstruction.Cluster.compileDenseBank_extra C E book prepared ci ei
          s R.period m L H next incoming enabled idx target targetCounts window
        simp only
        unfold extra
        omega
  · simp only; omega

def compile (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (sources : Mutable.Batch.Sources) (target : Array Bool) (cfg : Mutable.Store.Config) :
    Result (Option (Mutable.Store.Bank C E)×Nat) :=
  let d:=cfg.descriptor
  if d.repetitions=0 then
    let ⟨bank,oldWork⟩:=Mutable.Batch.compileSingleton C E book ci ei sources d.first cfg.length cfg.anchor
      (d.nextAt sources.n) cfg.incoming cfg.incomingEnabled target cfg.window
    ((some bank,oldWork+1),oldWork+1)
  else
    match cfg.runId with
    | none=>((none,2),2)
    | some id=>
      match sources.runs[id]? with
      | none=>((none,4),4)
      | some R=>
        if R.period=d.period ∧ R.lo≤d.first ∧ d.last+cfg.anchor≤R.hi+1 then
          let ⟨⟨bank,oldWork⟩,fullWork⟩:=compileRun C E book prepared ci ei sources id d.first d.repetitions
            cfg.length cfg.anchor (d.nextAt sources.n) cfg.incoming cfg.incomingEnabled target cfg.targetCounts cfg.window
          ((bank,oldWork+9),fullWork+9)
        else ((none,8),8)

theorem compile_value (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (sources : Mutable.Batch.Sources) (target : Array Bool) (cfg : Mutable.Store.Config) :
    (compile C E book prepared ci ei sources target cfg).1=
      Mutable.Store.compile C E book prepared ci ei sources target cfg := by
  by_cases hz : cfg.descriptor.repetitions=0
  · simp only [compile,Mutable.Store.compile,hz,if_true]
  · simp only [compile,Mutable.Store.compile,hz,if_false]
    cases hid : cfg.runId with
    | none=>rfl
    | some id=>
      simp only
      cases hr : sources.runs[id]? with
      | none=>rfl
      | some R=>
        simp only
        split <;> simp only [compileRun_value]

theorem compile_extra (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (sources : Mutable.Batch.Sources) (target : Array Bool) (cfg : Mutable.Store.Config) :
    (compile C E book prepared ci ei sources target cfg).2≤
      (Mutable.Store.compile C E book prepared ci ei sources target cfg).2+extra C E prepared.K := by
  by_cases hz : cfg.descriptor.repetitions=0
  · simp only [compile,Mutable.Store.compile,hz,if_true]
    omega
  · simp only [compile,Mutable.Store.compile,hz,if_false]
    cases hid : cfg.runId with
    | none=>simp only; omega
    | some id=>
      simp only
      cases hr : sources.runs[id]? with
      | none=>simp only; omega
      | some R=>
        simp only
        split
        · have hh:=compileRun_extra C E book prepared ci ei sources id cfg.descriptor.first cfg.descriptor.repetitions
            cfg.length cfg.anchor (cfg.descriptor.nextAt sources.n) cfg.incoming cfg.incomingEnabled target cfg.targetCounts cfg.window
          simp only
          omega
        · simp only; omega

def readyCompile (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (partition : MaskedClusterLeaders.State h) (capacity first current : Nat)
    (anchors : Array (Option Nat)) (window : SourceWindow)
    (catalog : MaskedRunCatalog.Index) (classes : MaskedSuffixClass.Index n h')
    (sources : Mutable.Batch.Sources) (target : Array Bool) :
    Result (Option (Mutable.Store.Entry C E)×Nat) :=
  let ⟨config,preparation⟩:=MaskedTraversalBankReady.prepare partition capacity first current anchors window catalog classes
  match config with
  | none=>((none,preparation+1),preparation+1)
  | some cfg=>
    let ⟨⟨bank,oldWork⟩,fullWork⟩:=compile C E book prepared ci ei sources target cfg
    ((bank.map (fun table=>⟨cfg,table⟩),preparation+oldWork+3),preparation+fullWork+3)

theorem readyCompile_value (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (partition : MaskedClusterLeaders.State h) (capacity first current : Nat)
    (anchors : Array (Option Nat)) (window : SourceWindow)
    (catalog : MaskedRunCatalog.Index) (classes : MaskedSuffixClass.Index n h')
    (sources : Mutable.Batch.Sources) (target : Array Bool) :
    (readyCompile C E book prepared ci ei partition capacity first current anchors window catalog classes sources target).1=
      MaskedTraversalBankReady.compile C E book prepared ci ei partition capacity first current anchors window catalog classes sources target := by
  unfold readyCompile MaskedTraversalBankReady.compile
  cases hp : MaskedTraversalBankReady.prepare partition capacity first current anchors window catalog classes with
  | mk config preparation=>cases config <;> simp only [compile_value]

theorem readyCompile_extra (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (partition : MaskedClusterLeaders.State h) (capacity first current : Nat)
    (anchors : Array (Option Nat)) (window : SourceWindow)
    (catalog : MaskedRunCatalog.Index) (classes : MaskedSuffixClass.Index n h')
    (sources : Mutable.Batch.Sources) (target : Array Bool) :
    (readyCompile C E book prepared ci ei partition capacity first current anchors window catalog classes sources target).2≤
      (MaskedTraversalBankReady.compile C E book prepared ci ei partition capacity first current anchors window catalog classes sources target).2+
        extra C E prepared.K := by
  unfold readyCompile MaskedTraversalBankReady.compile
  cases hp : MaskedTraversalBankReady.prepare partition capacity first current anchors window catalog classes with
  | mk config preparation=>
    cases config with
    | none=>simp only; omega
    | some cfg=>
      have hh:=compile_extra C E book prepared ci ei sources target cfg
      simp only
      omega

def contextCompile (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (partition : MaskedClusterLeaders.State h) (capacity first L : Nat)
    (anchors : Array (Option Nat)) (target : Array Bool) (st : Mutable.Store.State C E) :
    Result (Option (Mutable.Store.Entry C E)×Nat) :=
  let ⟨config,preparation⟩:=MaskedTraversalContext.prepare partition capacity first L anchors (st.slots[first]?.join)
  match config with
  | none=>((none,preparation+3),preparation+3)
  | some cfg=>
    let ⟨⟨bank,oldWork⟩,fullWork⟩:=compile C E book prepared ci ei st.sources target cfg
    ((bank.map (fun table=>⟨cfg,table⟩),preparation+oldWork+5),preparation+fullWork+5)

theorem contextCompile_value (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (partition : MaskedClusterLeaders.State h) (capacity first L : Nat)
    (anchors : Array (Option Nat)) (target : Array Bool) (st : Mutable.Store.State C E) :
    (contextCompile C E book prepared ci ei partition capacity first L anchors target st).1=
      MaskedTraversalContext.compile C E book prepared ci ei partition capacity first L anchors target st := by
  unfold contextCompile MaskedTraversalContext.compile
  cases hp : MaskedTraversalContext.prepare partition capacity first L anchors (st.slots[first]?.join) with
  | mk config preparation=>cases config <;> simp only [compile_value]

theorem contextCompile_extra (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (partition : MaskedClusterLeaders.State h) (capacity first L : Nat)
    (anchors : Array (Option Nat)) (target : Array Bool) (st : Mutable.Store.State C E) :
    (contextCompile C E book prepared ci ei partition capacity first L anchors target st).2≤
      (MaskedTraversalContext.compile C E book prepared ci ei partition capacity first L anchors target st).2+
        extra C E prepared.K := by
  unfold contextCompile MaskedTraversalContext.compile
  cases hp : MaskedTraversalContext.prepare partition capacity first L anchors (st.slots[first]?.join) with
  | mk config preparation=>
    cases config with
    | none=>simp only; omega
    | some cfg=>
      have hh:=compile_extra C E book prepared ci ei st.sources target cfg
      simp only
      omega

end REWB.MaskedAllStart.FullCost.Bank
