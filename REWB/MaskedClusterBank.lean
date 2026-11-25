import REWB.MaskedClusterReplay

/-! Actual prepared cursor blocks, materialized for every C/E replay
    prefix and for both source-enabled/disabled components. Both source
    and target masks are immutable. The source component and report
    interval gate only source jumps; no already-reported-start deletion
    data structure is supplied here.

    The pattern catalog is supplied once and shared. Bank counters charge
    actual map-cell composition, AP-cell work, matrix writes and flatten
    copies. As in the underlying compiler, finite-orbit/formula creation
    and pattern catalog/action construction have separate accounting.
-/
namespace REWB.MaskedCluster
open REWB.MaskedFiniteAction
variable {α : Type}

def SourceWindow.gate (window : SourceWindow) (enabled : Bool) : SourceWindow :=
  ⟨enabled && window.enabled,window.lo,window.hi⟩

theorem SourceWindow.gate_true (window : SourceWindow) : window.gate true=window := by
  cases window
  rfl

theorem SourceWindow.gate_false (window : SourceWindow) (p : Nat) :
    (window.gate false).allows p=false := by
  simp only [SourceWindow.gate,SourceWindow.allows,Bool.false_and]

def bankAction {c e : Nat} (z : ReplayMaps.Value c e) :
    Vector (Fin (2*ReplayMaps.count c e)) (2*ReplayMaps.count c e) :=
  let action:=ReplayMaps.rightAction z
  Vector.ofFn fun key=>code (ReplayMaps.count c e) (codeMode _ key) (action.get (codeState _ key))

theorem bankAction_get {c e : Nat} (z : ReplayMaps.Value c e) (key : Fin (2*ReplayMaps.count c e)) :
    (bankAction z).get key=code (ReplayMaps.count c e) (codeMode _ key)
      ((ReplayMaps.rightAction z).get (codeState _ key)) := by
  simp only [bankAction,BoundaryIndex.Table.get_ofFn]

theorem bankAction_gate {c e : Nat} (z : ReplayMaps.Value c e) (key : Fin (2*ReplayMaps.count c e)) :
    codeMode _ ((bankAction z).get key)=codeMode _ key := by
  rw [bankAction_get,codeMode_code]

theorem bankAction_prefix {c e : Nat} (z : ReplayMaps.Value c e) (key : Fin (2*ReplayMaps.count c e)) :
    ReplayMaps.decode c e (codeState _ ((bankAction z).get key))=
      ReplayMaps.mul (ReplayMaps.decode c e (codeState _ key)) z := by
  rw [bankAction_get,codeState_code,ReplayMaps.rightAction_decode]

theorem bankAction_comp {c e : Nat} (z0 z1 : ReplayMaps.Value c e)
    (key : Fin (2*ReplayMaps.count c e)) :
    (bankAction z0).get ((bankAction z1).get key)=
      (bankAction (ReplayMaps.mul z1 z0)).get key := by
  simp only [bankAction_get,codeMode_code,codeState_code,ReplayMaps.rightAction_comp]

/-- Project either whole-region source component without copying its
    immutable matrices. Different region components may subsequently be
    multiplied in chronological order, while sharing one replay key. -/
def bankComponent {c e m : Nat} (a : Table (2*ReplayMaps.count c e) m) (enabled : Bool) :
    Table (ReplayMaps.count c e) m×Nat :=
  (⟨Vector.ofFn fun key=>a.cells.get (code _ enabled key)⟩,ReplayMaps.count c e)

theorem bankComponent_view {c e m : Nat} (a : Table (2*ReplayMaps.count c e) m) (enabled : Bool)
    (key : Fin (ReplayMaps.count c e)) (i j : Fin m) :
    (bankComponent a enabled).1.view key i j=a.view (code _ enabled key) i j := by
  simp only [bankComponent,Table.view,BoundaryIndex.Table.get_ofFn]

theorem bankComponent_work {c e m : Nat} (a : Table (2*ReplayMaps.count c e) m) (enabled : Bool) :
    (bankComponent a enabled).2=ReplayMaps.count c e := rfl

theorem bankComponent_reindex {c e m : Nat} (a : Table (2*ReplayMaps.count c e) m)
    (enabled : Bool) (z : ReplayMaps.Value c e) :
    (bankComponent (Counted.reindex (bankAction z) a).1 enabled).1.view=
      (Counted.reindex (ReplayMaps.rightAction z) (bankComponent a enabled).1).1.view := by
  funext key i j
  simp only [bankComponent_view,Counted.reindex_view,View.reindex,bankAction_get,
    codeMode_code,codeState_code]

/-- The function argument is evaluated at every fixed pattern key, and
    all returned matrices are stored immediately. The executable dense
    and singleton instances below call the proved real block compilers. -/
def tabulate {c e m : Nat} (book : ReplayMaps.Prepared c e)
    (f : Bool→ReplayMaps.Value c e→CursorBlocks m) (tail : ReplayMaps.Value c e) :
    Table (2*ReplayMaps.count c e) (2*m)×Nat :=
  let results:=Vector.ofFn fun key : Fin (2*ReplayMaps.count c e)=>
    let mixed:=ReplayMaps.mulCounted (book.values.get (codeState _ key)) tail
    let compiled:=f (codeMode _ key) mixed.1
    let flat:=flattenResult compiled
    (flat.cells,mixed.2+compiled.work+flat.work+6)
  (⟨Vector.ofFn fun key=>(results.get key).1⟩,
    BoundaryIndex.Counted.rowWork results)

theorem tabulate_view {c e m : Nat} (book : ReplayMaps.Prepared c e)
    (f : Bool→ReplayMaps.Value c e→CursorBlocks m) (tail : ReplayMaps.Value c e)
    (key : Fin (2*ReplayMaps.count c e)) (i j : Fin (2*m)) :
    (tabulate book f tail).1.view key i j=
      (((flatten (f (codeMode _ key) (ReplayMaps.mul (ReplayMaps.decode c e (codeState _ key)) tail))).get i).get j) := by
  simp only [tabulate,Table.view,BoundaryIndex.Table.get_ofFn,ReplayMaps.mulCounted_value,book.exact,flatten]

theorem tabulate_select {c e m : Nat} (book : ReplayMaps.Prepared c e)
    (f : Bool→ReplayMaps.Value c e→CursorBlocks m) (tail pref : ReplayMaps.Value c e)
    (enabled input output : Bool) (i j : Fin m) :
    (tabulate book f tail).1.view (code _ enabled (ReplayMaps.encode pref)) (code _ input i) (code _ output j)=
      ((((f enabled (ReplayMaps.mul pref tail)).get input output).cells.get i).get j) := by
  rw [tabulate_view,codeMode_code,codeState_code,ReplayMaps.decode_encode,flatten_get]

theorem tabulate_work {c e m : Nat} (book : ReplayMaps.Prepared c e)
    (f : Bool→ReplayMaps.Value c e→CursorBlocks m) (tail : ReplayMaps.Value c e)
    (budget : Nat) (h : ∀ enabled value,(f enabled value).work≤budget) :
    (tabulate book f tail).2≤
      (2*ReplayMaps.count c e)*(c+e+budget+(2*m)*((2*m)*11)+7) := by
  apply rowWork_le
  intro key
  simp only [BoundaryIndex.Table.get_ofFn,ReplayMaps.mulCounted_steps,flattenResult_work]
  have hh:=h (codeMode _ key) (ReplayMaps.mulCounted (book.values.get (codeState _ key)) tail).1
  omega

/-- Reindexing keeps the source component and prepends the same z to
    the existing local tail. No inverse or injectivity is needed. -/
theorem tabulate_reindex {c e m : Nat} (book : ReplayMaps.Prepared c e)
    (f : Bool→ReplayMaps.Value c e→CursorBlocks m) (tail z : ReplayMaps.Value c e) :
    (Counted.reindex (bankAction z) (tabulate book f tail).1).1.view=
      (tabulate book f (ReplayMaps.mul z tail)).1.view := by
  rw [Counted.reindex_view]
  funext key i j
  simp only [View.reindex,tabulate_view,bankAction_gate,bankAction_prefix,ReplayMaps.mul_assoc]

def denseBank (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (rows : Option (RowContext C E)×Option (RowContext C E)) (tail : Replay C E)
    (source target : Array Bool) (sourceCounts targetCounts : Array Nat)
    (base : Nat) (window : SourceWindow) :
    Table (2*ReplayMaps.count C.stateCount E.stateCount) (2*(MaskedClusterStage.dfa C E).stateCount)×Nat :=
  tabulate book (fun enabled value=>blocks C E prepared rows value source target sourceCounts targetCounts
    base (window.gate enabled)) tail

def pointBank (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (rows : Option (RowContext C E)×Option (RowContext C E)) (tail : Replay C E)
    (source target : Array Bool) (window : SourceWindow) :
    Table (2*ReplayMaps.count C.stateCount E.stateCount) (2*(MaskedClusterStage.dfa C E).stateCount)×Nat :=
  tabulate book (fun enabled value=>pointBlocks C E rows value source target (window.gate enabled)) tail

theorem denseBank_reindex (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (rows : Option (RowContext C E)×Option (RowContext C E)) (tail z : Replay C E)
    (source target : Array Bool) (sourceCounts targetCounts : Array Nat) (base : Nat) (window : SourceWindow) :
    (Counted.reindex (bankAction z)
      (denseBank C E book prepared rows tail source target sourceCounts targetCounts base window).1).1.view=
      (denseBank C E book prepared rows (ReplayMaps.mul z tail) source target sourceCounts targetCounts base window).1.view :=
  tabulate_reindex book _ tail z

theorem pointBank_reindex (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (rows : Option (RowContext C E)×Option (RowContext C E)) (tail z : Replay C E)
    (source target : Array Bool) (window : SourceWindow) :
    (Counted.reindex (bankAction z) (pointBank C E book rows tail source target window).1).1.view=
      (pointBank C E book rows (ReplayMaps.mul z tail) source target window).1.view :=
  tabulate_reindex book _ tail z

theorem denseBank_work (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (rows : Option (RowContext C E)×Option (RowContext C E)) (tail : Replay C E)
    (source target : Array Bool) (sourceCounts targetCounts : Array Nat) (base : Nat) (window : SourceWindow) :
    (denseBank C E book prepared rows tail source target sourceCounts targetCounts base window).2≤
      (2*ReplayMaps.count C.stateCount E.stateCount)*
        (C.stateCount+E.stateCount+
          4*((1+C.stateCount+E.stateCount)*((1+C.stateCount+E.stateCount)*(rowBudget C E prepared.K+1)))+
          (2*(1+C.stateCount+E.stateCount))*((2*(1+C.stateCount+E.stateCount))*11)+7) := by
  rw [←MaskedClusterStage.dfa_size C E]
  apply tabulate_work
  intro enabled value
  conv => rhs; rw [MaskedClusterStage.dfa_size C E]
  exact blocks_work C E prepared rows value source target sourceCounts targetCounts base (window.gate enabled)

theorem pointBank_work (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (rows : Option (RowContext C E)×Option (RowContext C E)) (tail : Replay C E)
    (source target : Array Bool) (window : SourceWindow) :
    (pointBank C E book rows tail source target window).2≤
      (2*ReplayMaps.count C.stateCount E.stateCount)*
        (C.stateCount+E.stateCount+4*((1+C.stateCount+E.stateCount)*((1+C.stateCount+E.stateCount)*21))+
          (2*(1+C.stateCount+E.stateCount))*((2*(1+C.stateCount+E.stateCount))*11)+7) := by
  rw [←MaskedClusterStage.dfa_size C E]
  apply tabulate_work
  intro enabled value
  conv => rhs; rw [MaskedClusterStage.dfa_size C E]
  exact pointBlocks_work C E rows value source target (window.gate enabled)

end REWB.MaskedCluster
