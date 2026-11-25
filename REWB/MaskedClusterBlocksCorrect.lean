import REWB.MaskedClusterBlocks

/-! Concrete four-block compilers and their chronological text semantics.
    Both compilers consume shared text indices and immutable mask arrays.
    `compileDense` uses the two already built stepped-prefix arrays;
    `compilePoint` requires no periodicity and reads the masks directly.
    Their counters include context preparation, one replay lookup, and
    the four materialized cell matrices. Finite-orbit/formula construction
    is still outside the AP-cell counter, as in the underlying compiler.

    `BlockDenotes` is only a proof interface. Actual compiler instances
    are proved below from local anchor certificates; no relation or
    answer oracle occurs in either executable compiler.
-/
namespace REWB.MaskedCluster
variable {α : Type}

def CursorBlocks.work {m : Nat} (b : CursorBlocks m) : Nat :=
  b.normal.normal.work+b.normal.over.work+b.over.normal.work+b.over.over.work

def compileDense (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (s q m L H next incoming : Nat) (enabled : Bool) (source target : Array Bool)
    (sourceCounts targetCounts : Array Nat) (base : Nat) (window : SourceWindow) :
    CursorBlocks (MaskedClusterStage.dfa C E).stateCount×Nat :=
  let rows:=prepareRows C E ci ei s q m H next incoming enabled
  let tail:=replay C E ci ei s L H
  let out:=blocks C E prepared rows.1 tail.maps source target sourceCounts targetCounts base window
  (out,rows.2+tail.work+out.work+3)

def compilePoint (C E : DFA α)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (s L H next incoming : Nat) (enabled : Bool) (source target : Array Bool) (window : SourceWindow) :
    CursorBlocks (MaskedClusterStage.dfa C E).stateCount×Nat :=
  let rows:=preparePointRows C E ci ei s H next incoming enabled
  let tail:=replay C E ci ei s L H
  let out:=pointBlocks C E rows.1 tail.maps source target window
  (out,rows.2+tail.work+out.work+3)

def BlockDenotes (C E : DFA α) (b : CursorBlocks (MaskedClusterStage.dfa C E).stateCount)
    (R : Bool→Bool→MaskedClusterStage.State C.stateCount E.stateCount→
      MaskedClusterStage.State C.stateCount E.stateCount→Prop) : Prop :=
  ∀ input output i j,(((b.get input output).cells.get i).get j)=true ↔
    R input output (MaskedClusterStage.decode C E i) (MaskedClusterStage.decode C E j)

theorem compileDense_correct (C E : DFA α) (prepared : Prepared C.stateCount E.stateCount)
    (w : Word α) (fallback : α) (classBase L : Nat) (copies : List Nat)
    (s q m H next incoming : Nat) (previous following : Option Nat)
    (enabled : Bool) (source target : Array Bool) (base len : Nat) (window : SourceWindow)
    (cert : MaskedLocalAnchor.Certificate (ArrayText.read w.toArray fallback) w.length
      classBase L copies (s+m*q) next previous following H)
    (hq : 0<q) (hm : 0<m) (hd : 2*q≤L) (hmem : ∀ k,k≤m→s+k*q∈copies)
    (hprev : previous=some (s+(m-1)*q)) (hsep : s+m*q<next) (hnext : next≤w.length)
    (hin : enabled=true→s<incoming ∧ incoming≤s+q)
    (hbase : base≤s) (hend : s+m*q+H≤base+len) :
    BlockDenotes C E
      (compileDense C E prepared (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
        s q m L H next incoming enabled source target
        (MaskedProgression.build source base len (prepared.K*q)).counts
        (MaskedProgression.build target base len (prepared.K*q)).counts base window).1
      (fun input output=>CursorStep C E w s q m L H next incoming enabled input output source target window) := by
  intro input output i j
  cases input <;>
    simp only [compileDense,blocks,prepareRows,CursorBlocks.get,Bool.false_eq_true,if_false,if_true] <;>
    exact rowMatrix_correct C E prepared w fallback classBase L copies s q m H next incoming previous following
      enabled _ output source target base len window i j cert hq hm hd hmem hprev hsep hnext hin hbase hend

theorem compilePoint_correct (C E : DFA α) (w : Word α) (fallback : α)
    (classBase L : Nat) (copies : List Nat) (s H next incoming : Nat) (previous following : Option Nat)
    (enabled : Bool) (source target : Array Bool) (window : SourceWindow)
    (cert : MaskedLocalAnchor.Certificate (ArrayText.read w.toArray fallback) w.length
      classBase L copies s next previous following H)
    (hsep : s<next) (hnext : next≤w.length)
    (hin : enabled=true→s<incoming ∧ incoming≤next) :
    BlockDenotes C E
      (compilePoint C E (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
        s L H next incoming enabled source target window).1
      (fun input output=>CursorStep C E w s 1 0 L H next incoming enabled input output source target window) := by
  intro input output i j
  cases input <;>
    simp only [compilePoint,pointBlocks,preparePointRows,CursorBlocks.get,Bool.false_eq_true,if_false,if_true] <;>
    rw [pointRowMatrix_get] <;>
    exact pointRowCell_correct C E w fallback classBase L copies s H next incoming previous following
      enabled _ output source target window _ _ cert hsep hnext hin

/-- The middle state is a real wait/C/E stage, not merely an unchecked
    numeric code. Combining this with the two concrete compiler theorems
    gives exactly two chronological cursor steps, with the same middle
    cursor mode. Geometric compatibility of adjacent cluster boundaries
    remains an obligation of the eventual cluster-list assembly. -/
theorem composeBlocks_denotes (C E : DFA α)
    (a b : CursorBlocks (MaskedClusterStage.dfa C E).stateCount)
    (R S : Bool→Bool→MaskedClusterStage.State C.stateCount E.stateCount→
      MaskedClusterStage.State C.stateCount E.stateCount→Prop)
    (ha : BlockDenotes C E a R) (hb : BlockDenotes C E b S)
    (input output : Bool) (i j : Fin (MaskedClusterStage.dfa C E).stateCount) :
    (composeBlocks a b).1.view 0 (code _ input i) (code _ output j)=true ↔
      ∃ midMode midState,R input midMode (MaskedClusterStage.decode C E i) midState ∧
        S midMode output midState (MaskedClusterStage.decode C E j) := by
  rw [composeBlocks_correct]
  constructor
  · rintro ⟨mode,state,h1,h2⟩
    exact ⟨mode,MaskedClusterStage.decode C E state,(ha _ _ _ _).mp h1,(hb _ _ _ _).mp h2⟩
  · rintro ⟨mode,state,h1,h2⟩
    refine ⟨mode,MaskedClusterStage.encode C E state,(ha _ _ _ _).mpr ?_,(hb _ _ _ _).mpr ?_⟩
    · simpa only [MaskedClusterStage.decode_encode] using h1
    · simpa only [MaskedClusterStage.decode_encode] using h2

end REWB.MaskedCluster
