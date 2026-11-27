import REWB.MaskedClusterMutableBudget
import REWB.MaskedMutableProgressionBatchQuery

/-! Actual run-ID and singleton adapters for the maintained source batch.
    The dense adapter reads the descriptor and current source index by
    direct array lookup. Its period comes from the stored run; incompatible
    moduli are rejected. Immutable target counts are prepared once by the
    caller and their exact construction is required in physical correctness.
    No source mask/count array is constructed by either adapter.

    History predicates below are specifications only: executable queries
    neither traverse the erase history nor rebuild an erased Boolean mask.
    Global cache ownership and selecting banks to repair are separate.
-/
namespace REWB.MaskedCluster.Mutable.Batch
open REWB.MaskedFiniteAction
open REWB.RunGeometry
open REWB.MaskedPeriodic.Batch (span)
variable {α : Type}

abbrev Sources := MaskedMutableProgression.Batch.State

def compileRun (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (sources : Sources) (id s m L H next incoming : Nat) (enabled : Bool)
    (target : Array Bool) (targetCounts : Array Nat) (window : SourceWindow) :
    Option (Table (2*ReplayMaps.count C.stateCount E.stateCount)
      (2*(MaskedClusterStage.dfa C E).stateCount))×Nat :=
  if sources.modulus=prepared.K then
    match sources.runs[id]?,sources.indexes[id]? with
    | some R,some idx =>
      let out:=compileDenseBank C E book prepared ci ei s R.period m L H next incoming enabled idx target targetCounts window
      (some out.1,out.2+9)
    | _,_ => (none,5)
  else (none,2)

def compileSingleton (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (sources : Sources) (s L H next incoming : Nat) (enabled : Bool)
    (target : Array Bool) (window : SourceWindow) :
    Table (2*ReplayMaps.count C.stateCount E.stateCount)
      (2*(MaskedClusterStage.dfa C E).stateCount)×Nat :=
  let out:=compilePointBank C E book ci ei s L H next incoming enabled sources.singleton target window
  (out.1,out.2+1)

theorem compileRun_lookup (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (sources : Sources) (id s m L H next incoming : Nat) (enabled : Bool)
    (target : Array Bool) (targetCounts : Array Nat) (window : SourceWindow)
    (R : Bounds) (idx : Index) (hK : sources.modulus=prepared.K)
    (hR : sources.runs[id]?=some R) (hi : sources.indexes[id]?=some idx) :
    compileRun C E book prepared ci ei sources id s m L H next incoming enabled target targetCounts window=
      (some (compileDenseBank C E book prepared ci ei s R.period m L H next incoming enabled idx target targetCounts window).1,
       (compileDenseBank C E book prepared ci ei s R.period m L H next incoming enabled idx target targetCounts window).2+9) := by
  simp only [compileRun,hK,if_true,hR,hi]

theorem compileRun_missing (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (sources : Sources) (id s m L H next incoming : Nat) (enabled : Bool)
    (target : Array Bool) (targetCounts : Array Nat) (window : SourceWindow)
    (hR : sources.runs[id]?=none) :
    (compileRun C E book prepared ci ei sources id s m L H next incoming enabled target targetCounts window).1=none ∧
      (compileRun C E book prepared ci ei sources id s m L H next incoming enabled target targetCounts window).2≤5 := by
  by_cases hK : sources.modulus=prepared.K <;> simp [compileRun,hK,hR]

/-- The history is read only by the semantic specification. -/
def currentBit (source : Array Bool) (removed : List Nat) (p : Nat) : Bool :=
  MaskedProgression.readMask source p && decide (p∉removed)

theorem member_current {source : Array Bool} {removed : List Nat} {base len step : Nat}
    {idx : Index} (hs : MaskedMutableProgression.Batch.IndexSpec source removed base len step idx)
    (p : Nat) (hlo : base≤p) (hhi : p<base+len) :
    (MaskedMutableProgression.member idx p).1=currentBit source removed p := by
  apply Bool.eq_iff_iff.mpr
  rw [MaskedMutableProgression.member_correct idx hs.good p,hs.live p,hs.base_eq,hs.len_eq]
  simp only [currentBit,Bool.and_eq_true,decide_eq_true_eq,MaskedMutableProgression.Batch.Current]
  constructor
  · exact fun h=>h.2.2
  · exact fun h=>⟨hlo,hhi,h⟩

def JumpAt (C E : DFA α) (w : Word α) (I s q L O : Nat)
    (source : Array Bool) (removed : List Nat) (target : Array Bool) (window : SourceWindow)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount) (k : Nat) : Prop :=
  MaskedClusterStage.direct C E w I (s+k*q) L O
    (window.allows (s+k*q) && currentBit source removed (s+k*q))
    (MaskedProgression.readMask target (s+k*q)) input=some output

def CursorStep (C E : DFA α) (w : Word α) (s q m L H next incoming : Nat)
    (enabled inMode outMode : Bool) (source : Array Bool) (removed : List Nat)
    (target : Array Bool) (window : SourceWindow)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount) : Prop :=
  modeAllowed enabled inMode=true ∧
    if outMode then
      ∃k,k≤m ∧ cursor s incoming inMode≤s+k*q ∧ next<s+k*q+L ∧
        JumpAt C E w (cursor s incoming inMode) s q L (s+m*q+H) source removed target window input output k
    else
      MaskedClusterStage.read C E (Spec.slice w (cursor s incoming inMode) next) input=output ∨
      ∃k,k≤m ∧ cursor s incoming inMode≤s+k*q ∧ s+k*q+L≤next ∧
        JumpAt C E w (cursor s incoming inMode) s q L next source removed target window input output k

theorem cursor_current (C E : DFA α) (w : Word α) (s q m L H next incoming : Nat)
    (enabled inMode outMode : Bool) (source : Array Bool) (removed : List Nat)
    (target : Array Bool) (window : SourceWindow) (idx : Index) (base len step : Nat)
    (hs : MaskedMutableProgression.Batch.IndexSpec source removed base len step idx)
    (hb : ∀k,k≤m→base≤s+k*q ∧ s+k*q<base+len)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount) :
    Mutable.CursorStep C E w s q m L H next incoming enabled inMode outMode idx target window input output ↔
      CursorStep C E w s q m L H next incoming enabled inMode outMode source removed target window input output := by
  have hj : ∀k,k≤m→∀O,Mutable.JumpAt C E w (cursor s incoming inMode) s q L O idx target window input output k ↔
      JumpAt C E w (cursor s incoming inMode) s q L O source removed target window input output k := by
    intro k hk O
    unfold Mutable.JumpAt JumpAt
    rw [member_current hs (s+k*q) (hb k hk).1 (hb k hk).2]
  unfold Mutable.CursorStep CursorStep
  apply and_congr Iff.rfl
  cases outMode with
  | false =>
    simp only [Bool.false_eq_true,if_false]
    apply or_congr Iff.rfl
    constructor
    · rintro ⟨k,hk,hI,hL,hj'⟩
      exact ⟨k,hk,hI,hL,(hj k hk next).mp hj'⟩
    · rintro ⟨k,hk,hI,hL,hj'⟩
      exact ⟨k,hk,hI,hL,(hj k hk next).mpr hj'⟩
  | true =>
    simp only [if_true]
    constructor
    · rintro ⟨k,hk,hI,hL,hj'⟩
      exact ⟨k,hk,hI,hL,(hj k hk (s+m*q+H)).mp hj'⟩
    · rintro ⟨k,hk,hI,hL,hj'⟩
      exact ⟨k,hk,hI,hL,(hj k hk (s+m*q+H)).mpr hj'⟩

theorem run_singleton_member {σ : Nat} (text : Array (Fin σ)) (fallback : Fin σ)
    (source : Array Bool) (K : Nat) (hK : 0<K) (removed : List Nat) (p : Nat) (hp : p≤text.size) :
    (MaskedMutableProgression.member (MaskedMutableProgression.Batch.run text fallback source K removed).singleton p).1=
      currentBit source removed p := by
  have hs:=(MaskedMutableProgression.Batch.run_valid text fallback source K hK removed).singleton
  exact member_current hs p (Nat.zero_le _) (by
    simpa only [MaskedMutableProgression.Batch.run,MaskedMutableProgression.Batch.eraseMany_n,
      MaskedMutableProgression.Batch.prepare,Nat.zero_add] using Nat.lt_succ_of_le hp)

end REWB.MaskedCluster.Mutable.Batch
