import REWB.MaskedClusterMutableCursor

/-! Chronological cursor semantics for the current persistent source
    snapshot. Source jumps test actual current membership; target jumps
    continue to test the original immutable target mask.
-/
namespace REWB.MaskedCluster.Mutable
variable {α : Type}

def JumpAt (C E : DFA α) (w : Word α) (I s q L O : Nat) (idx : Index)
    (target : Array Bool) (window : SourceWindow)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount) (k : Nat) : Prop :=
  MaskedClusterStage.direct C E w I (s+k*q) L O
    (window.allows (s+k*q) && (MaskedMutableProgression.member idx (s+k*q)).1)
    (MaskedProgression.readMask target (s+k*q)) input=some output

def CursorStep (C E : DFA α) (w : Word α) (s q m L H next incoming : Nat)
    (enabled inMode outMode : Bool) (idx : Index) (target : Array Bool) (window : SourceWindow)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount) : Prop :=
  modeAllowed enabled inMode=true ∧
    if outMode then
      ∃k,k≤m ∧ cursor s incoming inMode≤s+k*q ∧ next<s+k*q+L ∧
        JumpAt C E w (cursor s incoming inMode) s q L (s+m*q+H) idx target window input output k
    else
      MaskedClusterStage.read C E (Spec.slice w (cursor s incoming inMode) next) input=output ∨
      ∃k,k≤m ∧ cursor s incoming inMode≤s+k*q ∧ s+k*q+L≤next ∧
        JumpAt C E w (cursor s incoming inMode) s q L next idx target window input output k

theorem cursorStep_snapshot (C E : DFA α) (w : Word α) (s q m L H next incoming : Nat)
    (enabled inMode outMode : Bool) (idx : Index) (target : Array Bool) (window : SourceWindow)
    (input output : MaskedClusterStage.State C.stateCount E.stateCount) :
    REWB.MaskedCluster.CursorStep C E w s q m L H next incoming enabled inMode outMode (snapshot idx) target window input output ↔
      CursorStep C E w s q m L H next incoming enabled inMode outMode idx target window input output := by
  simp only [REWB.MaskedCluster.CursorStep,CursorStep,REWB.MaskedCluster.JumpAt,JumpAt,snapshot_read]

theorem current_source_bit (idx : Index) (hv : idx.Valid) (window : SourceWindow) (p : Nat) :
    (window.allows p && (MaskedMutableProgression.member idx p).1)=true ↔
      window.allows p=true ∧ idx.Live p := by
  rw [Bool.and_eq_true,MaskedMutableProgression.member_correct idx hv p]

end REWB.MaskedCluster.Mutable
