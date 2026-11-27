import REWB.MaskedClusterCursorBudget
import REWB.MaskedClusterRegression

/-! Kernel regressions for source-only clipping, singleton incoming
    overshoot, no-jump transitions, and exact cursor-code round trips.
    The executable audit additionally compares all four blocks and their
    materialized composition against literal chronological text scans.
-/
namespace REWB.MaskedCluster.CursorRegression
open REWB.MaskedCluster.Regression

def disabled : SourceWindow := ⟨false,0,5⟩
def excludesOne : SourceWindow := ⟨true,3,5⟩
def full : SourceWindow := ⟨true,0,5⟩

theorem window_endpoints :
    (SourceWindow.mk true 0 0).allows 0=false ∧
    (SourceWindow.mk true 4 2).allows 3=false ∧
    (SourceWindow.mk true 1 3).allows 1=true ∧
    (SourceWindow.mk true 1 3).allows 3=false := by decide

theorem point_certificate : MaskedLocalAnchor.Certificate
    (ArrayText.read singletonWord.toArray false) singletonWord.length 1 1 [1] 1 5 none none 3 := by
  refine ⟨by decide,?_,by decide,by decide,?_,?_⟩
  · intro k hk
    have he : k=1 := by simpa only [List.mem_singleton] using hk
    subst k
    exact ⟨by decide,rfl⟩
  · intro p hp
    cases hp
  · intro p hp
    cases hp

def pointExample (window : SourceWindow) : CursorBlocks (MaskedClusterStage.dfa seen last).stateCount :=
  (compilePoint seen last (BoundaryApplication.Range.build seen singletonWord)
    (BoundaryApplication.Range.build last singletonWord) 1 1 3 5 2 true
    singletonMask singletonMask window).1

theorem pointExample_correct (window : SourceWindow) : BlockDenotes seen last (pointExample window)
    (fun input output=>CursorStep seen last singletonWord 1 1 0 1 3 5 2 true input output
      singletonMask singletonMask window) := by
  exact compilePoint_correct seen last singletonWord false 1 1 [1] 1 3 5 2 none none true
    singletonMask singletonMask window point_certificate (by decide) (by decide) (by intro _; decide)

/-- The sole target lies outside the source report interval, but the
    target jump is retained. This would fail if both masks were clipped. -/
theorem target_outside_source_window :
    ((((pointExample excludesOne).get false false).cells.get (MaskedClusterStage.encode seen last (.gap seen1))).get
      (MaskedClusterStage.encode seen last (.suffix last1)))=true := by
  apply (pointExample_correct excludesOne false false _ _).mpr
  simp only [CursorStep,MaskedClusterStage.decode_encode,exists_le_zero,modeAllowed,
    Bool.not_false,Bool.true_or,Bool.false_eq_true,if_false,cursor,Nat.zero_mul,Nat.add_zero]
  unfold JumpAt
  decide

theorem disabled_source_has_no_source_jump :
    ((((pointExample disabled).get false false).cells.get (MaskedClusterStage.encode seen last .waiting)).get
      (MaskedClusterStage.encode seen last (.gap seen1)))=false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have hs:=(pointExample_correct disabled false false _ _).mp h
  simp only [CursorStep,MaskedClusterStage.decode_encode,exists_le_zero,modeAllowed,
    Bool.not_false,Bool.true_or,Bool.false_eq_true,if_false,cursor,Nat.zero_mul,Nat.add_zero] at hs
  have hn : ¬(True ∧
      (MaskedClusterStage.read seen last (Spec.slice singletonWord 1 5) .waiting=.gap seen1 ∨
      (1≤1 ∧ 1+1≤5 ∧ JumpAt seen last singletonWord 1 1 1 1 5 singletonMask singletonMask disabled
        .waiting (.gap seen1) 0))) := by unfold JumpAt; decide
  exact hn hs

theorem incoming_no_jump_survives :
    ((((pointExample disabled).get true false).cells.get (MaskedClusterStage.encode seen last .waiting)).get
      (MaskedClusterStage.encode seen last .waiting))=true := by
  apply (pointExample_correct disabled true false _ _).mpr
  simp only [CursorStep,MaskedClusterStage.decode_encode,exists_le_zero,modeAllowed,
    Bool.not_true,Bool.false_or,Bool.false_eq_true,if_false,cursor,if_true,Nat.zero_mul,Nat.add_zero]
  unfold JumpAt
  decide

theorem incoming_passed_singleton :
    ((((pointExample full).get true false).cells.get (MaskedClusterStage.encode seen last .waiting)).get
      (MaskedClusterStage.encode seen last (.gap seen1)))=false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have hs:=(pointExample_correct full true false _ _).mp h
  simp only [CursorStep,MaskedClusterStage.decode_encode,exists_le_zero,modeAllowed,
    Bool.not_true,Bool.false_or,Bool.false_eq_true,if_false,cursor,if_true,Nat.zero_mul,Nat.add_zero] at hs
  have hn : ¬(True ∧
      (MaskedClusterStage.read seen last (Spec.slice singletonWord 2 5) .waiting=.gap seen1 ∨
      (2≤1 ∧ 1+1≤5 ∧ JumpAt seen last singletonWord 2 1 1 1 5 singletonMask singletonMask full
        .waiting (.gap seen1) 0))) := by unfold JumpAt; decide
  exact hn hs

end REWB.MaskedCluster.CursorRegression
