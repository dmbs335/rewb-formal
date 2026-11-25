import REWB.MaskedClusterCutCorrect
import REWB.MaskedClusterRegression

/-! Correlation regression: B accepts only the longer candidate, while
    the requested E result is possible only at the shorter candidate.
    Independent prefix/suffix witnesses both exist, but the actual
    shared-cut query rejects. The theorem checks the real query without
    evaluating an unnecessarily large fixed-pattern cut table in-kernel.
-/
namespace REWB.MaskedCluster.CutRegression
open REWB.MaskedCluster.Regression

def all : DFA Bool := ⟨1,0,fun _ _=>0,fun _=>true⟩
def word : Word Bool := [false,true]
def mask : Array Bool := #[true,false]
def window : SourceWindow := ⟨true,0,2⟩

theorem certificate : MaskedLocalAnchor.Certificate (ArrayText.read word.toArray false)
    word.length 0 2 [0] 0 2 none none 2 := by
  refine ⟨by decide,?_,by decide,Iff.rfl,?_,?_⟩
  · intro k hk
    have he : k=0 := by simpa only [List.mem_singleton] using hk
    subst k
    exact ⟨by decide,rfl⟩
  · intro p h
    cases h
  · intro p h
    cases h

def bank := (compilePointBank all last (ReplayMaps.prepare all.stateCount last.stateCount)
  (BoundaryApplication.Range.build all word) (BoundaryApplication.Range.build last word)
  0 2 2 2 0 false mask mask window).1

def result := Cut.queryBank last all last (Cut.build last all last word) bank false 0 1 2 2
  (code _ false (MaskedClusterStage.encode all last (.gap all.initial)))
  (code _ false (MaskedClusterStage.encode all last (.suffix last1)))

theorem result_correct : result.1.answer=true ↔
    ∃ L,1≤L ∧ L≤2 ∧ last.accepts (Spec.slice word 0 L) ∧
      CursorStep all last word 0 1 0 L 2 2 0 false false false mask mask (window.gate false)
        (.gap all.initial) (.suffix last1) := by
  have hh:=Cut.query_pointBank_correct last all last (ReplayMaps.prepare all.stateCount last.stateCount)
    word false 0 0 1 2 2 [0] 0 2 2 0 none none false false false false mask mask window
    (MaskedClusterStage.encode all last (.gap all.initial)) (MaskedClusterStage.encode all last (.suffix last1))
    certificate (by decide) (by decide) (by decide) rfl (by intro L hl hh; omega)
    (by decide) (by decide) (by intro h; cases h)
  simpa only [result,bank,MaskedClusterStage.decode_encode,Nat.zero_add] using hh

theorem separate_witnesses :
    last.accepts (Spec.slice word 0 2) ∧
      CursorStep all last word 0 1 0 1 2 2 0 false false false mask mask (window.gate false)
        (.gap all.initial) (.suffix last1) := by
  constructor
  · unfold DFA.accepts
    decide
  · simp only [CursorStep,exists_le_zero,modeAllowed,Bool.not_false,Bool.true_or,
      Bool.false_eq_true,if_false,cursor,Nat.zero_mul,Nat.add_zero]
    unfold JumpAt
    decide

/-- There is no single length witnessing both conditions. -/
theorem rejects_mixed_cuts : result.1.answer=false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨L,hl,hh,hB,hstep⟩:=result_correct.mp h
  have hcases : L=1 ∨ L=2 := by omega
  rcases hcases with rfl|rfl
  · have hn : ¬last.accepts (Spec.slice word 0 1) := by unfold DFA.accepts; decide
    exact hn hB
  · have hn : ¬CursorStep all last word 0 1 0 2 2 2 0 false false false mask mask (window.gate false)
        (.gap all.initial) (.suffix last1) := by
      simp only [CursorStep,exists_le_zero,modeAllowed,Bool.not_false,Bool.true_or,
        Bool.false_eq_true,if_false,cursor,Nat.zero_mul,Nat.add_zero]
      unfold JumpAt
      decide
    exact hn hstep

end REWB.MaskedCluster.CutRegression
