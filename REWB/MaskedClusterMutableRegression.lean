import REWB.MaskedClusterMutableBudget

/-! Source deletion changes an explicitly rebuilt bank while retaining
    the target use of the same occurrence and the old persistent bank.
    The executable audit additionally checks arbitrary masks, dense APs,
    shortening, interval gates and shared-cut queries after repeated erase.
-/
namespace REWB.MaskedCluster.Mutable.Regression

def one : DFA Bool := ⟨1,0,fun _ _=>0,fun _=>true⟩
def word : Word Bool := [true,false,true]
def source : Array Bool := #[false,true,false,true]
def target : Array Bool := #[false,true,false,false]
def window : SourceWindow := ⟨true,0,4⟩
def initial := (MaskedMutableProgression.build source 0 4 1).index
def erased := (MaskedMutableProgression.erase initial 1).index

def bank (idx : Index) :=
  (compilePointBank one one (ReplayMaps.prepare one.stateCount one.stateCount)
    (BoundaryApplication.Range.build one word) (BoundaryApplication.Range.build one word)
    1 1 1 3 0 false idx target window).1

def sourceAnswer (idx : Index) : Bool :=
  (bank idx).view (code _ true (ReplayMaps.encode (ReplayMaps.one one.stateCount one.stateCount)))
    (code _ false (MaskedClusterStage.encode one one .waiting))
    (code _ false (MaskedClusterStage.encode one one (.gap one.initial)))

def targetAnswer (idx : Index) : Bool :=
  (bank idx).view (code _ true (ReplayMaps.encode (ReplayMaps.one one.stateCount one.stateCount)))
    (code _ false (MaskedClusterStage.encode one one (.gap one.initial)))
    (code _ false (MaskedClusterStage.encode one one (.suffix one.initial)))

theorem certificate : MaskedLocalAnchor.Certificate (ArrayText.read word.toArray false) word.length
    1 1 [1] 1 3 none none 1 := by
  refine ⟨by decide,?_,by decide,Iff.rfl,?_,?_⟩
  · intro k hk
    have he : k=1 := by simpa only [List.mem_singleton] using hk
    subst k
    exact ⟨by decide,rfl⟩
  · intro p h
    cases h
  · intro p h
    cases h

theorem sourceAnswer_member (idx : Index) : sourceAnswer idx=(MaskedMutableProgression.member idx 1).1 := by
  apply Bool.eq_iff_iff.mpr
  rw [sourceAnswer,bank,compilePointBank_current one one _ word false 1 1 [1] 1 1 3 0 none none
    false true false false idx target window _ _ certificate (by decide) (by decide) (by intro h; cases h)]
  simp only [MaskedClusterStage.decode_encode,CursorStep,modeAllowed,cursor,exists_le_zero,
    Bool.not_false,Bool.true_or,Bool.false_eq_true,if_false,Nat.zero_mul,Nat.add_zero,JumpAt,
    MaskedClusterStage.direct_waiting]
  cases hm : (MaskedMutableProgression.member idx 1).1 <;>
    simp [hm,window,SourceWindow.gate,SourceWindow.allows,one,word,Spec.slice,DFA.run,MaskedClusterStage.read]

theorem targetAnswer_true (idx : Index) : targetAnswer idx=true := by
  rw [targetAnswer,bank]
  apply (compilePointBank_current one one _ word false 1 1 [1] 1 1 3 0 none none false true false false idx target window
    _ _ certificate (by decide) (by decide) (by intro h; cases h)).mpr
  simp only [MaskedClusterStage.decode_encode,CursorStep,modeAllowed,cursor,exists_le_zero,
    Bool.not_false,Bool.true_or,Bool.false_eq_true,if_false,Nat.zero_mul,Nat.add_zero,JumpAt,
    MaskedClusterStage.direct_gap]
  simp [one,word,target,MaskedProgression.readMask,Spec.slice,DFA.run,MaskedClusterStage.read]

theorem initial_valid : initial.Valid := MaskedMutableProgression.build_valid source 0 4 1
theorem erased_valid : erased.Valid := MaskedMutableProgression.erase_valid initial initial_valid 1

theorem initial_source : (MaskedMutableProgression.member initial 1).1=true := by
  apply (MaskedMutableProgression.member_correct initial initial_valid 1).mpr
  unfold initial
  rw [MaskedMutableProgression.build_live]
  decide

theorem erased_source : (MaskedMutableProgression.member erased 1).1=false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have hh:=(MaskedMutableProgression.member_correct erased erased_valid 1).mp h
  have hn:=(MaskedMutableProgression.erase_live initial initial_valid 1 1).mp hh
  exact hn.1 rfl

theorem rebuilt_source_deleted_target_retained :
    sourceAnswer initial=true ∧ sourceAnswer erased=false ∧
      targetAnswer initial=true ∧ targetAnswer erased=true := by
  rw [sourceAnswer_member,sourceAnswer_member,initial_source,erased_source,targetAnswer_true,targetAnswer_true]
  decide

/-- The old persistent bank still represents its old source snapshot;
    a source erase alone cannot silently repair that cached bank. -/
theorem old_snapshot_remains : sourceAnswer initial≠sourceAnswer erased := by
  rw [sourceAnswer_member,sourceAnswer_member,initial_source,erased_source]
  decide

theorem terminal_source_member : (MaskedMutableProgression.member erased word.length).1=true := by
  apply (MaskedMutableProgression.member_correct erased erased_valid word.length).mpr
  unfold erased
  rw [MaskedMutableProgression.erase_live initial initial_valid 1 word.length]
  constructor
  · decide
  · unfold initial
    rw [MaskedMutableProgression.build_live]
    decide

end REWB.MaskedCluster.Mutable.Regression
