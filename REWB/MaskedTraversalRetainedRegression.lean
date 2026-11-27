import REWB.MaskedTraversalRetainedTransitions

namespace REWB.MaskedTraversalRetained.Regression

def descriptor : MaskedClusterDescriptor.Descriptor :=
  ⟨2,10,4,2,some 22,some 6,some 26⟩

theorem exact_grid : copies descriptor=[2,6,10] := by decide

theorem reset_slot_and_retention :
    let a:=MaskedTraversalRepair.anchorsLoop 5 [1,3,1]
      #[some 9,some 8,none,some 7,some 6] 0
    a.1=#[some 9,some 5,none,some 5,some 6] ∧ a.2=13 := by decide

def before : MaskedClusterLeaders.State 6 :=
  (MaskedClusterLeaders.shorten 64 9 (MaskedClusterLeaders.execute 6 9
    [.insert 0,.insert 2,.insert 10,.insert 12,.insert 20,.insert 22,
     .insert 30,.insert 32]).state).state

theorem overlap_event_marks_left_cluster :
    let crossing:=MaskedClusterLeaders.shorten 64 8 before
    let dirty:=MaskedTraversalDirty.crossing before crossing 64 (MaskedTraversalDirty.empty 6)
    0∈dirty.keys.positions ∧ 10∈dirty.keys.positions := by decide

theorem crossing_preserves_literal_descriptor :
    (MaskedClusterDescriptor.describeLeader (MaskedClusterLeaders.shorten 64 8 before).state 64 0).1=
      (MaskedClusterDescriptor.describeLeader before 64 0).1 := by decide

end REWB.MaskedTraversalRetained.Regression
