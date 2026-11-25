import REWB.MaskedTraversalContextCost

namespace REWB.MaskedTraversalContext.Regression

def partition : MaskedClusterLeaders.State 3 :=
  (MaskedClusterLeaders.execute 3 4 [.insert 0,.insert 3,.insert 6]).state

theorem one_successor :
    (successors partition.leaders 8 [0] (MaskedTraversalDirty.empty 3)).keys.positions=[3] := by decide

theorem adjacent_resets :
    (successors partition.leaders 8 [0,3] (MaskedTraversalDirty.empty 3)).keys.positions=[6,3] := by decide

theorem invalid_reset_has_no_successor :
    (successors partition.leaders 8 [1,2,7] (MaskedTraversalDirty.empty 3)).keys.positions=[] := by decide

theorem last_reset_has_no_successor :
    (successors partition.leaders 8 [6] (MaskedTraversalDirty.empty 3)).keys.positions=[] := by decide

end REWB.MaskedTraversalContext.Regression
