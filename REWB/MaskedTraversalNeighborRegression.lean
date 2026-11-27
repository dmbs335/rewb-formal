import REWB.MaskedTraversalNeighborAnchors

namespace REWB.MaskedTraversalNeighbor.Regression

def before : MaskedClusterLeaders.State 6 :=
  (MaskedClusterLeaders.execute 6 4
    [.insert 0,.insert 2,.insert 10,.insert 12,.insert 20,.insert 22,.insert 30,.insert 32,.insert 40,.insert 42]).state

theorem distant_descriptor_unchanged :
    (MaskedClusterDescriptor.describeLeader (MaskedClusterLeaders.add 64 4 11 before).state 64 40).1=
      (MaskedClusterDescriptor.describeLeader before 64 40).1 := by decide

theorem actual_distant_key_unmarked :
    40∉(MaskedTraversalDirty.prepareChange before.leaders
      (MaskedClusterLeaders.add 64 4 11 before).state.leaders 64 11).keys := by decide

end REWB.MaskedTraversalNeighbor.Regression
