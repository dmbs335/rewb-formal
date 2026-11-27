import REWB.MaskedClusterLeaderTrace

namespace REWB.MaskedClusterLeaders.Regression

def inserted : List Operation := [.insert 0,.insert 4,.insert 2]
def atThree := execute 3 8 (inserted++[.lower 3])
def atTwo := execute 3 8 (inserted++[.lower 3,.lower 2])

theorem dense_then_split :
    (execute 3 8 inserted).state.leaders.entries=[0] ∧
    atThree.state.leaders.entries=[0,2,4] := by decide

theorem stale_pair_does_not_restore_leader :
    atThree.generated=6 ∧ atThree.popped=4 ∧
    MaskedThresholdQueue.count atThree.state.queue=2 := by decide

theorem overlap_records_once :
    atTwo.popped=6 ∧ MaskedThresholdQueue.count atTwo.state.queue=0 ∧
    (execute 3 8 (inserted++[.lower 3,.lower 2,.lower 2])).popped=6 := by decide

theorem invalid_operations_ignored :
    (execute 3 8 (inserted++[.lower 3,.lower 7,.insert 8])).length=3 ∧
    (execute 3 8 (inserted++[.lower 3,.lower 7,.insert 8])).state.occurrences.entries=[0,2,4] := by decide

theorem born_due_records :
    (execute 3 3 [.insert 0,.insert 4,.insert 2,.lower 3]).state.leaders.entries=[0,2,4] ∧
    (execute 3 3 [.insert 0,.insert 4,.insert 2,.lower 3]).popped=4 := by decide

end REWB.MaskedClusterLeaders.Regression
