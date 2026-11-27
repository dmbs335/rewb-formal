import REWB.MaskedThresholdValidation
import REWB.MaskedThresholdQueueOrder

namespace REWB.MaskedThresholdEvents.Regression
open REWB.MaskedThresholdQueue

def first := add 3 8 0 .empty .empty
def second := add 3 8 4 first.insertion.tree first.queue
def middle := add 3 8 2 second.insertion.tree second.queue
def duplicate := add 3 8 2 middle.insertion.tree middle.queue
def atThree := shorten 4 3 middle.insertion.tree 8 middle.queue
def atTwo := shorten 4 2 middle.insertion.tree 8 atThree.pending

theorem actual_generations :
    first.generated=0 ∧ second.generated=2 ∧ middle.generated=4 ∧
      count middle.queue=6 ∧ duplicate.generated=0 ∧ count duplicate.queue=6 := by decide

theorem obsolete_pair_filtered :
    atThree.popped=4 ∧ atThree.live.length=2 ∧ count atThree.pending=2 ∧
      atThree.live.all (fun e=>decide (e.value.edge≠(0,4)))=true := by decide

theorem descending_thresholds :
    ((drain 4 3 middle.queue).due.map Entry.key)=[7,4,3,3] := by decide

theorem future_thresholds_once :
    atTwo.popped=2 ∧ atTwo.live.length=2 ∧ count atTwo.pending=0 ∧
      (shorten 4 2 middle.insertion.tree 8 atTwo.pending).popped=0 := by decide

theorem original_queue_preserved :
    count second.queue=2 ∧ count middle.queue=6 ∧
      (entries second.queue).map Entry.key=[4,7] := by decide

end REWB.MaskedThresholdEvents.Regression
