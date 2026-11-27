import REWB.MaskedClusterBankBudget
import REWB.MaskedClusterRegression
import REWB.MaskedFiniteActionTree

/-! Kernel checks for the actual replay-pair universe and source-gate
    preservation. The runtime audit checks shortened real-text blocks
    and noncommuting lazy actions on actual dense/singleton banks.
-/
namespace REWB.MaskedCluster.BankRegression
open REWB.MaskedCluster.Regression

theorem universe_size : ReplayMaps.count 2 2=16 ∧ 2*ReplayMaps.count 2 2=32 := by
  simp only [ReplayMaps.count_eq]
  decide

def falseMap := ReplayMaps.word seen last [false]
def trueMap := ReplayMaps.word seen last [true]

theorem maps_noncommute : ReplayMaps.mul falseMap trueMap≠ReplayMaps.mul trueMap falseMap := by decide

theorem source_gate_retained (gate : Bool) :
    codeMode _ ((bankAction falseMap).get (code _ gate (ReplayMaps.encode trueMap)))=gate := by
  rw [bankAction_gate,codeMode_code]

theorem constant_word_roundtrip :
    ReplayMaps.decode 2 2 (ReplayMaps.encode (ReplayMaps.mul falseMap trueMap))=
      ReplayMaps.mul falseMap trueMap := ReplayMaps.decode_encode _

end REWB.MaskedCluster.BankRegression
