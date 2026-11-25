import REWB.MaskedTraversalRepairCost

namespace REWB.MaskedTraversalRepair.Regression

theorem anchor_pass_selected :
    (anchorsLoop 4 [2,0,1] #[some 8,some 9,some 10] 0).1=#[some 4,some 4,some 4] := by decide

theorem anchor_pass_keeps_other :
    (anchorsLoop 4 [2,0] #[some 8,some 9,some 10] 0).1=#[some 4,some 9,some 4] := by decide

theorem anchor_outside_defaults :
    MaskedTraversalBankReady.readAnchor (anchorsLoop 4 [99] #[some 8] 0).1 99 4=4 := by decide

theorem anchor_pass_count : (anchorsLoop 4 [2,0,1] #[some 8,some 9,some 10] 7).2=20 := rfl

end REWB.MaskedTraversalRepair.Regression
