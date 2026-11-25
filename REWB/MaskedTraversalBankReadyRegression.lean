import REWB.MaskedTraversalBankReadySemantics

namespace REWB.MaskedTraversalBankReady.Regression

theorem missing_anchor : readAnchor #[] 7 4=4 := rfl

theorem retained_anchor : readAnchor #[none,some 9] 1 4=9 := rfl

theorem reset_selected : readAnchor (resetAnchor #[some 8,some 9] 1 4) 1 4=4 :=
  resetAnchor_read _ _ _ (by decide)

theorem no_previous :
    (incoming (MaskedClusterLeaders.empty 3) 8 2 4 #[some 9]).cursor=2 ∧
      (incoming (MaskedClusterLeaders.empty 3) 8 2 4 #[some 9]).enabled=false := by
  decide

theorem missing_descriptor (catalog : MaskedRunCatalog.Index)
    (classes : MaskedSuffixClass.Index n h) :
    (prepare (MaskedClusterLeaders.empty 3) 8 2 4 #[some 9]
      ⟨true,0,8⟩ catalog classes).1=none :=
  prepare_none _ _ _ _ _ _ _ _ (by decide)

end REWB.MaskedTraversalBankReady.Regression
