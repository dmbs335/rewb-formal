import REWB.MaskedTraversalRepairCoherenceCost

namespace REWB.MaskedTraversalRepairCoherence.Regression
open REWB.MaskedCluster REWB.MaskedTraversalAggregate
variable {α : Type} {C E : DFA α} {h h' n : Nat}

theorem empty_anchors (env : Env C E n h') (partition : MaskedClusterLeaders.State h) (capacity L : Nat)
    (anchors : Array (Option Nat)) (st : Mutable.Store.State C E) (tree : BankTree C E h) :
    (apply env partition capacity L anchors (MaskedTraversalDirty.empty h) st tree).anchors=anchors := rfl

theorem empty_slots (env : Env C E n h') (partition : MaskedClusterLeaders.State h) (capacity L : Nat)
    (anchors : Array (Option Nat)) (st : Mutable.Store.State C E) (tree : BankTree C E h) :
    (apply env partition capacity L anchors (MaskedTraversalDirty.empty h) st tree).store.slots=st.slots := rfl

theorem empty_tree (env : Env C E n h') (partition : MaskedClusterLeaders.State h) (capacity L : Nat)
    (anchors : Array (Option Nat)) (st : Mutable.Store.State C E) (tree : BankTree C E h) :
    (apply env partition capacity L anchors (MaskedTraversalDirty.empty h) st tree).tree=tree := rfl

theorem empty_work (env : Env C E n h') (partition : MaskedClusterLeaders.State h) (capacity L : Nat)
    (anchors : Array (Option Nat)) (st : Mutable.Store.State C E) (tree : BankTree C E h) :
    (apply env partition capacity L anchors (MaskedTraversalDirty.empty h) st tree).work=16 := by
  change (1+(st.repairWork+1-st.repairWork)+4)+2+(st.repairWork+1+1-(st.repairWork+1))+0+0+7=16
  omega

/-- An empty dirty set cannot keep H=8 at this actual overlap crossing;
the retained-certificate premise detects the missing reset. -/
theorem overlap_crossing_requires_reset (f : Nat→α) :
    ¬MaskedLocalAnchor.Certificate f 30 0 7 [] 0 7 none none 8 := by
  intro hh
  have hm:=hh.overlap
  omega

end REWB.MaskedTraversalRepairCoherence.Regression
