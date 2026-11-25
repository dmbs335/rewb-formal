import REWB.MaskedTraversalAggregateClipCells

/-! Source gating for exact owned physical positions. Unselected banks
retain their original full source window; selected banks use the two
actual boundary replacements. This does not alter target eligibility.
-/
namespace REWB.MaskedTraversalAggregate.Cells
open REWB.MaskedCluster REWB.MaskedOrdered REWB.MaskedOrdered.Tree
variable {h : Nat}

def windowFor (plan : Clip.Plan) (original : SourceWindow) (first lo hi : Nat) : SourceWindow :=
  if first∈plan.keys then ⟨true,lo,hi⟩ else original

theorem gated_allows (window : SourceWindow) (enabled : Bool) (p : Nat) :
    (window.gate enabled).allows p=true ↔ enabled=true ∧ window.allows p=true := by
  simp only [SourceWindow.gate,SourceWindow.allows,Bool.and_eq_true,and_assoc]

theorem windowFor_selection (leaders : Tree h) (capacity lo hi first position : Nat)
    (original : SourceWindow) (allowed : original.allows position=true)
    (hg : leaders.Good) (hf : leaders.Fits 0) (hc : capacity=2^h)
    (ho : PredSpec leaders.entries (position+1) (some first)) :
    ((windowFor (Clip.plan leaders capacity lo hi) original first lo hi).gate
      (decide ((Clip.plan leaders capacity lo hi).lower≤first ∧ first<hi))).allows position=true ↔
      lo≤position ∧ position<hi := by
  have hs:=Clip.plan_selection leaders capacity lo hi first position hg hf hc ho
  rw [gated_allows]
  simp only [decide_eq_true_eq]
  by_cases hk : first∈(Clip.plan leaders capacity lo hi).keys
  · simpa only [windowFor,hk,if_true,SourceWindow.allows,Bool.true_and,decide_eq_true_eq,
      Clip.Selected,true_implies,and_assoc] using hs
  · simpa only [windowFor,hk,if_false,allowed,and_true,Clip.Selected,false_implies] using hs

theorem windowFor_current (leaders : Tree h) (capacity lo hi first position : Nat)
    (original : SourceWindow) (allowed : original.allows position=true)
    (source : Array Bool) (removed : List Nat)
    (hg : leaders.Good) (hf : leaders.Fits 0) (hc : capacity=2^h)
    (ho : PredSpec leaders.entries (position+1) (some first)) :
    (((windowFor (Clip.plan leaders capacity lo hi) original first lo hi).gate
      (decide ((Clip.plan leaders capacity lo hi).lower≤first ∧ first<hi))).allows position &&
        Mutable.Batch.currentBit source removed position)=true ↔
      lo≤position ∧ position<hi ∧ Mutable.Batch.currentBit source removed position=true := by
  rw [Bool.and_eq_true,windowFor_selection leaders capacity lo hi first position original allowed hg hf hc ho]
  exact and_assoc

end REWB.MaskedTraversalAggregate.Cells
