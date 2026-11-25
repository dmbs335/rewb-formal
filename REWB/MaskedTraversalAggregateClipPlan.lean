import REWB.MaskedTraversalAggregate
import REWB.MaskedOrderedQuery

/-! Two actual leader predecessors suffice for a physical source window.
The gate interval is widened only to the lower boundary leader. Every
unclipped leader inside that interval has all its owned positions inside
the requested window. This proof uses exact predecessor semantics, not
enumeration of a dense progression or a scan of the occurrence list.
-/
namespace REWB.MaskedTraversalAggregate.Clip
open REWB.MaskedOrdered REWB.MaskedOrdered.Tree
variable {h : Nat}

structure Plan where
  lower : Nat
  keys : List Nat
  work : Nat
  deriving Repr

def selected (left right : Option Nat) : List Nat :=
  left.toList++if right=left then [] else right.toList

theorem selected_mem (left right : Option Nat) (p : Nat) :
    p∈selected left right ↔ left=some p ∨ right=some p := by
  cases left <;> cases right <;> simp [selected,eq_comm] <;> omega

theorem selected_length (left right : Option Nat) : (selected left right).length≤2 := by
  cases left <;> cases right <;> simp only [selected,Option.toList,List.length_append]
  all_goals split <;> simp

theorem selected_nodup (left right : Option Nat) : (selected left right).Nodup := by
  cases left <;> cases right <;> simp [selected]
  split <;> simp_all [eq_comm]

def plan (leaders : Tree h) (capacity lo hi : Nat) : Plan :=
  let left:=Tree.pred leaders capacity (lo+1)
  let right:=Tree.pred leaders capacity hi
  ⟨left.1.getD lo,selected left.1 right.1,left.2+right.2+7⟩

theorem plan_length (leaders : Tree h) (capacity lo hi : Nat) :
    (plan leaders capacity lo hi).keys.length≤2 := selected_length _ _

theorem plan_nodup (leaders : Tree h) (capacity lo hi : Nat) :
    (plan leaders capacity lo hi).keys.Nodup := selected_nodup _ _

theorem plan_work (leaders : Tree h) (capacity lo hi : Nat) :
    (plan leaders capacity lo hi).work≤14*h+13 := by
  have hl:=Tree.pred_work leaders capacity (lo+1)
  have hr:=Tree.pred_work leaders capacity hi
  simp only [plan]
  omega

def Selected (p : Plan) (lo hi first position : Nat) : Prop :=
  p.lower≤first ∧ first<hi ∧ (first∈p.keys→lo≤position ∧ position<hi)

theorem predecessor_selection (leaders : List Nat) (lo hi first position : Nat)
    (left right : Option Nat) (hl : PredSpec leaders (lo+1) left)
    (hr : PredSpec leaders hi right) (ho : PredSpec leaders (position+1) (some first)) :
    (left.getD lo≤first ∧ first<hi ∧
      (first∈selected left right→lo≤position ∧ position<hi)) ↔ lo≤position ∧ position<hi := by
  have hfirst:=ho.1
  have hle:=ho.2.1
  constructor
  · rintro ⟨hlo,hhi,hclip⟩
    have lower : lo≤position := by
      by_cases hp : lo≤position
      · exact hp
      · cases left with
        | none =>
          have hh:=hl first hfirst
          omega
        | some a =>
          have hh:=hl.2.2 first hfirst (by omega)
          have he : a=first := by simpa only [Option.getD_some] using Nat.le_antisymm hlo hh
          have inside:=hclip ((selected_mem _ _ first).mpr (Or.inl (congrArg some he)))
          exact inside.1
    have upper : position<hi := by
      by_cases hp : position<hi
      · exact hp
      · cases right with
        | none =>
          have hh:=hr first hfirst
          omega
        | some b =>
          have hab:=hr.2.2 first hfirst hhi
          have hba:=ho.2.2 b hr.1 (by have hh:=hr.2.1; omega)
          have he : b=first := Nat.le_antisymm hba hab
          exact (hclip ((selected_mem _ _ first).mpr (Or.inr (congrArg some he)))).2
    exact ⟨lower,upper⟩
  · intro hp
    refine ⟨?_,by omega,fun _=>hp⟩
    cases left with
    | none =>
      have hh:=hl first hfirst
      change lo≤first
      omega
    | some a =>
      have hbound:=hl.2.1
      exact ho.2.2 a hl.1 (by omega)

theorem plan_selection (leaders : Tree h) (capacity lo hi first position : Nat)
    (hg : leaders.Good) (hf : leaders.Fits 0) (hc : capacity=2^h)
    (ho : PredSpec leaders.entries (position+1) (some first)) :
    Selected (plan leaders capacity lo hi) lo hi first position ↔ lo≤position ∧ position<hi :=
  predecessor_selection leaders.entries lo hi first position _ _
    (Tree.pred_correct leaders capacity (lo+1) hg hf hc)
    (Tree.pred_correct leaders capacity hi hg hf hc) ho

end REWB.MaskedTraversalAggregate.Clip
