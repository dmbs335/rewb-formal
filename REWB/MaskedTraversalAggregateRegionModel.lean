import REWB.MaskedTraversalAggregateWindowPhysical
import REWB.MaskedTraversalAggregateSourceGate

/-! Physical part membership follows the actual position-indexed sparse
leaf model. The middle gate applies exactly to the leader positions in
the requested aggregate region; no physical cluster list is sorted or
enumerated at query time.
-/
namespace REWB.MaskedTraversalAggregate.Cells
open REWB.MaskedCluster REWB.MaskedFiniteAction
variable {α : Type} {C E : DFA α} {h : Nat}

theorem parts_mem (gate : Bool) (entries : List (Option (Mutable.Store.Entry C E))) (p : Part) :
    p∈parts gate entries ↔ ∃entry,some entry∈entries ∧ p=⟨entry.config,gate⟩ := by
  constructor
  · intro hp
    obtain ⟨value,hvalue,hp⟩:=List.mem_filterMap.mp hp
    cases value with
    | none=>cases hp
    | some entry=>exact ⟨entry,hvalue,(Option.some.inj hp).symm⟩
  · rintro ⟨entry,he,rfl⟩
    exact List.mem_filterMap.mpr ⟨some entry,he,rfl⟩

theorem regionParts_mem (entries : List (Option (Mutable.Store.Entry C E))) (lo hi : Nat) (horder : lo≤hi) (p : Part) :
    p∈regionParts entries lo hi ↔
      ∃first entry,entries[first]?=some (some entry) ∧ p=⟨entry.config,decide (lo≤first ∧ first<hi)⟩ := by
  simp only [regionParts,List.mem_append,parts_mem]
  constructor
  · rintro ((⟨entry,he,hp⟩|⟨entry,he,hp⟩)|⟨entry,he,hp⟩)
    · obtain ⟨i,hget⟩:=List.getElem?_of_mem he
      have hi' : i<lo := by
        by_cases hh : i<lo
        · exact hh
        · simp only [List.getElem?_take,hh,if_false] at hget; cases hget
      have horig : entries[i]?=some (some entry) := by
        simpa only [List.getElem?_take,hi',if_true] using hget
      refine ⟨i,entry,horig,?_⟩
      simpa only [show ¬(lo≤i ∧ i<hi) by omega,decide_false] using hp
    · obtain ⟨i,hget⟩:=List.getElem?_of_mem he
      have hi' : i<hi-lo := by
        by_cases hh : i<hi-lo
        · exact hh
        · simp only [Spec.slice,List.getElem?_take,hh,if_false] at hget; cases hget
      have horig : entries[lo+i]?=some (some entry) := by
        simpa only [Spec.slice,List.getElem?_take,hi',if_true,List.getElem?_drop] using hget
      refine ⟨lo+i,entry,horig,?_⟩
      simpa only [show lo≤lo+i ∧ lo+i<hi by omega,decide_true] using hp
    · obtain ⟨i,hget⟩:=List.getElem?_of_mem he
      have horig : entries[hi+i]?=some (some entry) := by simpa only [List.getElem?_drop] using hget
      refine ⟨hi+i,entry,horig,?_⟩
      simpa only [show ¬(lo≤hi+i ∧ hi+i<hi) by omega,decide_false] using hp
  · rintro ⟨i,entry,hget,hp⟩
    by_cases hbefore : i<lo
    · apply Or.inl; apply Or.inl
      refine ⟨entry,List.mem_of_getElem? (i:=i) ?_,?_⟩
      · simpa only [List.getElem?_take,hbefore,if_true] using hget
      · simpa only [show ¬(lo≤i ∧ i<hi) by omega,decide_false] using hp
    · by_cases hinside : i<hi
      · apply Or.inl; apply Or.inr
        refine ⟨entry,List.mem_of_getElem? (i:=i-lo) ?_,?_⟩
        · simpa only [Spec.slice,List.getElem?_take,show i-lo<hi-lo by omega,if_true,List.getElem?_drop,
            show lo+(i-lo)=i by omega] using hget
        · simpa only [show lo≤i ∧ i<hi by omega,decide_true] using hp
      · apply Or.inr
        refine ⟨entry,List.mem_of_getElem? (i:=i-hi) ?_,?_⟩
        · simpa only [List.getElem?_drop,show hi+(i-hi)=i by omega] using hget
        · simpa only [show ¬(lo≤i ∧ i<hi) by omega,decide_false] using hp

theorem plan_lower_le (partition : MaskedClusterLeaders.State h) (capacity old lo hi : Nat)
    (hv : MaskedClusterLeaders.Invariant old partition) (hc : capacity=2^h) :
    (Clip.plan partition.leaders capacity lo hi).lower≤lo := by
  have hp:=MaskedOrdered.Tree.pred_correct partition.leaders capacity (lo+1) hv.leadGood hv.leadFits hc
  cases he : (MaskedOrdered.Tree.pred partition.leaders capacity (lo+1)).1 with
  | none=>simp only [Clip.plan,he,Option.getD_none,Nat.le_refl]
  | some p=>
    rw [he] at hp
    simp only [Clip.plan,he,Option.getD_some]
    have hh:=hp.2.1
    omega

end REWB.MaskedTraversalAggregate.Cells
