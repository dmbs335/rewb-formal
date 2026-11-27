import REWB.MaskedSuffixClassCost
import REWB.MaskedOrderedOwnerRegression

/-! Kernel regressions for complete retained classes and the first
equal-depth threshold. Runtime preparation is independently exercised
in audits/masked_suffix_class_smoke.lean. -/
namespace REWB.MaskedSuffixClass.Regression
open REWB.MaskedRunDiscovery REWB.BoundaryApplication

theorem empty_class :
    ∃out,(query (prepare (#[] : Array (Fin 2)) 0) 0 0).value=some out ∧
      ∀k,k∈out.record.state.tree.entries ↔ k=0 := by
  obtain ⟨out,ho,_,hf⟩:=query_complete (#[] : Array (Fin 2)) 0 0 0 (by decide)
  refine ⟨out,ho,?_⟩
  intro k
  rw [hf k]
  constructor
  · intro hk
    have hb:=hk.1
    change k+0≤0 at hb
    omega
  · rintro rfl
    exact ⟨Nat.le_refl 0,rfl⟩

theorem empty_positive_rejected :
    (query (prepare (#[] : Array (Fin 2)) 0) 0 1).value=none :=
  query_invalid _ _ _ _ (by decide)

theorem epsilon_class (text : Array (Fin σ)) (fallback : Fin σ)
    (p : Fin (text.size+1)) :
    ∃out,(query (prepare text fallback) p 0).value=some out ∧
      ∀k,k∈out.record.state.tree.entries ↔ k≤text.size := by
  obtain ⟨out,ho,_,hf⟩:=query_complete text fallback p 0 (Nat.zero_le _)
  refine ⟨out,ho,?_⟩
  intro k
  rw [hf k]
  constructor
  · exact fun hk=>by have hh:=hk.1; omega
  · exact fun hk=>⟨by omega,rfl⟩

def partialText : Array (Fin 2) := #[0,1,1,0,1,1]

theorem partial_occurs : ∀k : Fin 7,
    Occurs (ArrayText.read partialText 0) 6 0 1 k.val ↔ k.val=0 ∨ k.val=3 := by
  unfold Occurs
  decide

/-- Prefix length one lies strictly inside the common `011` edge. The
actual prepared query still returns both occurrences, not one leaf. -/
theorem partial_class :
    ∃out,(query (prepare partialText 0) 0 1).value=some out ∧
      ∀k,k∈out.record.state.tree.entries ↔ k=0 ∨ k=3 := by
  obtain ⟨out,ho,_,hf⟩:=query_complete partialText 0 0 1 (by decide)
  refine ⟨out,ho,?_⟩
  intro k
  rw [hf k]
  constructor
  · intro hk
    have hb:=hk.1
    have hb' : k<7 := by change k+1≤6 at hb; omega
    exact (partial_occurs ⟨k,hb'⟩).mp hk
  · rintro (rfl|rfl) <;> unfold Occurs <;> decide

def refinementHit := StartLocate.query 3
  (StartLocate.build 3 (annotate MaskedOrdered.Owner.Regression.refinements 0).tree)
  (⟨0,by decide⟩ : Fin 7) 4

/-- The lower depth-four refinement has [0,2], while its complete
ancestor has [0,1,2]. Cached parent jumps must return the ancestor. -/
theorem equal_depth_lift : refinementHit.value.map (fun out=>out.cell.payload)=some 0 := by
  decide

theorem retained_complete_ancestor :
    (refinementHit.value.bind fun hit=>
      MaskedOrdered.Owner.Regression.saved.nodes[hit.cell.payload]?).map
      (fun r=>r.state.tree.entries)=some [0,1,2] := by
  decide

end REWB.MaskedSuffixClass.Regression
