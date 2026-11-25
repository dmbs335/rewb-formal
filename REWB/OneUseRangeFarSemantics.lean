import REWB.OneUseRangeFarSelection

/-! The exact meaning of a selected immutable all-start row on a
prefix. All source and target boundaries remain original coordinates.
This is a substitution theorem for a row whose bits have already been
proved correct, not a construction of such a row. -/
namespace REWB.OneUseRange.FarSelection
open REWB.BoundaryApplication REWB.BoundaryRange REWB.Spec
variable {α : Type} {σ : Nat}

theorem prefix_slice (w : Word α) (grid a b : Nat) (hb : b≤grid) :
    slice (w.take grid) a b=slice w a b := by
  simp only [slice,List.drop_take,List.take_take]
  rw [Nat.min_eq_left (show b-a≤grid-a by omega)]

theorem masked_prefix (B C E : DFA (Fin σ)) (w : Word (Fin σ)) (grid right i : Nat)
    (hgr : grid≤right) (hr : right≤w.length) :
    Spec.maskedStart B C (variant E (key (build E w) grid right).1)
      (w.take grid) (fun _=>true) i ↔
      ∃a j t,i≤a ∧ a≤j ∧ j≤t ∧ t≤grid ∧ slice w i a=slice w j t ∧
        B.accepts (slice w i a) ∧ C.accepts (slice w a j) ∧ E.accepts (slice w t right) := by
  rw [key_variant]
  have hg : grid≤w.length := by omega
  have hlen : (w.take grid).length=grid := by rw [List.length_take,Nat.min_eq_left hg]
  constructor
  · rintro ⟨a,j,t,hia,haj,hjt,ht,_,he,hB,hC,hE⟩
    rw [hlen] at ht hE
    rw [prefix_slice w grid i a (by omega),prefix_slice w grid j t ht] at he
    rw [prefix_slice w grid i a (by omega)] at hB
    rw [prefix_slice w grid a j (by omega)] at hC
    rw [prefix_slice w grid t grid (Nat.le_refl _),Automata.tail_slice E w t grid right ht hgr hr] at hE
    exact ⟨a,j,t,hia,haj,hjt,ht,he,hB,hC,hE⟩
  · rintro ⟨a,j,t,hia,haj,hjt,ht,he,hB,hC,hE⟩
    refine ⟨a,j,t,hia,haj,hjt,by rw [hlen]; exact ht,rfl,?_,?_,?_,?_⟩
    · rwa [prefix_slice w grid i a (by omega),prefix_slice w grid j t ht]
    · rwa [prefix_slice w grid i a (by omega)]
    · rwa [prefix_slice w grid a j (by omega)]
    · rw [hlen,prefix_slice w grid t grid (Nat.le_refl _),Automata.tail_slice E w t grid right ht hgr hr]
      exact hE

theorem farTarget_iff (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (left right grid : Nat)
    (hgr : grid≤right) (hr : right≤w.length) :
    Border.FarTarget A B C E w left right grid ↔
      ∃i,left≤i ∧ i≤grid ∧ A.accepts (slice w left i) ∧
        Spec.maskedStart B C (variant E (key (build E w) grid right).1)
          (w.take grid) (fun _=>true) i := by
  simp only [masked_prefix B C E w grid right _ hgr hr]
  constructor
  · rintro ⟨i,t,h,htg⟩
    obtain ⟨a,j,hli,hia,haj,hjt,_,he,hA,hB,hC,hE⟩:=
      (Border.at_iff_cuts A B C E w left right i t hr).mp h
    exact ⟨i,hli,by omega,hA,a,j,t,hia,haj,hjt,htg,he,hB,hC,hE⟩
  · rintro ⟨i,hli,_,hA,a,j,t,hia,haj,hjt,htg,he,hB,hC,hE⟩
    exact ⟨i,t,(Border.at_iff_cuts A B C E w left right i t hr).mpr
      ⟨a,j,hli,hia,haj,hjt,by omega,he,hA,hB,hC,hE⟩,htg⟩

end REWB.OneUseRange.FarSelection
