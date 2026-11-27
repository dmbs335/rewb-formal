import REWB.MaskedAllStartRows
import REWB.MaskedAllStartCorrect

/-! The finite cache rows are produced by the actual all-start solver.
All Ready contracts below are conclusions about materialized bit arrays;
there is no supplied answer table or callback correctness premise. -/
namespace REWB.MaskedAllStart.Rows
open REWB.BoundaryRange REWB.BoundaryApplication REWB.OneUseRange
variable {σ : Nat}

theorem row_correct (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) (p : Nat) :
    FarAggregate.bit (row B C E text fallback source target).bits p=true ↔
      MaskedProgression.readMask source p=true ∧
        Spec.maskedStart B C E text.toList (MaskedProgression.readMask target) p :=
  MaskedAllStart.solve_correct B C E text fallback source target p

theorem row_size (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) : (row B C E text fallback source target).bits.size=text.size+1 :=
  MaskedAllStart.solve_size B C E text fallback source target

theorem full_target (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (p : Nat) :
    Spec.maskedStart B C E text.toList (MaskedProgression.readMask (full text.size)) p ↔
      Spec.maskedStart B C E text.toList (fun _=>true) p :=
  FarRight.masked_mask_congr B C E text.toList _ _
    (fun j hj=>full_read text.size j (by simpa only [Array.length_toList] using hj)) p

theorem row_full_correct (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) (p : Nat) :
    FarAggregate.bit (row B C E text fallback (full text.size) (full text.size)).bits p=true ↔
      Spec.maskedStart B C E text.toList (fun _=>true) p := by
  rw [row_correct,full_target]
  constructor
  · exact And.right
  · intro hp
    have hb:=MaskedReporting.maskedStart_bound B C E text.toList (fun _=>true) p hp
    exact ⟨full_read text.size p (by simpa only [Array.length_toList] using hb),hp⟩

theorem prefix_ready (B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (grid : Nat) :
    FarBank.Ready B C E w grid (prefixRows B C E w fallback grid).bits := by
  intro c i _
  rw [prefix_get]
  simpa only [List.size_toArray,List.toList_toArray] using
    row_full_correct B C (FarSelection.variant E c) (w.take grid).toArray fallback i

theorem far_ready (A B C K D : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (grid : Nat) :
    FarRight.Ready A B C K D w grid (far A B C K D w fallback grid).bits := by
  intro q k y hy
  rw [far_get,row_correct,full_read w.length y hy]
  simp only [true_and,List.toList_toArray]
  rfl

theorem forward_ready (B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (width : Nat) :
    ∀slot,FarBank.Ready B C E w (Grid.position w.length width slot.val)
      ((forward B C E w fallback width).bits.get slot) := by
  intro slot
  rw [forward_get]
  exact prefix_ready B C E w fallback _

theorem backward_ready (A B C : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (width : Nat) :
    ∀slot,FarBank.Ready (Automata.reverse B) (Automata.reverse C) (Automata.reverse A)
      w.reverse (Grid.backward w.length width slot.val)
      ((backward A B C w fallback width).bits.get slot) := by
  intro slot
  rw [backward_get]
  exact prefix_ready _ _ _ _ fallback _

theorem oneUse_ready (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (width : Nat) :
    OneUseRange.Cache.Ready A B C E w width
      (forward B C E w fallback width).bits (backward A B C w fallback width).bits :=
  ⟨forward_ready B C E w fallback width,backward_ready A B C w fallback width⟩

theorem boundary_ready (A B C K D : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (width : Nat) :
    BoundaryRange.Cache.Ready A B C K D w width (boundary A B C K D w fallback width).bits := by
  intro slot
  rw [boundary_get]
  exact far_ready A B C K D w fallback _

end REWB.MaskedAllStart.Rows
