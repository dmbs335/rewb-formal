import REWB.BoundaryRangeCache

/-! All six regions assemble into the original boundaryRange predicate.
The output-row provenance of the pending, explicitly materialized
far-right all-start instances remains the sole input assumption. -/
namespace REWB.BoundaryRange.Cache
variable {σ : Nat}

theorem prepare_request_mask (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) (hw : 0<width) (slot : Fin (CacheGrid.count w.length width))
    (q k : Fin K.stateCount) (y : Nat) (hy : y≤w.length) :
    FarRight.readMask (Table.get (prepare A B C K D E w fallback width hw).blocks slot).requests q k y=
      farMask K w (CacheGrid.upper w.length width slot.val) q k (w.length-y) := by
  rw [prepare_block]
  exact FarRight.readMask_correct K w (CacheGrid.upper w.length width slot.val) q k y hy

theorem queryValid_correct (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) (hw : 0<width) (bits : Inputs K w.length width)
    (ready : Ready A B C K D w width bits) (left right : Nat)
    (hlr : left≤right) (hr : right≤w.length) :
    (queryValid (build A B C K D E w fallback width hw bits) left right (by change left≤w.length; omega)).1=true ↔
      Spec.boundaryRange A B C K D E w left right := by
  let slot : Fin (CacheGrid.count w.length width):=⟨left/width,CacheGrid.slot_bound w.length width left hw (by omega)⟩
  let g0:=CacheGrid.lower w.length width slot.val
  let g:=CacheGrid.upper w.length width slot.val
  have hgg:=CacheGrid.bounds w.length width slot.val
  change g0≤g ∧ g≤w.length at hgg
  have hl:=CacheGrid.selected_bounds w.length width left hw (by omega)
  change g0≤left ∧ left≤g ∧ _ at hl
  have hf:=FarLeft.query_correct A B C K D E w fallback g hgg.2 left right g0 hl.2.1 hr
  have ht:=FarRight.query_correct A B C K D E w g (bits.get slot) (ready slot) left right g0 hl.2.1 hgg.2 hr
  have hn:=NearIndex.queryThree_correct A B C K D E w fallback g0 g hgg.1 hgg.2 left right hl.1 hl.2.1 hr
  have hb:=NearIndex.Border.query_correct A B C K D E w fallback left right g0 g hgg.2 hr
  unfold queryValid
  change (((FarLeft.query K E (Table.get (prepare A B C K D E w fallback width hw).blocks slot).far left right).1 ||
      (FarRight.query K (Table.get (build A B C K D E w fallback width hw bits).right slot) left right).1) ||
      (NearIndex.queryThree (Table.get (prepare A B C K D E w fallback width hw).blocks slot).near left right).1 ||
      (NearIndex.Border.query (NearIndex.Border.build A B C K D E w fallback) left right
        (Table.get (prepare A B C K D E w fallback width hw).blocks slot).lower
        (Table.get (prepare A B C K D E w fallback width hw).blocks slot).upper).1)=true ↔ _
  rw [prepare_block,build_right]
  change (((FarLeft.query K E (FarLeft.build A B C K D E w fallback g hgg.2) left right).1 ||
      (FarRight.query K (FarRight.build K E w g (bits.get slot)) left right).1) ||
      (NearIndex.queryThree (NearIndex.build A B C K D E w fallback g0 g hgg.1 hgg.2) left right).1 ||
      (NearIndex.Border.query (NearIndex.Border.build A B C K D E w fallback) left right g0 g).1)=true ↔ _
  simp only [Bool.or_eq_true,hf,ht,hn,hb]
  rw [six_cases A B C K D E w left right g0 g]
  simp only [hlr,hr,true_and,or_assoc]

theorem query_correct (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) (hw : 0<width) (bits : Inputs K w.length width)
    (ready : Ready A B C K D w width bits) (left right : Nat) :
    (query (build A B C K D E w fallback width hw bits) left right).1=true ↔
      Spec.boundaryRange A B C K D E w left right := by
  unfold query
  change ((if h : left≤right ∧ right≤w.length then _ else _) : Bool×Nat).1=true ↔ _
  by_cases h : left≤right ∧ right≤w.length
  · rw [dif_pos h]
    exact queryValid_correct A B C K D E w fallback width hw bits ready left right h.1 h.2
  · rw [dif_neg h]
    simp only [Bool.false_eq_true,false_iff]
    intro hh
    exact h ⟨hh.1,hh.2.1⟩

end REWB.BoundaryRange.Cache
