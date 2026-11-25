import REWB.OneUseRangeCache

/-! Exact range-query assembly from the actual finite caches. `Ready`
is intentionally retained: proving that a concrete fast all-start
execution constructs those input bit rows is a separate obligation. -/
namespace REWB.OneUseRange.Cache
open REWB.BoundaryRange
variable {σ : Nat}

theorem queryValid_correct (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) (hw : 0<width) (forward : Inputs E w.length width)
    (backward : Inputs (Automata.reverse A) w.length width)
    (ready : Ready A B C E w width forward backward) (left right : Nat)
    (hlr : left≤right) (hr : right≤w.length) :
    (queryValid (build A B C E w fallback width hw forward backward) left right hlr hr).1=true ↔
      Spec.oneUseRange A B C E w left right := by
  let chosen:=Grid.choose w.length width hw left right hlr hr
  have hg:=Grid.choose_bounds w.length width hw left right hlr hr
  change left≤chosen.leftGrid ∧ chosen.leftGrid≤w.length ∧ chosen.rightGrid≤right ∧ _ at hg
  have hf:=FarBank.query_correct A B C E w (Grid.position w.length width chosen.rightSlot.val)
    (forward.get chosen.rightSlot) (ready.1 chosen.rightSlot) left right hg.2.2.1 hr
  have hb:=FarBank.query_correct (Automata.reverse E) (Automata.reverse B) (Automata.reverse C)
    (Automata.reverse A) w.reverse (Grid.backward w.length width chosen.leftSlot.val)
    (backward.get chosen.leftSlot) (ready.2 chosen.leftSlot) (w.length-right) (w.length-left)
    (by change w.length-chosen.leftGrid≤w.length-left; omega)
    (by rw [List.length_reverse]; omega)
  have hb' :
      (FarBank.query
        (FarBank.build (Automata.reverse E) (Automata.reverse A) w.reverse
          (Grid.backward w.length width chosen.leftSlot.val) (backward.get chosen.leftSlot))
        (FarSelection.build (Automata.reverse A) w.reverse) (w.length-right) (w.length-left)).1=true ↔
      Border.FarSource A B C E w left right chosen.leftGrid :=
    hb.trans (Reverse.farSource_reverse A B C E w left right chosen.leftGrid (by omega) hr hg.2.1).symm
  unfold queryValid
  simp only [build_forward,build_backward_query]
  change (((FarBank.query
      (FarBank.build A E w (Grid.position w.length width chosen.rightSlot.val) (forward.get chosen.rightSlot))
      (FarSelection.build E w) left right).1 ||
    (FarBank.query
      (FarBank.build (Automata.reverse E) (Automata.reverse A) w.reverse
        (Grid.backward w.length width chosen.leftSlot.val) (backward.get chosen.leftSlot))
      (FarSelection.build (Automata.reverse A) w.reverse) (w.length-right) (w.length-left)).1) ||
    (Border.query (Border.build A B C E w fallback) left right chosen.leftGrid chosen.rightGrid).1)=true ↔ _
  rw [Bool.or_eq_true,Bool.or_eq_true,hf,hb',Border.partition A B C E w fallback left right chosen.leftGrid chosen.rightGrid]
  simp only [hlr,hr,true_and,or_assoc]
  rfl

theorem query_correct (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) (hw : 0<width) (forward : Inputs E w.length width)
    (backward : Inputs (Automata.reverse A) w.length width)
    (ready : Ready A B C E w width forward backward) (left right : Nat) :
    (query (build A B C E w fallback width hw forward backward) left right).1=true ↔
      Spec.oneUseRange A B C E w left right := by
  unfold query
  change ((if h : left≤right ∧ right≤w.length then _ else _) : Bool×Nat).1=true ↔ _
  by_cases h : left≤right ∧ right≤w.length
  · rw [dif_pos h]
    exact queryValid_correct A B C E w fallback width hw forward backward ready left right h.1 h.2
  · rw [dif_neg h]
    simp only [Bool.false_eq_true,false_iff]
    intro hh
    exact h ⟨hh.1,hh.2.1⟩

end REWB.OneUseRange.Cache
