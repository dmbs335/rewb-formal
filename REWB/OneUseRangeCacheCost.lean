import REWB.OneUseRangeCacheCorrect

/-! Costs of constructing and querying the eager cache from finite bit
rows. The rows' own all-start construction cost is deliberately absent
and must be supplied by the concrete execution that establishes Ready. -/
namespace REWB.OneUseRange.Cache
open REWB.BoundaryRange
variable {σ : Nat}

private theorem bank_mono (A E : DFA (Fin σ)) (g n : Nat) (h : g≤n) :
    FarBank.buildBudget A E g≤FarBank.buildBudget A E n := by
  have hs:=Nat.mul_le_mul_left (6*A.stateCount+7) (Nat.add_le_add_right h 1)
  have hc:=Nat.mul_le_mul_left (TableColor.count E) (Nat.add_le_add_right hs 4)
  unfold FarBank.buildBudget
  omega

theorem forward_work (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) (hw : 0<width) (forward : Inputs E w.length width)
    (backward : Inputs (Automata.reverse A) w.length width) :
    (build A B C E w fallback width hw forward backward).forward.work≤
      Grid.count w.length width*(FarBank.buildBudget A E w.length+7)+1 := by
  have hh:=Table.build_work_le (fun slot : Fin (Grid.count w.length width)=>
      let bank:=FarBank.build A E w (Grid.position w.length width slot.val) (forward.get slot)
      (bank,bank.work+4)) (FarBank.buildBudget A E w.length+4) (by
        intro slot
        have hc:=FarBank.build_work A E w (Grid.position w.length width slot.val) (forward.get slot)
        have hm:=bank_mono A E _ w.length (Grid.position_bound w.length width slot.val)
        dsimp only
        omega)
  simpa only [Nat.add_assoc,Nat.reduceAdd] using hh

theorem backward_work (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) (hw : 0<width) (forward : Inputs E w.length width)
    (backward : Inputs (Automata.reverse A) w.length width) :
    (build A B C E w fallback width hw forward backward).backward.banks.work≤
      Grid.count w.length width*(FarBank.buildBudget (Automata.reverse E) (Automata.reverse A) w.length+8)+1 := by
  have hh:=Table.build_work_le (fun slot : Fin (Grid.count w.length width)=>
      let bank:=FarBank.build (Automata.reverse E) (Automata.reverse A) w.reverse
        (Grid.backward w.length width slot.val) (backward.get slot)
      (bank,bank.work+5)) (FarBank.buildBudget (Automata.reverse E) (Automata.reverse A) w.length+5) (by
        intro slot
        have hc:=FarBank.build_work (Automata.reverse E) (Automata.reverse A) w.reverse
          (Grid.backward w.length width slot.val) (backward.get slot)
        have hm:=bank_mono (Automata.reverse E) (Automata.reverse A)
          (Grid.backward w.length width slot.val) w.length
          (Nat.sub_le w.length (Grid.position w.length width slot.val))
        dsimp only
        omega)
  simpa only [Nat.add_assoc,Nat.reduceAdd] using hh

def buildBudget (A B C E : DFA (Fin σ)) (n width : Nat) : Nat :=
  FarSelection.buildBudget E n+
    (Grid.count n width*(FarBank.buildBudget A E n+7)+1)+
    FarSelection.buildBudget (Automata.reverse A) n+
    (Grid.count n width*(FarBank.buildBudget (Automata.reverse E) (Automata.reverse A) n+8)+1)+
    Border.buildBound A B C E n+2*n+20

theorem build_work (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) (hw : 0<width) (forward : Inputs E w.length width)
    (backward : Inputs (Automata.reverse A) w.length width) :
    (build A B C E w fallback width hw forward backward).work≤buildBudget A B C E w.length width := by
  have hf:=forward_work A B C E w fallback width hw forward backward
  have hb:=backward_work A B C E w fallback width hw forward backward
  have hn:=Border.build_work A B C E w fallback
  change (FarSelection.build E w).work+(build A B C E w fallback width hw forward backward).forward.work+
    (FarSelection.build (Automata.reverse A) w.reverse).work+
    (build A B C E w fallback width hw forward backward).backward.banks.work+
    (Border.build A B C E w fallback).work+2*w.length+20≤_
  rw [FarSelection.build_work,FarSelection.build_work,List.length_reverse]
  unfold buildBudget
  omega

def queryBudget (A B C E : DFA (Fin σ)) (n width : Nat) : Nat :=
  FarBank.queryBudget E n+FarBank.queryBudget (Automata.reverse A) n+
    (width*(width*(Border.fixedBudget A B C E*((n+1).log2+1)^2)+4)+1)+23

theorem queryValid_work (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) (hw : 0<width) (forward : Inputs E w.length width)
    (backward : Inputs (Automata.reverse A) w.length width) (left right : Nat)
    (hlr : left≤right) (hr : right≤w.length) :
    (queryValid (build A B C E w fallback width hw forward backward) left right hlr hr).2≤
      queryBudget A B C E w.length width := by
  let chosen:=Grid.choose w.length width hw left right hlr hr
  have hg:=Grid.choose_bounds w.length width hw left right hlr hr
  change left≤chosen.leftGrid ∧ chosen.leftGrid≤w.length ∧ chosen.rightGrid≤right ∧
    chosen.leftGrid-left<width ∧ right-chosen.rightGrid<width at hg
  have hf:=FarBank.query_work A E w (Grid.position w.length width chosen.rightSlot.val)
    (forward.get chosen.rightSlot) left right
  have hb:=FarBank.query_work (Automata.reverse E) (Automata.reverse A) w.reverse
    (Grid.backward w.length width chosen.leftSlot.val) (backward.get chosen.leftSlot)
    (w.length-right) (w.length-left)
  rw [List.length_reverse] at hb
  have hn:=Border.query_work_height A B C E w fallback left right chosen.leftGrid chosen.rightGrid
  have hi:=Nat.mul_le_mul_right (Border.fixedBudget A B C E*((w.length+1).log2+1)^2)
    (Nat.le_of_lt hg.2.2.2.2)
  have ho:=Nat.mul_le_mul (Nat.le_of_lt hg.2.2.2.1) (Nat.add_le_add_right hi 4)
  unfold queryValid
  simp only [build_forward,build_backward_query]
  change (FarBank.query
      (FarBank.build A E w (Grid.position w.length width chosen.rightSlot.val) (forward.get chosen.rightSlot))
      (FarSelection.build E w) left right).2+
    (FarBank.query
      (FarBank.build (Automata.reverse E) (Automata.reverse A) w.reverse
        (Grid.backward w.length width chosen.leftSlot.val) (backward.get chosen.leftSlot))
      (FarSelection.build (Automata.reverse A) w.reverse) (w.length-right) (w.length-left)).2+
    (Border.query (Border.build A B C E w fallback) left right chosen.leftGrid chosen.rightGrid).2+14+9≤_
  unfold queryBudget
  omega

theorem query_work (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) (hw : 0<width) (forward : Inputs E w.length width)
    (backward : Inputs (Automata.reverse A) w.length width) (left right : Nat) :
    (query (build A B C E w fallback width hw forward backward) left right).2≤
      queryBudget A B C E w.length width := by
  unfold query
  change ((if h : left≤right ∧ right≤w.length then _ else _) : Bool×Nat).2≤_
  split
  · rename_i h
    exact queryValid_work A B C E w fallback width hw forward backward left right h.1 h.2
  · dsimp only
    unfold queryBudget
    omega

end REWB.OneUseRange.Cache
