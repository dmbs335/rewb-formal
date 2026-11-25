import REWB.MaskedEmptyCorrect

namespace REWB.MaskedEmpty
open MarkedDP (MarkedWord)
variable {α : Type}

theorem compute_work (C E : DFA α) (mark : Bool) (xs : MarkedWord α) :
    (compute C E mark xs).work = rowBudget C E*(xs.length+1) := by
  induction xs with
  | nil => simp only [compute,terminal,List.length_nil,Nat.zero_add,Nat.mul_one]
  | cons x xs ih =>
    change (compute C E mark xs).work+rowBudget C E =
      rowBudget C E*(xs.length+1+1)
    rw [ih]
    simp only [Nat.mul_add,Nat.mul_one]

theorem solve_work (B C E : DFA α) (w : Word α) (source target : Array Bool) :
    (solve B C E w source target).work =
      (12*C.stateCount+6*E.stateCount+64)*(w.length+1) := by
  simp only [solve,compute_work,markWord_length,rowBudget,Nat.add_mul,Nat.mul_add]
  omega

end REWB.MaskedEmpty
