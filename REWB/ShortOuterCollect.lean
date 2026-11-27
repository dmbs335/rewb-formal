import REWB.ShortOuterReadySound

/-! Counted finite event loops.  The range and concatenation work is
included in the returned scalar; semantic membership never evaluates a
second copy of the event builder. -/
namespace REWB.ShortOuter.Collect
variable {α β : Type}

theorem map_work (f : α→β×Nat) (xs : List α) (c : Nat)
    (hc : ∀x,x∈xs→(f x).2≤c) :
    (CountedProjection.map f xs).2≤xs.length*(c+1)+1 := by
  induction xs with
  | nil => simp [CountedProjection.map]
  | cons x xs ih =>
    have ha:=hc x (by simp)
    have hb:=ih (by intro y hy; exact hc y (by simp [hy]))
    simp only [CountedProjection.map,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem flatMap_length (f : α→List β×Nat) (xs : List α) (m : Nat)
    (hm : ∀x,x∈xs→(f x).1.length≤m) :
    (CountedProjection.flatMap f xs).1.length≤xs.length*m := by
  induction xs with
  | nil => simp [CountedProjection.flatMap]
  | cons x xs ih =>
    simp only [CountedProjection.flatMap,CountedProjection.append_value,List.length_append,List.length_cons]
    have ha:=hm x (by simp)
    have hb:=ih (by intro y hy; exact hm y (by simp [hy]))
    rw [Nat.add_mul,Nat.one_mul]
    omega

theorem flatMap_work (f : α→List β×Nat) (xs : List α) (c m : Nat)
    (hc : ∀x,x∈xs→(f x).2≤c) (hm : ∀x,x∈xs→(f x).1.length≤m) :
    (CountedProjection.flatMap f xs).2≤xs.length*(c+m+2)+1 := by
  induction xs with
  | nil => simp [CountedProjection.flatMap]
  | cons x xs ih =>
    simp only [CountedProjection.flatMap,CountedProjection.append_steps,List.length_cons]
    have ha:=hc x (by simp)
    have hl:=hm x (by simp)
    have hb:=ih (by intro y hy; exact hc y (by simp [hy]))
      (by intro y hy; exact hm y (by simp [hy]))
    rw [Nat.add_mul,Nat.one_mul]
    omega

def run (n : Nat) (f : Nat→List α×Nat) : List α×Nat :=
  let ns:=CountedProjection.range n
  let out:=CountedProjection.flatMap f ns.1
  (out.1,ns.2+out.2+2)

theorem mem (n : Nat) (f : Nat→List α×Nat) (x : α) :
    x∈(run n f).1 ↔ ∃i,i<n ∧ x∈(f i).1 := by
  simp only [run,CountedProjection.flatMap_value,CountedProjection.range_value,List.mem_flatMap,List.mem_range]

theorem length (n : Nat) (f : Nat→List α×Nat) (m : Nat)
    (hm : ∀i,i<n→(f i).1.length≤m) : (run n f).1.length≤n*m := by
  have h:=flatMap_length f (CountedProjection.range n).1 m
    (by simpa only [CountedProjection.range_value,List.mem_range] using hm)
  simpa only [run,CountedProjection.range_value,List.length_range] using h

theorem work (n : Nat) (f : Nat→List α×Nat) (c m : Nat)
    (hc : ∀i,i<n→(f i).2≤c) (hm : ∀i,i<n→(f i).1.length≤m) :
    (run n f).2≤n*(c+m+4)+4 := by
  have h:=flatMap_work f (CountedProjection.range n).1 c m
    (by simpa only [CountedProjection.range_value,List.mem_range] using hc)
    (by simpa only [CountedProjection.range_value,List.mem_range] using hm)
  have hn : (CountedProjection.range n).1.length=n := by
    rw [CountedProjection.range_value,List.length_range]
  rw [hn] at h
  change (CountedProjection.range n).2+(CountedProjection.flatMap f _).2+2≤_
  have hr : (CountedProjection.range n).2=2*n+1 := CountedProjection.rangeFrom_steps 0 n
  rw [hr]
  simp only [Nat.mul_add,Nat.mul_one] at h ⊢
  omega

def emit (condition : Bool) (value : α) (cost : Nat) : List α×Nat :=
  (if condition then [value] else [],cost+1)

theorem emit_mem (condition : Bool) (value x : α) (cost : Nat) :
    x∈(emit condition value cost).1 ↔ condition=true ∧ value=x := by
  cases condition <;> simp [emit,eq_comm]

theorem emit_length (condition : Bool) (value : α) (cost : Nat) :
    (emit condition value cost).1.length≤1 := by cases condition <;> simp [emit]

theorem emit_work (condition : Bool) (value : α) (cost : Nat) :
    (emit condition value cost).2=cost+1 := rfl

end REWB.ShortOuter.Collect
