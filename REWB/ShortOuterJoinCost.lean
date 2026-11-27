import REWB.ShortOuterJoin

/-! Closed polynomial-logarithmic budgets for the executed plain join.
No maximum-key scan appears: only the number of actual source and target
events enters the sorting term. -/
namespace REWB.ShortOuter.Join
variable {α : Type}

theorem budget_mono (k n e f E F : Nat) (he : e≤E) (hf : f≤F) :
    budget k n e f≤budget k n E F := by
  let z:=e+k*f
  let Z:=E+k*F
  have hz : z≤Z := Nat.add_le_add he (Nat.mul_le_mul_left k hf)
  have hl:=CountedJoin.log2_mono hz
  have hs:=Nat.mul_le_mul (Nat.mul_le_mul_left 10 hz) (Nat.add_le_add_right hl 1)
  have hbase : z+e+f+n+2^(DyadicIndex.heightFor n+1)≤Z+E+F+n+2^(DyadicIndex.heightFor n+1) := by omega
  have hc:=Nat.mul_le_mul_left (coefficient k) hbase
  have hh:=Nat.mul_le_mul_left (DyadicIndex.heightFor n+1) (Nat.add_le_add hs hc)
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right hh n) (DyadicIndex.heightFor n)) 3

theorem nodes_budget (n : Nat) : 2^(DyadicIndex.heightFor n+1)≤4*(n+1) := by
  have hp : 2^n.log2≤n+1 := by
    by_cases hn : n=0
    · simp [hn]
    · exact Nat.le_trans (Nat.log2_self_le hn) (by omega)
  have he : 2^(DyadicIndex.heightFor n+1)=4*2^n.log2 := by
    simp only [DyadicIndex.heightFor,Nat.pow_succ]
    omega
  rw [he]
  exact Nat.mul_le_mul_left 4 hp

def ceiling (k n e f : Nat) : Nat :=
  let z:=e+k*f
  (n.log2+2)*(10*z*(z.log2+1)+coefficient k*(z+e+f+n+4*(n+1)))+n+n.log2+4

theorem budget_le_ceiling (k n e f : Nat) : budget k n e f≤ceiling k n e f := by
  have hn:=nodes_budget n
  have hc:=Nat.mul_le_mul_left (coefficient k)
    (Nat.add_le_add_left hn (e+k*f+e+f+n))
  have hh:=Nat.mul_le_mul_left (n.log2+2)
    (Nat.add_le_add_left hc (10*(e+k*f)*((e+k*f).log2+1)))
  simp only [budget,ceiling,DyadicIndex.heightFor,Nat.add_assoc,Nat.reduceAdd] at hh ⊢
  omega

theorem run_work_max (d : DFA α) (w : Word α) (es fs : List TimedJoin.TimedEntry)
    (hs : Plain es) (ht : Plain fs) (E F : Nat) (he : es.length≤E) (hf : fs.length≤F) :
    (run d w es fs).work≤ceiling d.stateCount w.length E F :=
  Nat.le_trans (run_work d w es fs hs ht)
    (Nat.le_trans (budget_mono d.stateCount w.length es.length fs.length E F he hf)
      (budget_le_ceiling d.stateCount w.length E F))

end REWB.ShortOuter.Join
