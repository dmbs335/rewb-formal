import REWB.PeriodicActualJoin

/-! A closed linear-times-height bound for all additional chronological
join construction. This theorem uses the actual returned join volume,
including the empty leaves, rather than an assumed recursion schedule. -/
namespace REWB.PeriodicActual.Join
open REWB.TimedJoin
variable {α : Type}

theorem node_budget (n : Nat) : 2^(DyadicIndex.heightFor n+1)≤4*(n+1) := by
  by_cases hn : n=0
  · subst n
    simp [DyadicIndex.heightFor]
  · have h:=Nat.log2_self_le hn
    have hh:=Nat.mul_le_mul_left 4 h
    unfold DyadicIndex.heightFor
    simp only [Nat.pow_succ] at *
    omega

theorem volume_bound (d : DFA α) (K N : Nat) (w : Word α) (es fs : List TimedEntry) :
    volume (DyadicIndex.heightFor w.length) (CountedJoin.run d K N w es fs)≤
      (DyadicIndex.heightFor w.length+1)*(es.length+fs.length+5*(w.length+1)) := by
  have hc:=OfflineJoin.solve_cost d K N (DyadicIndex.heightFor w.length) w es fs
  have hn:=node_budget w.length
  have hnodes : (OfflineJoin.solve d K N (DyadicIndex.heightFor w.length) w es fs).nodes≤
      4*(w.length+1) := by omega
  have hm:=Nat.mul_le_mul_left (DyadicIndex.heightFor w.length+1) hnodes
  unfold volume
  rw [CountedJoin.run_value]
  change (OfflineJoin.solve d K N (DyadicIndex.heightFor w.length) w es fs).eventVisits+
    (OfflineJoin.solve d K N (DyadicIndex.heightFor w.length) w es fs).textVisits+
    (DyadicIndex.heightFor w.length+1)*(OfflineJoin.solve d K N (DyadicIndex.heightFor w.length) w es fs).nodes≤_
  have hw:=Nat.mul_le_mul_left (DyadicIndex.heightFor w.length+1)
    (show w.length+4*(w.length+1)≤5*(w.length+1) by omega)
  simp only [Nat.mul_add] at hc hm hw ⊢
  omega

theorem run_work_bound (d : DFA α) (K N : Nat) (w : Word α) (es fs : List TimedEntry)
    (bound : Nat) (he : bounded es bound) (hf : bounded fs bound) :
    (run d K N w es fs).2≤(coefficient d.stateCount K bound+10)*
      (DyadicIndex.heightFor w.length+1)*(es.length+fs.length+5*(w.length+1)) := by
  let V:=es.length+fs.length+5*(w.length+1)
  let H:=DyadicIndex.heightFor w.length+1
  have hh:=run_work d K N w es fs bound he hf
  have hv:=Nat.mul_le_mul_left (coefficient d.stateCount K bound) (volume_bound d K N w es fs)
  have hp : 1≤H := by dsimp only [H]; omega
  have hn : w.length+1≤V := by dsimp only [V]; omega
  have hV : 1≤V := by omega
  have hl:=Nat.mul_le_mul_right V hp
  have hr:=Nat.mul_le_mul_left H hV
  have hpos:=Nat.mul_le_mul hp hV
  change _≤_+w.length+4*H+4 at hh
  change _≤coefficient d.stateCount K bound*(H*V) at hv
  change _≤(coefficient d.stateCount K bound+10)*H*V
  simp only [Nat.mul_one,Nat.one_mul,Nat.add_mul,Nat.mul_assoc] at hl hr hpos ⊢
  omega

theorem coefficient_mono (states K L bound : Nat) (h : K≤L) :
    coefficient states K bound≤coefficient states L bound := by
  have hx:=Nat.mul_le_mul_right (bound+1) (Nat.mul_le_mul_left 41 h)
  have hy:=Nat.mul_le_mul_left (states+1) (Nat.add_le_add_right hx 7)
  unfold coefficient crossCoefficient
  omega

theorem run_work_bound_modulus (d : DFA α) (K N maxK : Nat) (w : Word α) (es fs : List TimedEntry)
    (bound : Nat) (he : bounded es bound) (hf : bounded fs bound) (hK : K≤maxK) :
    (run d K N w es fs).2≤(coefficient d.stateCount maxK bound+10)*
      (DyadicIndex.heightFor w.length+1)*(es.length+fs.length+5*(w.length+1)) := by
  apply Nat.le_trans (run_work_bound d K N w es fs bound he hf)
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
    (Nat.add_le_add_right (coefficient_mono d.stateCount K maxK bound hK) 10))

end REWB.PeriodicActual.Join
