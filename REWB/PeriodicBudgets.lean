import REWB.RunBudget

/-! Consequences of the weighted primitive-square budget for the
    periodic branches. This counts phase layouts, not their total
    processing time. The cubic-run restriction is essential: in a run
    of exponent exactly two, its square-start mass may be just one. -/
namespace REWB.RunBudget
open REWB.RunGeometry REWB.Periodic
variable {α : Type}

theorem cubic_mass (R : Bounds) (hc : 3*R.period≤R.hi-R.lo) :
    R.period≤mass R := by
  unfold mass
  omega

def phaseWork (k : Nat) : List Bounds→Nat
  | [] => 0
  | R::Rs => R.period^(k+1)+phaseWork k Rs

theorem phaseWork_le (k Q : Nat) (Rs : List Bounds)
    (h : ∀ R,R∈Rs→R.period≤Q ∧ 3*R.period≤R.hi-R.lo) :
    phaseWork k Rs≤Q^k*totalMass Rs := by
  have pow_le : ∀ a b t : Nat,a≤b→a^t≤b^t := by
    intro a b t hab
    induction t with
    | zero => simp
    | succ t ih =>
      rw [Nat.pow_succ,Nat.pow_succ]
      exact Nat.mul_le_mul ih hab
  induction Rs with
  | nil => simp [phaseWork,totalMass]
  | cons R Rs ih =>
    obtain ⟨hq,hc⟩ := h R (by simp)
    have hP : R.period^(k+1)≤Q^k*mass R := by
      rw [Nat.pow_succ]
      exact Nat.mul_le_mul (pow_le _ _ _ hq) (cubic_mass R hc)
    have hrest := ih (fun r hr=>h r (by simp [hr]))
    change R.period^(k+1)+phaseWork k Rs≤Q^k*(mass R+totalMass Rs)
    rw [Nat.mul_add]
    exact Nat.add_le_add hP hrest

theorem cubic_phase_bound (f : Nat→α) (n k Q : Nat) (Rs : List Bounds)
    (hd : Rs.Nodup) (hR : ∀ R,R∈Rs→R.Valid f n)
    (h : ∀ R,R∈Rs→R.period≤Q ∧ 3*R.period≤R.hi-R.lo) :
    phaseWork k Rs≤Q^k*(2*n*DyadicIndex.heightFor n) :=
  Nat.le_trans (phaseWork_le k Q Rs h)
    (Nat.mul_le_mul_left _ (totalMass_bound f n Rs hd hR))

/-- A non-cubic maximal equality run can only use the minimum period
    as an overlapping displacement. -/
theorem low_exponent_shift (p delta L : Nat)
    (hp : 0<p) (hd : 0<delta) (hdiv : p∣delta)
    (hoverlap : delta≤L) (hshort : L+delta<3*p) : delta=p := by
  obtain ⟨m,hm⟩ := hdiv
  have hm0 : 0<m := by
    by_cases h : m=0
    · simp [h] at hm
      omega
    · omega
  by_cases he : m=1
  · simp [he] at hm
    exact hm
  · have hge : 2≤m := by omega
    have hprod := Nat.mul_le_mul_left p hge
    rw [← hm,Nat.mul_comm p 2] at hprod
    omega

theorem low_exponent_equality (f : Nat→α) (L delta p : Nat)
    (hd : 0<delta) (hoverlap : delta≤L)
    (hcopy : ∀ i,i<L→f i=f (i+delta))
    (hmin : LeastPeriod f (L+delta) p) (hshort : L+delta<3*p) :
    delta=p :=
  low_exponent_shift p delta L hmin.1 hd
    (overlap_shift_multiple f L delta p hd hoverlap hcopy hmin) hoverlap hshort

end REWB.RunBudget
