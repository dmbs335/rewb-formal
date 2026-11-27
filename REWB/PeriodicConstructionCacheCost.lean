import REWB.PeriodicConstructionCacheContexts

/-! Closed bounds for the actual materialized cache builders. The period
parameter occurs only quadratically in DFA tables and cubically in the
equality table. Exterior contexts are built once in linear word length.
The full local construction counter is bounded by a fixed-pattern
multiple of the legacy counter, with the zero-period overhead explicit. -/
namespace REWB.PeriodicConstruction.Cache
variable {α : Type}

theorem contextsCost_bound (m n : Nat) :
    contextsCost m n≤64*(m+1)*(n+1) := by
  simp only [contextsCost,prefixCost,suffixCost,vectorCost,
    Nat.mul_add,Nat.add_mul,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] <;> (simp only [←Nat.mul_assoc] <;> omega)

theorem transitionsCost_bound (m q : Nat) :
    transitionsCost m q≤64*(m+1)*(q+1)^2 := by
  simp only [transitionsCost,phaseCost,rowCost,prefixCost,Nat.pow_succ,Nat.pow_zero,
    Nat.mul_one,Nat.one_mul,Nat.mul_add,Nat.add_mul,
    Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] <;> (simp only [←Nat.mul_assoc] <;> omega)

theorem equalityCost_bound (q : Nat) :
    equalityCost q≤64*(q+1)^3 := by
  simp only [equalityCost,equalRowCost,equalPairCost,Nat.pow_succ,Nat.pow_zero,
    Nat.mul_one,Nat.one_mul,Nat.mul_add,Nat.add_mul,
    Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] <;> (simp only [←Nat.mul_assoc] <;> omega)

theorem prepareAtCost_bound (P : SevenDFA α) (q : Nat) :
    prepareAtCost P q≤128*(FullyCachedP2.stateSum P+1)*(q+1)^3 := by
  simp only [prepareAtCost,FullyCachedP2.stateSum,transitionsCost,phaseCost,rowCost,
    prefixCost,equalityCost,equalRowCost,equalPairCost,Nat.pow_succ,Nat.pow_zero,
    Nat.mul_one,Nat.one_mul,Nat.mul_add,Nat.add_mul,
    Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] <;> (simp only [←Nat.mul_assoc] <;> omega)

theorem cube_next (q : Nat) : (q+1)^3≤8*(q^3+1) := by
  cases q with
  | zero=>decide
  | succ q=>
    simp only [Nat.succ_eq_add_one,Nat.pow_succ,Nat.pow_zero,Nat.mul_one,Nat.one_mul,
      Nat.mul_add,Nat.add_mul,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] <;> (simp only [←Nat.mul_assoc] <;> omega)

theorem contexts_work_le_old (P : SevenDFA α) (w : Word α) :
    (contexts P w).2≤64*(BoundaryContexts.build P w).2 := by
  rw [contexts_work,BoundaryContexts.build_cost]
  simpa only [Nat.add_comm,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using
    contextsCost_bound P.H.stateCount w.length

def prepareCoefficient (P : SevenDFA α) : Nat :=
  1024*(FullyCachedP2.stateSum P+1)

theorem prepareAt_work_le_old [DecidableEq α] (P : SevenDFA α) (s : Nat→α) (q : Nat)
    (I : BoundaryContexts.Index P) (lo hi : Nat) :
    (prepareAt P s q I lo hi).2≤
      prepareCoefficient P*((BoundaryContexts.countedPrepareAt P s q I lo hi).2+1) := by
  have hq : q^3+1≤(BoundaryContexts.countedPrepareAt P s q I lo hi).2+1 := by
    rw [BoundaryContexts.countedPrepareAt_cost]
    omega
  rw [prepareAt_work]
  calc
    prepareAtCost P q≤128*(FullyCachedP2.stateSum P+1)*(q+1)^3 :=
      prepareAtCost_bound P q
    _≤128*(FullyCachedP2.stateSum P+1)*(8*(q^3+1)) :=
      Nat.mul_le_mul_left _ (cube_next q)
    _=(128*8)*(FullyCachedP2.stateSum P+1)*(q^3+1) := by ac_rfl
    _=prepareCoefficient P*(q^3+1) := rfl
    _≤prepareCoefficient P*((BoundaryContexts.countedPrepareAt P s q I lo hi).2+1) :=
      Nat.mul_le_mul_left _ hq

theorem prepareAt_work_le_old_pos [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (q : Nat) (I : BoundaryContexts.Index P) (lo hi : Nat) (hq : 0<q) :
    (prepareAt P s q I lo hi).2≤
      (2*prepareCoefficient P)*(BoundaryContexts.countedPrepareAt P s q I lo hi).2 := by
  have hq1 : 1≤q := hq
  have hp : 1≤q^3 := by
    have h:=Nat.mul_le_mul (Nat.mul_le_mul hq1 hq1) hq1
    simpa only [Nat.one_mul,Nat.mul_one,Nat.pow_succ,Nat.pow_zero] using h
  have oldpos : 1≤(BoundaryContexts.countedPrepareAt P s q I lo hi).2 := by
    rw [BoundaryContexts.countedPrepareAt_cost]
    omega
  have h:=prepareAt_work_le_old P s q I lo hi
  have step : (BoundaryContexts.countedPrepareAt P s q I lo hi).2+1≤
      2*(BoundaryContexts.countedPrepareAt P s q I lo hi).2 := by omega
  calc
    (prepareAt P s q I lo hi).2≤
        prepareCoefficient P*((BoundaryContexts.countedPrepareAt P s q I lo hi).2+1) := h
    _≤prepareCoefficient P*(2*(BoundaryContexts.countedPrepareAt P s q I lo hi).2) :=
      Nat.mul_le_mul_left _ step
    _=(2*prepareCoefficient P)*(BoundaryContexts.countedPrepareAt P s q I lo hi).2 := by ac_rfl

end REWB.PeriodicConstruction.Cache
