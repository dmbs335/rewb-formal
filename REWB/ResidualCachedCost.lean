import REWB.ResidualCachedRounded

/-! The concrete residual, short-outer and finite-cache budgets obey the
25/13 target. The final bound also includes the existing periodic
ledgers. It is deliberately a theorem about the counters actually
accounted for: all-start row production and the documented unmeasured
periodic formula/window assembly remain separate runtime obligations. -/
namespace REWB.ResidualCached.Cost
open Growth
variable {σ : Nat}

set_option maxHeartbeats 1000000

theorem grid_bound {n t x C : Nat} (ht : 1≤t) (hn : n+2≤t^39)
    (hx : Bound n (t^3) x 1 0 1 2 C) : x≤(3*C)*t^75*(height n)^2 := by
  have hh:=Nat.mul_le_mul_right ((height n)^2) (Nat.mul_le_mul_left C (Rounded.grid n t ht hn))
  simp only [Bound,scale,Nat.pow_zero,Nat.pow_one,Nat.mul_one] at hx
  have he : C*((n+2)*(n/t^3+2))*(height n)^2=C*((n+2)*(n/t^3+2)*(height n)^2) := by ac_rfl
  rw [he] at hh
  exact Nat.le_trans hx (by simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hh)

theorem short_bound {n t x C : Nat} (ht : 1≤t) (hn : n+2≤t^39)
    (hx : Bound n (t^13) x 1 2 0 2 C) : x≤(4*C)*t^75*(height n)^2 := by
  have hh:=Nat.mul_le_mul_right ((height n)^2) (Nat.mul_le_mul_left C (Rounded.short n t ht hn))
  simp only [Bound,scale,Nat.pow_zero,Nat.pow_one,Nat.mul_one] at hx
  have he : C*((n+2)*(t^13+1)^2)*(height n)^2=C*((n+2)*(t^13+1)^2*(height n)^2) := by ac_rfl
  rw [he] at hh
  exact Nat.le_trans hx (by simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hh)

theorem query_bound {n t x C : Nat} (ht : 1≤t) (hn : n+2≤t^39)
    (hx : Bound n (t^3) x 0 2 0 2 C) :
    ResidualDispatch.selectorBudget n (t^13) (t^13) (t^9)*x≤(60*C)*t^75*(height n)^3 := by
  simp only [Bound,scale,Nat.pow_zero,Nat.one_mul,Nat.mul_one] at hx
  have h₁:=Nat.mul_le_mul_left (ResidualDispatch.selectorBudget n (t^13) (t^13) (t^9)) hx
  have h₂:=Nat.mul_le_mul_right ((height n)^2) (Nat.mul_le_mul_left C (Rounded.window_queries n t ht hn))
  have he : ResidualDispatch.selectorBudget n (t^13) (t^13) (t^9)*(C*((t^3+1)^2*(height n)^2))=
      C*(ResidualDispatch.selectorBudget n (t^13) (t^13) (t^9)*(t^3+1)^2)*(height n)^2 := by ac_rfl
  rw [he] at h₁
  have hh:=Nat.le_trans h₁ h₂
  have he' : C*(60*t^75*height n)*(height n)^2=(60*C)*t^75*(height n)^3 := by
    rw [show (height n)^3=height n*(height n)^2 by rw [Nat.pow_succ,Nat.mul_comm]]
    ac_rfl
  rwa [he'] at hh

theorem raise_height {n t x C a b : Nat} (hx : x≤C*t^75*(height n)^a) (hab : a≤b) :
    x≤C*t^75*(height n)^b :=
  Nat.le_trans hx (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by unfold height; omega) hab))

theorem preparation (σ : Nat) : ∃C,∀n t,1≤t→n+2≤t^39→
    ResidualDispatch.preparationBudget σ n (t^3) (t^13) (t^13) (t^9)≤C*t^75*(height n)^2 := by
  obtain ⟨Cg,hg⟩:=Growth.strip_generation σ
  obtain ⟨Cr,hr⟩:=Growth.run_preparation σ
  refine ⟨3*Cg+3*Cr+622,?_⟩
  intro n t ht hn
  have hg':=grid_bound ht hn (hg n (t^3))
  have hr':=grid_bound ht hn (hr n (t^3))
  have hs:=raise_height (show _≤68*t^75*(height n)^1 by simpa only [Nat.pow_one] using Rounded.strip_extra n t ht hn)
    (by decide : 1≤2)
  have hc:=raise_height (show _≤549*t^75*(height n)^1 by simpa only [Nat.pow_one] using Rounded.selector_work n t ht hn)
    (by decide : 1≤2)
  have hpos : 1≤t^75*(height n)^2 := Nat.mul_le_mul
    (show 1≤t^75 from Nat.pow_pos (by omega)) (show 1≤(height n)^2 from Nat.pow_pos (by unfold height; omega))
  unfold ResidualDispatch.preparationBudget ResidualStripSchedule.scheduleBudget
  simp only [Nat.add_mul,Nat.mul_assoc] at hg' hr' hs hc ⊢
  omega

theorem overhead (n t : Nat) (ht : 1≤t) (hn : n+2≤t^39) : n+11≤12*t^75*(height n)^3 := by
  have hp:=Nat.le_trans hn (Rounded.power_le t 39 75 ht (by decide))
  have hH : 1≤(height n)^3 := Nat.pow_pos (by unfold height; omega)
  have hm:=Nat.mul_le_mul_left (t^75) hH
  simp only [Nat.mul_one] at hm
  simp only [Nat.mul_assoc]
  omega

def residual (σ : Nat) (short bank query : Nat→Nat→Nat) (n s L D Q : Nat) : Nat :=
  short n L+ResidualDispatch.preparationBudget σ n s L D Q+
    bank n s+ResidualDispatch.selectorBudget n L D Q*(query n s+3)+n+11

theorem residual_bound (σ : Nat) (short bank query : Nat→Nat→Nat)
    (hshort : ∃C,∀n L,Bound n L (short n L) 1 2 0 2 C)
    (hbank : ∃C,∀n s,Bound n s (bank n s) 1 0 1 2 C)
    (hquery : ∃C,∀n s,Bound n s (query n s+3) 0 2 0 2 C) :
    ∃C,0<C ∧ ∀n t,1≤t→n+2≤t^39→residual σ short bank query n (t^3) (t^13) (t^13) (t^9)≤C*t^75*(height n)^3 := by
  obtain ⟨Cs,hs⟩:=hshort
  obtain ⟨Cb,hb⟩:=hbank
  obtain ⟨Cq,hq⟩:=hquery
  obtain ⟨Cp,hp⟩:=preparation σ
  refine ⟨4*Cs+3*Cb+60*Cq+Cp+12,by omega,?_⟩
  intro n t ht hn
  have hs':=raise_height (short_bound ht hn (hs n (t^13))) (by decide : 2≤3)
  have hb':=raise_height (grid_bound ht hn (hb n (t^3))) (by decide : 2≤3)
  have hq':=query_bound ht hn (hq n (t^3))
  have hp':=raise_height (hp n t ht hn) (by decide : 2≤3)
  have ho:=overhead n t ht hn
  unfold residual
  simp only [Nat.add_mul,Nat.mul_assoc] at hs' hb' hq' hp' ho ⊢
  omega

theorem p1_residual (P : SevenDFA (Fin σ)) : ∃C,0<C ∧ ∀n t,1≤t→n+2≤t^39→
    P1.residualBudget P n (t^3) (t^13) (t^13) (t^9)≤C*t^75*(height n)^3 :=
  residual_bound σ (ShortOuter.P1.budget P) (P1.buildBudget P) (P1.queryBudget P)
    (Growth.p1_short P) (Growth.p1_build P) (Growth.p1_query P)

theorem p2_residual (P : SevenDFA (Fin σ)) : ∃C,0<C ∧ ∀n t,1≤t→n+2≤t^39→
    P2.residualBudget P n (t^3) (t^13) (t^13) (t^9)≤C*t^75*(height n)^3 :=
  residual_bound σ (ShortOuter.P2.budget P) (P2.buildBudget P) (P2.queryBudget P)
    (Growth.p2_short P) (Growth.p2_build P) (Growth.p2_query P)

def budget (P : SevenDFA (Fin σ)) (n : Nat) : Nat :=
  P1.residualBudget P n (ThresholdBudget.block n) (ThresholdBudget.length n) (ThresholdBudget.length n) (ThresholdBudget.period n)+
    P2.residualBudget P n (ThresholdBudget.block n) (ThresholdBudget.length n) (ThresholdBudget.length n) (ThresholdBudget.period n)+
    (PeriodicAccounting.longExpr P).eval n (ThresholdBudget.period n)+
    (PeriodicAccounting.shortExpr P).eval n (ThresholdBudget.period n)+
    (PeriodicAccounting.p2Expr P).eval n (ThresholdBudget.period n)*height n

theorem budget_bound (P : SevenDFA (Fin σ)) : ∃C,0<C ∧ ∀n,
    budget P n≤C*(ThresholdBudget.base n)^75*(height n)^3 := by
  obtain ⟨C₁,hC₁,h₁⟩:=p1_residual P
  obtain ⟨C₂,hC₂,h₂⟩:=p2_residual P
  refine ⟨C₁+C₂+(PeriodicAccounting.longExpr P).coeff+(PeriodicAccounting.shortExpr P).coeff+
    (PeriodicAccounting.p2Expr P).coeff,by omega,?_⟩
  intro n
  have ht : 1≤ThresholdBudget.base n := ThresholdBudget.base_pos n
  have hn:=ThresholdBudget.rounded_lower n
  have hp1:=h₁ n _ ht hn
  have hp2:=h₂ n _ ht hn
  have hl:=PeriodicAccounting.Expr.bound75 (PeriodicAccounting.longExpr P) (by rw [PeriodicAccounting.long_degree]; decide) n
  have hs:=PeriodicAccounting.Expr.bound75 (PeriodicAccounting.shortExpr P) (by rw [PeriodicAccounting.short_degree]; decide) n
  have hp:=PeriodicAccounting.Expr.bound75 (PeriodicAccounting.p2Expr P) (by rw [PeriodicAccounting.p2_degree]; decide) n
  have hl':=raise_height (show _≤(PeriodicAccounting.longExpr P).coeff*(ThresholdBudget.base n)^75*(height n)^0 by simpa only [Nat.pow_zero,Nat.mul_one] using hl)
    (by decide : 0≤3)
  have hs':=raise_height (show _≤(PeriodicAccounting.shortExpr P).coeff*(ThresholdBudget.base n)^75*(height n)^0 by simpa only [Nat.pow_zero,Nat.mul_one] using hs)
    (by decide : 0≤3)
  have hp':=raise_height (show _≤(PeriodicAccounting.p2Expr P).coeff*(ThresholdBudget.base n)^75*(height n)^1 by
      simpa only [Nat.pow_one] using Nat.mul_le_mul_right (height n) hp) (by decide : 1≤3)
  unfold budget ThresholdBudget.block ThresholdBudget.length ThresholdBudget.period
  simp only [ThresholdBudget.period,Nat.add_mul,Nat.mul_assoc] at hp1 hp2 hl' hs' hp' ⊢
  omega

set_option exponentiation.threshold 1024 in
theorem budget_target (P : SevenDFA (Fin σ)) : Spec.Target25Over13 (budget P) := by
  obtain ⟨C,hC,h⟩:=budget_bound P
  refine ⟨C^13*(2^39)^25,39,Nat.mul_pos (Nat.pow_pos hC) (Nat.pow_pos (Nat.pow_pos (by decide))),?_⟩
  intro n
  have hh:=Nat.pow_le_pow_left (h n) 13
  have he : ((ThresholdBudget.base n)^75)^13=((ThresholdBudget.base n)^39)^25 := by
    rw [←Nat.pow_mul,←Nat.pow_mul]
  rw [Nat.mul_pow,Nat.mul_pow,he] at hh
  rw [show ((height n)^3)^13=(height n)^39 by rw [←Nat.pow_mul]] at hh
  have ht:=Nat.pow_le_pow_left (ThresholdBudget.rounded_upper n) 25
  rw [Nat.mul_pow] at ht
  have hb:=Nat.mul_le_mul_right ((height n)^39) (Nat.mul_le_mul_left (C^13) ht)
  exact Nat.le_trans hh (by simpa only [height,Nat.mul_assoc] using hb)

end REWB.ResidualCached.Cost
