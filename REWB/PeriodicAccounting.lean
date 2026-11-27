import REWB.CountedP1Cubic
import REWB.SmallPeriodP2
import REWB.ThresholdBudget

/-! Aggregate bounds for the counters returned by the concrete periodic
    branches. These counters include their generated runs, contexts,
    exact keys, projection, decisions, sorting and chronological joins.
    This file does not call them a complete machine running time: initial
    formula assembly, window construction and allocation retain the
    limitations documented by the individual measured implementations. -/
namespace REWB.PeriodicAccounting
open REWB.UniformPhaseBounds
variable {σ : Nat}

/-- A small arithmetic language makes the polynomial domination proof
    compositional. Constants below are proof bounds, never preprocessing
    that an executable matcher is required to evaluate. -/
inductive Expr where
  | val : Nat → Expr
  | input : Expr
  | period : Expr
  | add : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | pow : Expr → Nat → Expr
  | bits : Expr → Expr

namespace Expr
def eval (n Q : Nat) : Expr → Nat
  | .val c => c
  | .input => n
  | .period => Q
  | .add a b => a.eval n Q+b.eval n Q
  | .mul a b => a.eval n Q*b.eval n Q
  | .pow a k => (a.eval n Q)^k
  | .bits a => (a.eval n Q).log2+1

def degree : Expr → Nat
  | .val _ => 0
  | .input => 39
  | .period => 9
  | .add a b => max a.degree b.degree
  | .mul a b => a.degree+b.degree
  | .pow a k => a.degree*k
  | .bits _ => 1

def coeff : Expr → Nat
  | .val c => c
  | .input => 1
  | .period => 1
  | .add a b => a.coeff+b.coeff
  | .mul a b => a.coeff*b.coeff
  | .pow a k => a.coeff^k
  | .bits a => a.coeff+1+2*a.degree

theorem bits_bound (x c t a : Nat) (ht : 1≤t) (hx : x≤c*t^a) :
    x.log2+1≤(c+1+2*a)*t := by
  have hp := Nat.mul_lt_mul_of_lt_of_le (Nat.lt_log2_self (n:=c))
    (Nat.pow_le_pow_left (Nat.le_of_lt (Nat.lt_log2_self (n:=t))) a)
    (Nat.pow_pos (Nat.pow_pos (by decide : 0<2)))
  rw [← Nat.pow_mul,← Nat.pow_add] at hp
  have hl : x.log2+1≤c.log2+1+(t.log2+1)*a := by
    by_cases hz : x=0
    · simp only [hz,Nat.log2_zero]; omega
    · have h := (Nat.log2_lt hz).mpr (Nat.lt_of_le_of_lt hx hp)
      omega
  have hc : c.log2+1≤(c+1)*t := by
    have h := Nat.log2_le_self c
    have hm := Nat.mul_le_mul_left (c+1) ht
    omega
  have ht' : t.log2+1≤2*t := by have h := Nat.log2_le_self t; omega
  have ha := Nat.mul_le_mul_right a ht'
  have he : (c+1)*t+(2*t)*a=(c+1+2*a)*t := by
    simp only [Nat.add_mul,Nat.mul_add]
    ac_rfl
  rw [← he]
  omega

theorem bound (e : Expr) (n Q t : Nat) (ht : 1≤t)
    (hn : n≤t^39) (hq : Q≤t^9) : e.eval n Q≤e.coeff*t^e.degree := by
  induction e with
  | val c => simp [eval,coeff,degree]
  | input => simpa [eval,coeff,degree] using hn
  | period => simpa [eval,coeff,degree] using hq
  | add a b ia ib =>
    have ha := Cost.pow_mono_exponent t a.degree (max a.degree b.degree) ht (Nat.le_max_left _ _)
    have hb := Cost.pow_mono_exponent t b.degree (max a.degree b.degree) ht (Nat.le_max_right _ _)
    have h := Nat.add_le_add
      (Nat.le_trans ia (Nat.mul_le_mul_left a.coeff ha))
      (Nat.le_trans ib (Nat.mul_le_mul_left b.coeff hb))
    simpa only [eval,coeff,degree,Nat.add_mul] using h
  | mul a b ia ib =>
    have h := Nat.mul_le_mul ia ib
    have he : (a.coeff*t^a.degree)*(b.coeff*t^b.degree)=
        (a.coeff*b.coeff)*t^(a.degree+b.degree) := by rw [Nat.pow_add]; ac_rfl
    simpa only [eval,coeff,degree,he] using h
  | pow a k ia =>
    have h := Nat.pow_le_pow_left ia k
    simpa only [eval,coeff,degree,Nat.mul_pow,← Nat.pow_mul] using h
  | bits a ia =>
    simpa only [eval,coeff,degree,Nat.pow_one] using bits_bound _ _ _ _ ht ia

theorem bound75 (e : Expr) (hd : e.degree≤75) (n : Nat) :
    e.eval n (ThresholdBudget.period n)≤e.coeff*(ThresholdBudget.base n)^75 := by
  have ht : 1≤ThresholdBudget.base n := ThresholdBudget.base_pos n
  have hn : n≤(ThresholdBudget.base n)^39 := by
    have h := ThresholdBudget.rounded_lower n
    omega
  have h := bound e n (ThresholdBudget.period n) (ThresholdBudget.base n) ht hn (Nat.le_refl _)
  exact Nat.le_trans h (Nat.mul_le_mul_left _ (Cost.pow_mono_exponent _ _ _ ht hd))
end Expr

private abbrev c := Expr.val
private abbrev x := Expr.input
private abbrev q := Expr.period
local infixl:65 " +ₑ " => Expr.add
local infixl:70 " *ₑ " => Expr.mul
private def h : Expr := .bits x
private def mass : Expr := c 2 *ₑ x *ₑ h
private def enumeration : Expr := q *ₑ (x +ₑ (x +ₑ c 1) *ₑ (c 2 *ₑ q *ₑ (q +ₑ c 1) +ₑ c 1))
private def sourceCount : Expr := c 3 *ₑ q *ₑ mass
private def targetCount : Expr := c 3 *ₑ .pow q 3 *ₑ mass
private def shortSourceCount : Expr := (x +ₑ c 1) *ₑ (c 3 *ₑ q)
private def shortTargetCount : Expr := c 9 *ₑ .pow q 3 *ₑ mass
private def context (P : SevenDFA (Fin σ)) : Expr := (x +ₑ c 1) *ₑ c (1+P.H.stateCount)
private def cache (P : SevenDFA (Fin σ)) : Expr :=
  (c (FullyCachedP2.stateSum P) *ₑ q +ₑ .pow q 2) *ₑ mass
private def window (P : SevenDFA (Fin σ)) : Expr :=
  c (p1Modulus P) *ₑ (c (p1SourceBudget P) *ₑ sourceCount +ₑ
    c P.C.stateCount *ₑ (c (p1TargetBudget P) *ₑ targetCount))
private def shortWindow (P : SevenDFA (Fin σ)) : Expr :=
  shortSourceCount +ₑ c P.C.stateCount *ₑ shortTargetCount
private def sortBound (W : Expr) : Expr := (h +ₑ c 1) *ₑ (c 10 *ₑ W *ₑ .bits W)

def longExpr (P : SevenDFA (Fin σ)) : Expr :=
  enumeration +ₑ context P +ₑ ((c (3*σ+1) *ₑ q +ₑ c 1) *ₑ mass) +ₑ cache P +ₑ
  (c 9 *ₑ .pow q 3 *ₑ mass) +ₑ (c (CountedCachedP1.targetSteps P) *ₑ targetCount) +ₑ
  (c 2 *ₑ (c (p1SourceBudget P+1) *ₑ sourceCount +ₑ c (p1TargetBudget P+1) *ₑ targetCount) +ₑ c 3) +ₑ
  ((h +ₑ c 1) *ₑ window P) +ₑ ((h +ₑ c 1) *ₑ (sourceCount +ₑ targetCount)) +ₑ
  ((h +ₑ c 1) *ₑ x) +ₑ sortBound (window P) +ₑ (c 4 *ₑ (x +ₑ c 1))

def shortExpr (P : SevenDFA (Fin σ)) : Expr :=
  enumeration +ₑ context P +ₑ
  ((c (3*σ+1) *ₑ (c 3 *ₑ q) +ₑ c 1) *ₑ shortSourceCount +ₑ
    (c (P1ShortKeys.workConstant σ) *ₑ .pow q 2 +ₑ c 3 *ₑ q) *ₑ mass) +ₑ
  shortSourceCount +ₑ ((c 3 *ₑ q) *ₑ shortSourceCount) +ₑ cache P +ₑ
  (c (CountedShortTargets.anchorWork P) *ₑ targetCount) +ₑ
  ((h +ₑ c 1) *ₑ shortWindow P) +ₑ ((h +ₑ c 1) *ₑ (shortSourceCount +ₑ shortTargetCount)) +ₑ
  ((h +ₑ c 1) *ₑ x) +ₑ sortBound (shortWindow P) +ₑ (c 4 *ₑ (x +ₑ c 1))

/-- The common height factor is kept outside this P2 expression. -/
def p2Expr (P : SevenDFA (Fin σ)) : Expr :=
  enumeration +ₑ context P +ₑ
  ((c (FullyCachedP2.stateSum P) *ₑ q +ₑ .pow q 2) *ₑ (c 2 *ₑ x)) +ₑ
  ((c 7 +ₑ c (CountedProjection.p2Steps P)) *ₑ (.pow q 4 *ₑ (c 2 *ₑ x)))

theorem long_degree (P : SevenDFA (Fin σ)) : (longExpr P).degree=69 := by
  simp only [longExpr,enumeration,context,cache,sourceCount,targetCount,mass,
    sortBound,window,h,c,x,q,Expr.degree]
  decide
theorem short_degree (P : SevenDFA (Fin σ)) : (shortExpr P).degree=69 := by
  simp only [shortExpr,enumeration,context,cache,sourceCount,targetCount,mass,
    shortSourceCount,shortTargetCount,sortBound,shortWindow,h,c,x,q,Expr.degree]
  decide
theorem p2_degree (P : SevenDFA (Fin σ)) : (p2Expr P).degree=75 := by
  simp only [p2Expr,enumeration,context,c,x,q,Expr.degree]
  decide

/-- Sum only counters that the returned execution actually measured. -/
def longWork (r : CountedSmallPeriodP1.Result) : Nat :=
  r.runComparisons+r.contextEntries+r.keyWork+r.cacheWork+r.equalityReads+
  r.projectionSteps+r.modulusSteps+r.tests+r.eventVisits+r.textVisits+r.sortSteps+r.nodes

def shortWork (r : CountedShortBranch.Result) : Nat :=
  r.runComparisons+r.contextEntries+r.keyWork+r.sourcePrefixReads+r.sourceWordCells+
  r.targets.cacheWork+r.targetWork+r.tests+r.eventVisits+r.textVisits+r.sortSteps+r.nodes

def p2Work (r : SmallPeriodP2.Result) : Nat :=
  r.runComparisons+r.contextEntries+r.cacheWork+r.phaseCalls+r.equalityReads+r.projectionSteps

theorem join_nodes (d : DFA α) (K N : Nat) (w : Word α)
    (es fs : List TimedJoin.TimedEntry) :
    (OfflineJoin.run d K N w es fs).nodes≤4*(w.length+1) := by
  have hn := (OfflineJoin.solve_cost d K N (DyadicIndex.heightFor w.length) w es fs).2.2.2
  have hp : 2^w.length.log2≤w.length+1 := by
    by_cases hz : w.length=0
    · simp [hz]
    · exact Nat.le_trans (Nat.log2_self_le hz) (by omega)
  have hb := Nat.mul_le_mul_left 4 hp
  have he : 2^(DyadicIndex.heightFor w.length+1)=4*2^w.length.log2 := by
    unfold DyadicIndex.heightFor
    rw [Nat.add_assoc,Nat.pow_add]
    simp only [Nat.reduceAdd,Nat.reducePow]
    ac_rfl
  rw [he] at hn
  change (OfflineJoin.solve d K N (DyadicIndex.heightFor w.length) w es fs).nodes≤_
  omega

theorem long_bound (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    longWork (CountedSmallPeriodP1.solve P f n Q)≤(longExpr P).eval n Q := by
  obtain ⟨hr,hc,hk,_,hcache,he,hp⟩ := CountedSmallPeriodP1.solve_prepare_counts P f n Q
  obtain ⟨ht,hev,htx,hs⟩ := CountedSmallPeriodP1.solve_counts P f n Q
  have hm := CountedSmallPeriodP1.solve_modulus_steps_bound P f n Q
  have hn : (CountedSmallPeriodP1.solve P f n Q).nodes≤4*(n+1) := by
    change (CountedSmallPeriodP1.solve P f n Q).toResult.nodes≤_
    rw [CountedSmallPeriodP1.solve_value]
    simpa only [Periodic.segment_length] using join_nodes P.C _ n (Periodic.segment f 0 n) _ _
  simp only [longWork,longExpr,enumeration,context,cache,sourceCount,targetCount,mass,
    sortBound,window,h,c,x,q,Expr.eval,CountedSmallPeriodP1.windowBudget,
    DyadicIndex.heightFor,Nat.mul_assoc] at *
  omega

theorem short_bound (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    shortWork (CountedShortBranch.solve P f n Q)≤(shortExpr P).eval n Q := by
  obtain ⟨hr,hc,hk,_,hpre,hcells⟩ := CountedShortBranch.solve_prepare_counts P f n Q
  obtain ⟨hcache,hwork⟩ := CountedShortBranch.solve_target_counts P f n Q
  obtain ⟨ht,hev,htx,hs⟩ := CountedShortBranch.solve_counts P f n Q
  have hn : (CountedShortBranch.solve P f n Q).nodes≤4*(n+1) := by
    change (CountedShortBranch.solve P f n Q).toResult.nodes≤_
    rw [CountedShortBranch.solve_value]
    simpa only [Periodic.segment_length] using join_nodes P.C 1 0 (Periodic.segment f 0 n) _ _
  simp only [shortWork,shortExpr,enumeration,context,cache,sourceCount,targetCount,mass,
    shortSourceCount,shortTargetCount,sortBound,shortWindow,h,c,x,q,Expr.eval,
    CountedShortBranch.eventBudget,DyadicIndex.heightFor,Nat.mul_assoc] at *
  omega

def logHeight (n : Nat) : Nat := (n+2).log2+1

theorem height_le (n : Nat) : DyadicIndex.heightFor n≤logHeight n := by
  exact Nat.add_le_add_right (CountedJoin.log2_mono (show n≤n+2 by omega)) 1

theorem p2_bound (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    p2Work (SmallPeriodP2.solve P f n Q)≤(p2Expr P).eval n Q*logHeight n := by
  obtain ⟨hr,hc,hcache,hphase,he⟩ := SmallPeriodP2.solve_counts P f n Q
  have hp := SmallPeriodP2.solve_projection_steps P f n Q
  have hh := height_le n
  have hpos : 1≤logHeight n := by unfold logHeight; omega
  have hr' := Nat.le_trans hr (by simpa only [Nat.mul_one] using
    (Nat.mul_le_mul_left (Q*(n+(n+1)*(2*Q*(Q+1)+1))) hpos))
  have hc' : (SmallPeriodP2.solve P f n Q).contextEntries≤
      ((n+1)*(1+P.H.stateCount))*logHeight n := by
    rw [hc]
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left ((n+1)*(1+P.H.stateCount)) hpos
  have hm := Nat.mul_le_mul_left (2*n) hh
  have ha := Nat.le_trans hcache (Nat.mul_le_mul_left (FullyCachedP2.stateSum P*Q+Q^2) hm)
  have hb := Nat.le_trans hphase (Nat.mul_le_mul_left (Q^4) hm)
  have hd := Nat.le_trans he (Nat.mul_le_mul_left 6 (Nat.mul_le_mul_left (Q^4) hm))
  have hf := Nat.le_trans hp (Nat.mul_le_mul_left (CountedProjection.p2Steps P*Q^4) hm)
  simp only [p2Work,p2Expr,enumeration,context,c,x,q,Expr.eval,Nat.add_mul,Nat.mul_assoc] at *
  omega

/-- Aggregate of the actual counters of both cubic P1 paths and the P2
    phase matcher at the integer-rounded common threshold. -/
def measured (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n : Nat) : Nat :=
  let Q := ThresholdBudget.period n
  longWork (CountedSmallPeriodP1.solve P f n Q)+
  shortWork (CountedShortBranch.solve P f n Q)+
  p2Work (SmallPeriodP2.solve P f n Q)

def coefficient (P : SevenDFA (Fin σ)) : Nat :=
  (longExpr P).coeff+(shortExpr P).coeff+(p2Expr P).coeff+1

theorem measured_bound (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n : Nat) :
    measured P f n≤coefficient P*(ThresholdBudget.base n)^75*logHeight n := by
  have hl := Nat.le_trans (long_bound P f n (ThresholdBudget.period n))
    (Expr.bound75 (longExpr P) (by rw [long_degree]; decide) n)
  have hs := Nat.le_trans (short_bound P f n (ThresholdBudget.period n))
    (Expr.bound75 (shortExpr P) (by rw [short_degree]; decide) n)
  have hp := Nat.le_trans (p2_bound P f n (ThresholdBudget.period n))
    (Nat.mul_le_mul_right (logHeight n) (Expr.bound75 (p2Expr P) (by rw [p2_degree]; exact Nat.le_refl _) n))
  have hh : 1≤logHeight n := by unfold logHeight; omega
  have hl' := Nat.le_trans hl (by simpa only [Nat.mul_one] using
    (Nat.mul_le_mul_left ((longExpr P).coeff*(ThresholdBudget.base n)^75) hh))
  have hs' := Nat.le_trans hs (by simpa only [Nat.mul_one] using
    (Nat.mul_le_mul_left ((shortExpr P).coeff*(ThresholdBudget.base n)^75) hh))
  simp only [measured,coefficient,Nat.add_mul,Nat.one_mul]
  omega

def targetConstant (P : SevenDFA (Fin σ)) : Nat := (coefficient P)^13*(2^39)^25

set_option exponentiation.threshold 1024 in
theorem measured_power (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n : Nat) :
    (measured P f n)^13≤targetConstant P*(n+2)^25*(logHeight n)^13 := by
  have h := Nat.pow_le_pow_left (measured_bound P f n) 13
  have he : ((ThresholdBudget.base n)^75)^13=((ThresholdBudget.base n)^39)^25 := by
    rw [← Nat.pow_mul,← Nat.pow_mul]
  rw [Nat.mul_pow,Nat.mul_pow,he] at h
  have hu := Nat.pow_le_pow_left (ThresholdBudget.rounded_upper n) 25
  rw [Nat.mul_pow] at hu
  exact Nat.le_trans h (by
    simpa only [targetConstant,Nat.mul_assoc] using
      Nat.mul_le_mul_right ((logHeight n)^13) (Nat.mul_le_mul_left ((coefficient P)^13) hu))

/-- Uniform over all input families. This theorem is about the defined
    returned counters, not the missing complete matcher time model. -/
theorem measured_target (P : SevenDFA (Fin σ)) (texts : Nat→Nat→Fin σ) :
    Spec.Target25Over13 (fun n=>measured P (texts n) n) := by
  refine ⟨targetConstant P,13,?_,?_⟩
  · apply Nat.mul_pos
    · apply Nat.pow_pos
      unfold coefficient
      omega
    · exact Nat.pow_pos (Nat.pow_pos (by decide))
  · intro n
    exact measured_power P (texts n) n

end REWB.PeriodicAccounting
