import REWB.PeriodicActualBranch
import REWB.PeriodicActualPrepareCost
import REWB.PeriodicActualMeasures

/-! Bounds for the actual external periodic branches.  The new preparation,
formula/event construction and chronological-join construction are charged
together with the original join counters from the same execution.
The discovery, cache and exact-key primitive counters retain their stated
unit-cost scopes; these theorems make no machine-bit or allocation claim. -/
namespace REWB.PeriodicActual
open REWB.PeriodicAccounting REWB.UniformPhaseBounds
variable {σ : Nat}

theorem long_expr_events (P : SevenDFA (Fin σ)) (n Q : Nat) :
    (DyadicIndex.heightFor n+1)*
      (3*Q*(2*n*DyadicIndex.heightFor n)+3*Q^3*(2*n*DyadicIndex.heightFor n))≤
      (longExpr P).eval n Q := by
  change (n.log2+1+1)*(3*Q*(2*n*(n.log2+1))+3*Q^3*(2*n*(n.log2+1)))≤
    _+(n.log2+1+1)*(3*Q*(2*n*(n.log2+1))+3*Q^3*(2*n*(n.log2+1)))+_+_+_
  omega

theorem short_expr_events (P : SevenDFA (Fin σ)) (n Q : Nat) :
    (DyadicIndex.heightFor n+1)*
      ((n+1)*(3*Q)+9*Q^3*(2*n*DyadicIndex.heightFor n))≤
      (shortExpr P).eval n Q := by
  change (n.log2+1+1)*((n+1)*(3*Q)+9*Q^3*(2*n*(n.log2+1)))≤
    _+(n.log2+1+1)*((n+1)*(3*Q)+9*Q^3*(2*n*(n.log2+1)))+_+_+_
  omega

/-- Both the actual event volume and the empty chronological leaves are
absorbed by explicit terms of the established branch expression. -/
theorem join_volume_expr (n es fs S T B : Nat) (he : es≤S) (hf : fs≤T)
    (hev : (DyadicIndex.heightFor n+1)*(S+T)≤B)
    (htx : (DyadicIndex.heightFor n+1)*n≤B) (hin : n+1≤B) :
    (DyadicIndex.heightFor n+1)*(es+fs+5*(n+1))≤16*B := by
  have hevents := Nat.le_trans
    (Nat.mul_le_mul_left (DyadicIndex.heightFor n+1) (Nat.add_le_add he hf)) hev
  have hh : DyadicIndex.heightFor n+1≤2*(n+1) := by
    have hl := Nat.log2_le_self n
    unfold DyadicIndex.heightFor
    omega
  have hh' : DyadicIndex.heightFor n+1≤2*B :=
    Nat.le_trans hh (Nat.mul_le_mul_left 2 hin)
  have hlin : (DyadicIndex.heightFor n+1)*(n+1)≤3*B := by
    simp only [Nat.mul_add,Nat.mul_one]
    omega
  have hextra := Nat.mul_le_mul_left 5 hlin
  have heq : (DyadicIndex.heightFor n+1)*(es+fs+5*(n+1))=
      (DyadicIndex.heightFor n+1)*(es+fs)+
        5*((DyadicIndex.heightFor n+1)*(n+1)) := by
    rw [Nat.mul_add]
    ac_rfl
  rw [heq]
  omega

namespace Long

def joinCoefficient (P : SevenDFA (Fin σ)) : Nat :=
  Join.coefficient P.C.stateCount (p1Modulus P) (p1SourceBudget P+p1TargetBudget P)+10

def branchCoefficient (P : SevenDFA (Fin σ)) : Nat :=
  coefficient P+16*joinCoefficient P+6

theorem solve_construction_expr (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n Q : Nat) :
    (solve P f n Q).constructionWork≤
      (16*joinCoefficient P)*(longExpr P).eval n Q := by
  have hs : Join.bounded (P1Events.generated P f n Q).sources
      (p1SourceBudget P+p1TargetBudget P) := by
    intro e he
    exact Nat.le_trans (Measures.long_sources P f n Q e he) (by omega)
  have ht : Join.bounded (P1Events.generated P f n Q).targets
      (p1SourceBudget P+p1TargetBudget P) := by
    intro e he
    exact Nat.le_trans (Measures.long_targets P f n Q e he) (by omega)
  have hj := Join.run_work_bound_modulus P.C
    (CountedSmallPeriodP1.solve P f n Q).modulus n (p1Modulus P)
    (Periodic.segment f 0 n) (P1Events.generated P f n Q).sources
    (P1Events.generated P f n Q).targets (p1SourceBudget P+p1TargetBudget P) hs ht
    (CountedSmallPeriodP1.solve_modulus P f n Q).2
  simp only [Periodic.segment_length] at hj
  change _≤joinCoefficient P*(DyadicIndex.heightFor n+1)*
    ((P1Events.generated P f n Q).sources.length+
      (P1Events.generated P f n Q).targets.length+5*(n+1)) at hj
  have hv := join_volume_expr n _ _ _ _ ((longExpr P).eval n Q)
    (P1Events.generated_sizes P f n Q).1 (P1Events.generated_sizes P f n Q).2
    (long_expr_events P n Q) (long_expr_text P n Q) (long_expr_input P n Q)
  have hm := Nat.mul_le_mul_left (joinCoefficient P) hv
  have hout : (Join.run P.C (CountedSmallPeriodP1.solve P f n Q).modulus n
      (Periodic.segment f 0 n) (P1Events.generated P f n Q).sources
      (P1Events.generated P f n Q).targets).2≤
      (16*joinCoefficient P)*(longExpr P).eval n Q := by
    calc
      _≤joinCoefficient P*(16*(longExpr P).eval n Q) :=
        Nat.le_trans hj (by simpa only [Nat.mul_assoc] using hm)
      _=(16*joinCoefficient P)*(longExpr P).eval n Q := by ac_rfl
  simpa only [solve_constructionWork,prepare_text,prepare_sources,prepare_targets,
    prepare_modulus] using hout

theorem solve_expr (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n Q : Nat) :
    (solve P f n Q).work≤branchCoefficient P*(longExpr P).eval n Q := by
  have hp := prepare_expr P f n Q
  have hj := solve_construction_expr P f n Q
  have hl := Nat.le_trans (solve_joinLedger P f n Q) (long_bound P f n Q)
  have hi := long_expr_input P n Q
  rw [BranchResult.work,solve_preparationWork]
  unfold branchCoefficient
  simp only [Nat.add_mul]
  omega

theorem solve_rounded (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n : Nat) :
    (solve P f n (ThresholdBudget.period n)).work≤
      (branchCoefficient P*(longExpr P).coeff)*(ThresholdBudget.base n)^75 := by
  have hb := PeriodicAccounting.Expr.bound75 (longExpr P) (by rw [long_degree]; decide) n
  exact Nat.le_trans (solve_expr P f n (ThresholdBudget.period n))
    (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (branchCoefficient P) hb)

end Long

namespace Short

def joinCoefficient (P : SevenDFA (Fin σ)) : Nat := Join.coefficient P.C.stateCount 1 1+10

def branchCoefficient (P : SevenDFA (Fin σ)) : Nat :=
  coefficient P+16*joinCoefficient P+6

theorem solve_construction_expr (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n Q : Nat) :
    (solve P f n Q).constructionWork≤
      (16*joinCoefficient P)*(shortExpr P).eval n Q := by
  have hs : Join.bounded (P1ShortBranch.sourceList P f n Q) 1 := by
    intro e he
    exact Nat.le_of_eq (Measures.short_sources P f n Q e he)
  have ht : Join.bounded (P1ShortBranch.targetList P f n Q) 1 := by
    intro e he
    exact Nat.le_of_eq (Measures.short_targets P f n Q e he)
  have hj := Join.run_work_bound_modulus P.C 1 0 1 (Periodic.segment f 0 n)
    (P1ShortBranch.sourceList P f n Q) (P1ShortBranch.targetList P f n Q)
    1 hs ht (Nat.le_refl _)
  simp only [Periodic.segment_length] at hj
  change _≤joinCoefficient P*(DyadicIndex.heightFor n+1)*
    ((P1ShortBranch.sourceList P f n Q).length+
      (P1ShortBranch.targetList P f n Q).length+5*(n+1)) at hj
  have hv := join_volume_expr n _ _ _ _ ((shortExpr P).eval n Q)
    (P1ShortBranch.sourceList_bound P f n Q) (P1ShortBranch.targetList_bound P f n Q)
    (short_expr_events P n Q) (short_expr_text P n Q) (short_expr_input P n Q)
  have hm := Nat.mul_le_mul_left (joinCoefficient P) hv
  have hout : (Join.run P.C 1 0 (Periodic.segment f 0 n)
      (P1ShortBranch.sourceList P f n Q) (P1ShortBranch.targetList P f n Q)).2≤
      (16*joinCoefficient P)*(shortExpr P).eval n Q := by
    calc
      _≤joinCoefficient P*(16*(shortExpr P).eval n Q) :=
        Nat.le_trans hj (by simpa only [Nat.mul_assoc] using hm)
      _=(16*joinCoefficient P)*(shortExpr P).eval n Q := by ac_rfl
  simpa only [solve_constructionWork,prepare_text,prepare_sources,prepare_targets,
    prepare_modulus] using hout

theorem solve_expr (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n Q : Nat) :
    (solve P f n Q).work≤branchCoefficient P*(shortExpr P).eval n Q := by
  have hp := prepare_expr P f n Q
  have hj := solve_construction_expr P f n Q
  have hl := Nat.le_trans (solve_joinLedger P f n Q) (short_bound P f n Q)
  have hi := short_expr_input P n Q
  rw [BranchResult.work,solve_preparationWork]
  unfold branchCoefficient
  simp only [Nat.add_mul]
  omega

theorem solve_rounded (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n : Nat) :
    (solve P f n (ThresholdBudget.period n)).work≤
      (branchCoefficient P*(shortExpr P).coeff)*(ThresholdBudget.base n)^75 := by
  have hb := PeriodicAccounting.Expr.bound75 (shortExpr P) (by rw [short_degree]; decide) n
  exact Nat.le_trans (solve_expr P f n (ThresholdBudget.period n))
    (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (branchCoefficient P) hb)

end Short

namespace Cubic

/-- The two existing periodic P1 expressions; the new construction does
not require another input- or period-dependent factor. -/
def expr (P : SevenDFA (Fin σ)) : PeriodicAccounting.Expr := .add (longExpr P) (shortExpr P)

def coefficient (P : SevenDFA (Fin σ)) : Nat :=
  Long.branchCoefficient P+Short.branchCoefficient P+3

theorem expr_degree (P : SevenDFA (Fin σ)) : (expr P).degree=69 := by
  simp only [expr,PeriodicAccounting.Expr.degree,long_degree,short_degree,Nat.max_self]

theorem expr_input (P : SevenDFA (Fin σ)) (n Q : Nat) :
    n+1≤(expr P).eval n Q := by
  have h := long_expr_input P n Q
  change n+1≤(longExpr P).eval n Q+(shortExpr P).eval n Q
  omega

theorem solve_expr (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n Q : Nat) :
    (solve P f n Q).2≤coefficient P*(expr P).eval n Q := by
  have hl := Long.solve_expr P f n Q
  have hs := Short.solve_expr P f n Q
  have hll := Nat.mul_le_mul_left (Long.branchCoefficient P)
    (show (longExpr P).eval n Q≤(expr P).eval n Q by change _≤_+_; omega)
  have hss := Nat.mul_le_mul_left (Short.branchCoefficient P)
    (show (shortExpr P).eval n Q≤(expr P).eval n Q by change _≤_+_; omega)
  have hi := expr_input P n Q
  rw [solve_work]
  unfold coefficient
  simp only [Nat.add_mul]
  omega

theorem solve_rounded (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n : Nat) :
    (solve P f n (ThresholdBudget.period n)).2≤
      (coefficient P*(expr P).coeff)*(ThresholdBudget.base n)^75 := by
  have hb := PeriodicAccounting.Expr.bound75 (expr P) (by rw [expr_degree]; decide) n
  exact Nat.le_trans (solve_expr P f n (ThresholdBudget.period n))
    (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (coefficient P) hb)

end Cubic

/-- The returned unit-cost ledger of all three actual external periodic
branches at the common integer threshold. -/
def roundedWork (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n : Nat) : Nat :=
  (Cubic.solve P f n (ThresholdBudget.period n)).2+
  (P2.solve P f n (ThresholdBudget.period n)).2

def roundedCoefficient (P : SevenDFA (Fin σ)) : Nat :=
  Cubic.coefficient P*(Cubic.expr P).coeff+
  P2.coefficient P*(p2Expr P).coeff+1

theorem rounded_bound (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n : Nat) :
    roundedWork P f n≤
      roundedCoefficient P*(ThresholdBudget.base n)^75*logHeight n := by
  have hc := Cubic.solve_rounded P f n
  have hp := P2.solve_rounded P f n
  have hh : 1≤logHeight n := by unfold logHeight; omega
  have hc' := Nat.le_trans hc (by
    simpa only [Nat.mul_one] using
      (Nat.mul_le_mul_left ((Cubic.coefficient P*(Cubic.expr P).coeff)*(ThresholdBudget.base n)^75) hh))
  simp only [roundedWork,roundedCoefficient,Nat.add_mul,Nat.one_mul]
  omega

def targetConstant (P : SevenDFA (Fin σ)) : Nat := (roundedCoefficient P)^13*(2^39)^25

set_option exponentiation.threshold 1024 in
theorem rounded_power (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n : Nat) :
    (roundedWork P f n)^13≤targetConstant P*(n+2)^25*(logHeight n)^13 := by
  have h := Nat.pow_le_pow_left (rounded_bound P f n) 13
  have he : ((ThresholdBudget.base n)^75)^13=((ThresholdBudget.base n)^39)^25 := by
    rw [← Nat.pow_mul,← Nat.pow_mul]
  rw [Nat.mul_pow,Nat.mul_pow,he] at h
  have hu := Nat.pow_le_pow_left (ThresholdBudget.rounded_upper n) 25
  rw [Nat.mul_pow] at hu
  exact Nat.le_trans h (by
    simpa only [targetConstant,Nat.mul_assoc] using
      Nat.mul_le_mul_right ((logHeight n)^13)
        (Nat.mul_le_mul_left ((roundedCoefficient P)^13) hu))

theorem rounded_target (P : SevenDFA (Fin σ)) (texts : Nat → Nat → Fin σ) :
    Spec.Target25Over13 (fun n => roundedWork P (texts n) n) := by
  refine ⟨targetConstant P,13,?_,?_⟩
  · apply Nat.mul_pos
    · apply Nat.pow_pos
      unfold roundedCoefficient
      omega
    · exact Nat.pow_pos (Nat.pow_pos (by decide))
  · intro n
    exact rounded_power P (texts n) n

end REWB.PeriodicActual
