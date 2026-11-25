import REWB.ResidualCachedCost

/-! Rounded executable entry points and the target for their actual
returned ledgers. `Ready` is still needed for all-start row provenance;
the counters' exact scope is the one stated in ResidualCachedDispatch. -/
namespace REWB.ResidualCached
variable {σ : Nat}

theorem parameters (n : Nat) :
    0<ThresholdBudget.block n ∧ ThresholdBudget.block n≤ThresholdBudget.length n ∧
    0<ThresholdBudget.length n ∧ ThresholdBudget.period n≤ThresholdBudget.length n := by
  have ht:=ThresholdBudget.base_pos n
  exact ⟨Nat.pow_pos ht,Nat.pow_le_pow_right ht (by decide),Nat.pow_pos ht,
    Nat.pow_le_pow_right ht (by decide)⟩

namespace P1
def auto (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (bits : Inputs P text.toList.length (ThresholdBudget.block text.size)) : Execution :=
  execute P text fallback (ThresholdBudget.block text.size) (ThresholdBudget.length text.size)
    (ThresholdBudget.length text.size) (ThresholdBudget.period text.size) (parameters text.size).1 bits

theorem auto_correct (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (bits : Inputs P text.toList.length (ThresholdBudget.block text.size))
    (ready : Ready P text.toList (ThresholdBudget.block text.size) bits) :
    (auto P text fallback bits).answer=true ↔ MatchesWithin P.nested1 text.toList 2 :=
  execute_correct P text fallback _ _ _ _ (parameters text.size).1 (parameters text.size).2.1
    (parameters text.size).2.2.1 (parameters text.size).2.2.2 bits ready
end P1

namespace P2
def auto (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (bits : Inputs P text.toList.length (ThresholdBudget.block text.size)) : Execution :=
  execute P text fallback (ThresholdBudget.block text.size) (ThresholdBudget.length text.size)
    (ThresholdBudget.length text.size) (ThresholdBudget.period text.size) (parameters text.size).1 bits

theorem auto_correct (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (bits : Inputs P text.toList.length (ThresholdBudget.block text.size))
    (ready : Ready P text.toList (ThresholdBudget.block text.size) bits) :
    (auto P text fallback bits).answer=true ↔ MatchesWithin P.nested2 text.toList 2 :=
  execute_correct P text fallback _ _ _ _ (parameters text.size).1 (parameters text.size).2.1
    (parameters text.size).2.2.1 (parameters text.size).2.2.2 bits ready
end P2

theorem auto_accountedWork (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (one : P1.Inputs P text.toList.length (ThresholdBudget.block text.size))
    (two : P2.Inputs P text.toList.length (ThresholdBudget.block text.size)) :
    (P1.auto P text fallback one).accountedWork+(P2.auto P text fallback two).accountedWork≤Cost.budget P text.size := by
  have hp:=parameters text.size
  have h₁:=P1.execute_accountedWork P text fallback _ _ _ (ThresholdBudget.period text.size) hp.1 hp.2.2.1 hp.2.2.1 one
  have h₂:=P2.execute_accountedWork P text fallback _ _ _ (ThresholdBudget.period text.size) hp.1 hp.2.2.1 hp.2.2.1 two
  change (P1.auto P text fallback one).accountedWork≤_ at h₁
  change (P2.auto P text fallback two).accountedWork≤_ at h₂
  unfold Cost.budget
  change _≤_+_+_+_+_*PeriodicAccounting.logHeight text.size
  omega

/-- The concrete returned ledgers, uniformly over finite text/row
families. This includes no claim about the work of constructing the
input rows or the periodic operations absent from their old ledgers. -/
theorem auto_target (P : SevenDFA (Fin σ)) (texts : Nat→Array (Fin σ)) (fallback : Fin σ)
    (hsize : ∀n,(texts n).size=n)
    (one : ∀n,P1.Inputs P (texts n).toList.length (ThresholdBudget.block (texts n).size))
    (two : ∀n,P2.Inputs P (texts n).toList.length (ThresholdBudget.block (texts n).size)) :
    Spec.Target25Over13 (fun n=>(P1.auto P (texts n) fallback (one n)).accountedWork+
      (P2.auto P (texts n) fallback (two n)).accountedWork) := by
  obtain ⟨C,d,hC,h⟩:=Cost.budget_target P
  refine ⟨C,d,hC,?_⟩
  intro n
  have hh:=auto_accountedWork P (texts n) fallback (one n) (two n)
  rw [hsize] at hh
  exact Nat.le_trans (Nat.pow_le_pow_left hh 13) (h n)

end REWB.ResidualCached
