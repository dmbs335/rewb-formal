import REWB.ResidualCachedP1
import REWB.ResidualCachedP2
import REWB.ShortOuterDispatch
import REWB.ShortOuterCost
import REWB.ResidualDispatchCost
import REWB.PeriodicAccounting

/-! Executable final P1/P2 dispatch, conditional only on the provenance
of the supplied finite all-start rows. A fixed variant bank is built
once; each actual generated window is queried from that bank.

`residualWork` includes the full counters of the new short-outer,
schedule, cache, selector and fold paths, including text materialization.
The existing periodic result is retained separately because its ledger
does not yet claim complete formula/window-construction machine cost.
Producing the supplied all-start rows is also a separate obligation.
Neither gap is silently assigned zero in a total-runtime theorem. -/
namespace REWB.ResidualCached
variable {σ : Nat}

namespace P1

structure Execution where
  periodic : CountedP1Cubic.Result
  answer : Bool
  residualWork : Nat

def execute (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) (bits : Inputs P text.toList.length s) : Execution :=
  let w:=text.toList
  let read:=ArrayText.read text fallback
  let periodic:=CountedP1Cubic.solve P read text.size Q
  let short:=ShortOuter.P1.solve P text fallback L
  let schedule:=ResidualDispatch.prepare read text.size s L D Q
  let cache:=build P w fallback s hs bits
  let checked:=any (query cache) schedule.windows
  ⟨periodic,periodic.answer || short.answer || checked.1,
    short.work+schedule.work+cache.work+checked.2+text.size+10⟩

theorem execute_correct (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) (hSL : s≤L) (hD : 0<D) (hQL : Q≤L)
    (bits : Inputs P text.toList.length s) (ready : Ready P text.toList s bits) :
    (execute P text fallback s L D Q hs bits).answer=true ↔ MatchesWithin P.nested1 text.toList 2 := by
  rw [ShortOuter.p1_dispatch_iff P text fallback s L D Q hs hSL hD hQL]
  change ((CountedP1Cubic.solve P (ArrayText.read text fallback) text.size Q).answer ||
    (ShortOuter.P1.solve P text fallback L).answer ||
    (any (query (build P text.toList fallback s hs bits))
      (ResidualDispatch.prepare (ArrayText.read text fallback) text.size s L D Q).windows).1)=true ↔ _
  simp only [Bool.or_eq_true,any_correct,query_correct P text.toList fallback s hs bits ready,or_assoc]

def residualBudget (P : SevenDFA (Fin σ)) (n s L D Q : Nat) : Nat :=
  ShortOuter.P1.budget P n L+ResidualDispatch.preparationBudget σ n s L D Q+
    buildBudget P n s+ResidualDispatch.selectorBudget n L D Q*(queryBudget P n s+3)+n+11

theorem execute_residualWork (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) (hL : 0<L) (hD : 0<D)
    (bits : Inputs P text.toList.length s) :
    (execute P text fallback s L D Q hs bits).residualWork≤residualBudget P text.size s L D Q := by
  have hshort:=ShortOuter.P1.solve_work P text fallback L
  have hplan:=ResidualDispatch.prepare_work (ArrayText.read text fallback) text.size s L D Q hD hL
  have hbank:=build_work P text.toList fallback s hs bits
  rw [Array.length_toList] at hbank
  have hquery:=any_work (query (build P text.toList fallback s hs bits))
      (ResidualDispatch.prepare (ArrayText.read text fallback) text.size s L D Q).windows
      (queryBudget P text.size s) (by
        intro c hc
        have hwin:=ResidualDispatch.prepare_sound (ArrayText.read text fallback) text.size s L D Q c hc
        rw [ShortOuter.full_read] at hwin
        simpa only [Array.length_toList] using query_work P text.toList fallback s hs bits c hwin)
  have hlength:=ResidualDispatch.prepare_windows (ArrayText.read text fallback) text.size s L D Q hD hL
  have hmul:=Nat.mul_le_mul_right (queryBudget P text.size s+3) hlength
  change (ShortOuter.P1.solve P text fallback L).work+
    (ResidualDispatch.prepare (ArrayText.read text fallback) text.size s L D Q).work+
    (build P text.toList fallback s hs bits).work+
    (any (query (build P text.toList fallback s hs bits))
      (ResidualDispatch.prepare (ArrayText.read text fallback) text.size s L D Q).windows).2+text.size+10≤_
  unfold residualBudget
  omega

def Execution.accountedWork (r : Execution) : Nat :=
  r.residualWork+PeriodicAccounting.longWork r.periodic.long+PeriodicAccounting.shortWork r.periodic.short

theorem execute_accountedWork (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) (hL : 0<L) (hD : 0<D)
    (bits : Inputs P text.toList.length s) :
    (execute P text fallback s L D Q hs bits).accountedWork≤
      residualBudget P text.size s L D Q+(PeriodicAccounting.longExpr P).eval text.size Q+
        (PeriodicAccounting.shortExpr P).eval text.size Q := by
  have hr:=execute_residualWork P text fallback s L D Q hs hL hD bits
  have hl:=PeriodicAccounting.long_bound P (ArrayText.read text fallback) text.size Q
  have hh:=PeriodicAccounting.short_bound P (ArrayText.read text fallback) text.size Q
  exact Nat.add_le_add (Nat.add_le_add hr hl) hh

end P1

namespace P2

structure Execution where
  periodic : SmallPeriodP2.Result
  answer : Bool
  residualWork : Nat

def execute (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) (bits : Inputs P text.toList.length s) : Execution :=
  let w:=text.toList
  let read:=ArrayText.read text fallback
  let periodic:=SmallPeriodP2.solve P read text.size Q
  let short:=ShortOuter.P2.solve P text fallback L
  let schedule:=ResidualDispatch.prepare read text.size s L D Q
  let cache:=build P w fallback s hs bits
  let checked:=any (query cache) schedule.windows
  ⟨periodic,periodic.accepted || short.answer || checked.1,
    short.work+schedule.work+cache.work+checked.2+text.size+10⟩

theorem execute_correct (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) (hSL : s≤L) (hD : 0<D) (hQL : Q≤L)
    (bits : Inputs P text.toList.length s) (ready : Ready P text.toList s bits) :
    (execute P text fallback s L D Q hs bits).answer=true ↔ MatchesWithin P.nested2 text.toList 2 := by
  rw [ShortOuter.p2_dispatch_iff P text fallback s L D Q hs hSL hD hQL]
  change ((SmallPeriodP2.solve P (ArrayText.read text fallback) text.size Q).accepted ||
    (ShortOuter.P2.solve P text fallback L).answer ||
    (any (query (build P text.toList fallback s hs bits))
      (ResidualDispatch.prepare (ArrayText.read text fallback) text.size s L D Q).windows).1)=true ↔ _
  simp only [Bool.or_eq_true,any_correct,query_correct P text.toList fallback s hs bits ready,or_assoc]

def residualBudget (P : SevenDFA (Fin σ)) (n s L D Q : Nat) : Nat :=
  ShortOuter.P2.budget P n L+ResidualDispatch.preparationBudget σ n s L D Q+
    buildBudget P n s+ResidualDispatch.selectorBudget n L D Q*(queryBudget P n s+3)+n+11

theorem execute_residualWork (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) (hL : 0<L) (hD : 0<D)
    (bits : Inputs P text.toList.length s) :
    (execute P text fallback s L D Q hs bits).residualWork≤residualBudget P text.size s L D Q := by
  have hshort:=ShortOuter.P2.solve_work P text fallback L
  have hplan:=ResidualDispatch.prepare_work (ArrayText.read text fallback) text.size s L D Q hD hL
  have hbank:=build_work P text.toList fallback s hs bits
  rw [Array.length_toList] at hbank
  have hquery:=any_work (query (build P text.toList fallback s hs bits))
      (ResidualDispatch.prepare (ArrayText.read text fallback) text.size s L D Q).windows
      (queryBudget P text.size s) (by
        intro c hc
        have hwin:=ResidualDispatch.prepare_sound (ArrayText.read text fallback) text.size s L D Q c hc
        rw [ShortOuter.full_read] at hwin
        simpa only [Array.length_toList] using query_work P text.toList fallback s hs bits c hwin)
  have hlength:=ResidualDispatch.prepare_windows (ArrayText.read text fallback) text.size s L D Q hD hL
  have hmul:=Nat.mul_le_mul_right (queryBudget P text.size s+3) hlength
  change (ShortOuter.P2.solve P text fallback L).work+
    (ResidualDispatch.prepare (ArrayText.read text fallback) text.size s L D Q).work+
    (build P text.toList fallback s hs bits).work+
    (any (query (build P text.toList fallback s hs bits))
      (ResidualDispatch.prepare (ArrayText.read text fallback) text.size s L D Q).windows).2+text.size+10≤_
  unfold residualBudget
  omega

def Execution.accountedWork (r : Execution) : Nat := r.residualWork+PeriodicAccounting.p2Work r.periodic

theorem execute_accountedWork (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) (hL : 0<L) (hD : 0<D)
    (bits : Inputs P text.toList.length s) :
    (execute P text fallback s L D Q hs bits).accountedWork≤
      residualBudget P text.size s L D Q+(PeriodicAccounting.p2Expr P).eval text.size Q*
        PeriodicAccounting.logHeight text.size := by
  have hr:=execute_residualWork P text fallback s L D Q hs hL hD bits
  have hp:=PeriodicAccounting.p2_bound P (ArrayText.read text fallback) text.size Q
  exact Nat.add_le_add hr hp

end P2
end REWB.ResidualCached
