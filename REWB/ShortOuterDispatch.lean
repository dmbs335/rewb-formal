import REWB.ShortOuterP1
import REWB.ShortOuterP2

/-! The indexed residual dispatch now has an actual executable short
outer branch.  The remaining scheduled boundary/one-use predicates keep
their existing exact interfaces; this file does not invent their rows. -/
namespace REWB.ShortOuter
open REWB.Periodic
variable {σ : Nat}

theorem p1_dispatch_iff (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) (hSL : s≤L) (hD : 0<D) (hQL : Q≤L) :
    MatchesWithin P.nested1 text.toList 2 ↔
      (CountedP1Cubic.solve P (ArrayText.read text fallback) text.size Q).answer=true ∨
      (P1.solve P text fallback L).answer=true ∨
      ∃c,c∈(ResidualDispatch.prepare (ArrayText.read text fallback) text.size s L D Q).windows ∧
        ResidualDispatch.P1Query P text.toList c := by
  have h:=ResidualDispatch.p1_dispatch_iff P (ArrayText.read text fallback) text.size s L D Q hs hSL hD hQL
  rw [full_read,←P1.solve_correct P text fallback L] at h
  exact h

theorem p2_dispatch_iff (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (s L D Q : Nat) (hs : 0<s) (hSL : s≤L) (hD : 0<D) (hQL : Q≤L) :
    MatchesWithin P.nested2 text.toList 2 ↔
      (SmallPeriodP2.solve P (ArrayText.read text fallback) text.size Q).accepted=true ∨
      (P2.solve P text fallback L).answer=true ∨
      ∃c,c∈(ResidualDispatch.prepare (ArrayText.read text fallback) text.size s L D Q).windows ∧
        ResidualDispatch.P2Query P text.toList c := by
  have h:=ResidualDispatch.p2_dispatch_iff P (ArrayText.read text fallback) text.size s L D Q hs hSL hD hQL
  rw [full_read,←P2.solve_correct P text fallback L] at h
  exact h

end REWB.ShortOuter
