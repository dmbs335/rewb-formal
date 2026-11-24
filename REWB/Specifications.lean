import REWB.Reductions
import REWB.Cost

/-! Explicit targets, not asserted facts. These specifications are intentionally
    not introduced as axioms. The main complexity goal needs a concrete
    deterministic word-RAM implementation and an independently verified cost
    semantics, not just an unconstrained function returning a cost. -/
namespace REWB.Spec
open REWB
variable {α : Type}

def slice (w : Word α) (l r : Nat) : Word α := (w.drop l).take (r - l)

/-- One-use substring query with all boundaries explicit. -/
def oneUseRange (A B C E : DFA α) (w : Word α) (l r : Nat) : Prop :=
  l ≤ r ∧ r ≤ w.length ∧
  ∃ i a j t : Nat,
    l ≤ i ∧ i ≤ a ∧ a ≤ j ∧ j ≤ t ∧ t ≤ r ∧
    slice w i a = slice w j t ∧
    A.accepts (slice w l i) ∧ B.accepts (slice w i a) ∧
    C.accepts (slice w a j) ∧ E.accepts (slice w t r)

/-- Boundary-aware one-use query. The first copy can start before l, or
    cross l; only the split p and the second copy must be inside [l,r]. -/
def boundaryRange (A B C K D E : DFA α) (w : Word α) (l r : Nat) : Prop :=
  l ≤ r ∧ r ≤ w.length ∧
  ∃ i a p j t : Nat,
    i ≤ a ∧ a ≤ p ∧ p ≤ j ∧ j ≤ t ∧ t ≤ r ∧ l ≤ p ∧
    slice w i a = slice w j t ∧
    A.accepts (slice w 0 i) ∧ B.accepts (slice w i a) ∧
    C.accepts (slice w a p) ∧ K.accepts (slice w l p) ∧
    D.accepts (slice w p j) ∧ E.accepts (slice w t r)

/-- Masked all-start output contract. `mask` is arbitrary, not periodic. -/
def maskedStart (B C E : DFA α) (w : Word α) (mask : Nat → Bool) (s : Nat) : Prop :=
  ∃ a j t : Nat,
    s ≤ a ∧ a ≤ j ∧ j ≤ t ∧ t ≤ w.length ∧ mask j = true ∧
    slice w s a = slice w j t ∧ B.accepts (slice w s a) ∧
    C.accepts (slice w a j) ∧ E.accepts (slice w t w.length)

/-- Semantic correctness only, no computational-model claim. -/
def CorrectMatcher (p : Expr α) (matchWord : Word α → Bool) : Prop :=
  ∀ w, matchWord w = true ↔ MatchesWithin p w 2

/-- Functional normal-form compilation obligation, independent of costs.
    The remaining compiler must cover zero and one use as well as both uses. -/
def IsNormalization (p : Expr α) (pieces : List (Expr α)) : Prop :=
  ∀ w, MatchesWithin p w 2 ↔ ∃ q ∈ pieces, MatchesWithin q w 2

/-- Numeric target for a cost function *already* derived from a concrete
    machine execution. Taking the thirteenth power avoids real exponents.
    No theorem asserting this target for an REWB matcher is provided here. -/
def Target25Over13 (cost : Nat → Nat) : Prop :=
  ∃ C d : Nat, 0 < C ∧ ∀ n,
    (cost n)^13 ≤ C * (n+2)^25 * (Nat.log2 (n+2) + 1)^d

end REWB.Spec
