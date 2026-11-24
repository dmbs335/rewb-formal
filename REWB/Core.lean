import Lean

/-! A finite-state model, with the alphabet supplied as a type. The complexity
    target instantiates it with `Fin σ` for a fixed positive σ. -/
namespace REWB

abbrev Word (α : Type) := List α
abbrev Language (α : Type) := Word α → Prop

structure DFA (α : Type) where
  stateCount : Nat
  initial : Fin stateCount
  step : Fin stateCount → α → Fin stateCount
  final : Fin stateCount → Bool

namespace DFA

variable {α : Type}

def run (d : DFA α) : Fin d.stateCount → Word α → Fin d.stateCount
  | q, [] => q
  | q, c :: cs => run d (d.step q c) cs

def accepts (d : DFA α) (w : Word α) : Prop :=
  d.final (d.run d.initial w) = true

def transition (d : DFA α) (w : Word α) : Fin d.stateCount → Fin d.stateCount :=
  fun q => d.run q w

theorem run_append (d : DFA α) (q : Fin d.stateCount) (x y : Word α) :
    d.run q (x ++ y) = d.run (d.run q x) y := by
  induction x generalizing q with
  | nil => rfl
  | cons c cs ih =>
    exact ih (d.step q c)

theorem transition_append (d : DFA α) (x y : Word α) :
    d.transition (x ++ y) = fun q => d.transition y (d.transition x q) := by
  funext q
  exact d.run_append q x y

theorem run_append_three (d : DFA α) (q : Fin d.stateCount) (x y z : Word α) :
    d.run q (x ++ y ++ z) = d.run (d.run (d.run q x) y) z := by
  simp only [run_append]

/-- Preimage, not an inverse function: arbitrary noninjective DFA transitions
    are allowed. -/
def preimage (d : DFA α) (w : Word α) (Q : Fin d.stateCount → Prop) :
    Fin d.stateCount → Prop := fun q => Q (d.run q w)

theorem preimage_append (d : DFA α) (x y : Word α)
    (Q : Fin d.stateCount → Prop) (q : Fin d.stateCount) :
    d.preimage (x ++ y) Q q ↔ d.preimage x (d.preimage y Q) q := by
  simp only [preimage, run_append]

end DFA
end REWB
