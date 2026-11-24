import REWB.Core

/-! Operational semantics with a single mutable register. Capturing begins
    without erasing the previous register; closing commits the captured word.
    All open frames receive every emitted character, including recalled words.
    This is the last-closed-capture convention, not a claim about PCRE/Python. -/
namespace REWB

inductive Event (α : Type) where
  | emit : Word α → Event α
  | openCap : Event α
  | closeCap : Event α
  | recall : Event α
  deriving Repr

structure State (α : Type) where
  output : Word α
  stored : Word α
  frames : List (Word α)
  uses : Nat
  deriving Repr

namespace State
variable {α : Type}

def initial (stored : Word α := []) : State α :=
  ⟨[], stored, [], 0⟩

def appendText (s : State α) (w : Word α) : State α :=
  { s with output := s.output ++ w, frames := s.frames.map (fun f => f ++ w) }

def step (s : State α) : Event α → Option (State α)
  | .emit w => some (s.appendText w)
  | .openCap => some { s with frames := [] :: s.frames }
  | .closeCap =>
    match s.frames with
    | [] => none
    | f :: fs => some { s with stored := f, frames := fs }
  | .recall => some { (s.appendText s.stored) with uses := s.uses + 1 }

def execute : State α → List (Event α) → Option (State α)
  | s, [] => some s
  | s, e :: es => (s.step e).bind (fun t => execute t es)

theorem execute_append (s : State α) (xs ys : List (Event α)) :
    execute s (xs ++ ys) = (execute s xs).bind (fun t => execute t ys) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, execute]
    cases h : s.step x with
    | none => simp [h]
    | some t => simpa [h] using ih t

end State

namespace Event
variable {α : Type}

def refCost : Event α → Nat
  | .recall => 1
  | _ => 0

def refCount : List (Event α) → Nat
  | [] => 0
  | e :: es => e.refCost + refCount es

theorem refCount_append (xs ys : List (Event α)) :
    refCount (xs ++ ys) = refCount xs + refCount ys := by
  induction xs with
  | nil => simp [refCount]
  | cons e es ih => simp [refCount, ih, Nat.add_assoc]

end Event

/-- Regular atoms are genuine DFAs. There is only one register. -/
inductive Expr (α : Type) where
  | atom : DFA α → Expr α
  | seq : Expr α → Expr α → Expr α
  | alt : Expr α → Expr α → Expr α
  | star : Expr α → Expr α
  | capture : Expr α → Expr α
  | reference : Expr α

infixr:65 " ⋙ " => Expr.seq

/-- Syntax chooses a finite event trace. Reference words are not guessed here;
    they are emitted by the operational semantics. -/
inductive TraceOf {α : Type} : Expr α → List (Event α) → Prop where
  | atom (d : DFA α) (w : Word α) (h : d.accepts w) :
      TraceOf (.atom d) [.emit w]
  | seq {p q : Expr α} {xs ys : List (Event α)} :
      TraceOf p xs → TraceOf q ys → TraceOf (p ⋙ q) (xs ++ ys)
  | altLeft {p q : Expr α} {xs : List (Event α)} :
      TraceOf p xs → TraceOf (.alt p q) xs
  | altRight {p q : Expr α} {xs : List (Event α)} :
      TraceOf q xs → TraceOf (.alt p q) xs
  | starNil (p : Expr α) : TraceOf (.star p) []
  | starCons {p : Expr α} {xs ys : List (Event α)} :
      TraceOf p xs → TraceOf (.star p) ys → TraceOf (.star p) (xs ++ ys)
  | capture {p : Expr α} {xs : List (Event α)} :
      TraceOf p xs → TraceOf (.capture p) ([.openCap] ++ xs ++ [.closeCap])
  | reference : TraceOf (.reference : Expr α) [.recall]

/-- Existence of a complete trace using at most k dynamic references. -/
def MatchesWithin {α : Type} (p : Expr α) (w : Word α) (k : Nat) : Prop :=
  ∃ es s, TraceOf p es ∧ State.execute (State.initial []) es = some s ∧
    s.frames = [] ∧ s.output = w ∧ s.uses ≤ k

/-- Semantic promise: every successful, balanced execution respects the bound.
    This does not mean the expression has at most k reference syntax nodes. -/
def IsKUse {α : Type} (p : Expr α) (k : Nat) : Prop :=
  ∀ es s, TraceOf p es → State.execute (State.initial []) es = some s →
    s.frames = [] → s.uses ≤ k

theorem matchesWithin_mono {α : Type} {p : Expr α} {w : Word α} {k m : Nat}
    (hkm : k ≤ m) (h : MatchesWithin p w k) : MatchesWithin p w m := by
  rcases h with ⟨es, s, ht, hr, hb, ho, hk⟩
  exact ⟨es, s, ht, hr, hb, ho, Nat.le_trans hk hkm⟩

namespace State
variable {α : Type}

theorem step_uses (s t : State α) (e : Event α) (h : s.step e = some t) :
    t.uses = s.uses + e.refCost := by
  cases e with
  | emit w =>
    simp only [step, Option.some.injEq] at h
    subst t
    simp [appendText, Event.refCost]
  | openCap =>
    simp only [step, Option.some.injEq] at h
    subst t
    simp [Event.refCost]
  | closeCap =>
    cases hf : s.frames with
    | nil => simp [step, hf] at h
    | cons f fs =>
      simp only [step, hf, Option.some.injEq] at h
      subst t
      simp [Event.refCost]
  | recall =>
    simp only [step, Option.some.injEq] at h
    subst t
    simp [appendText, Event.refCost]

theorem execute_uses (es : List (Event α)) (s t : State α)
    (h : execute s es = some t) : t.uses = s.uses + Event.refCount es := by
  induction es generalizing s with
  | nil =>
    simp only [execute, Option.some.injEq] at h
    subst t
    simp [Event.refCount]
  | cons e es ih =>
    cases he : s.step e with
    | none => simp [execute, he] at h
    | some mid =>
      have hr : execute mid es = some t := by simpa [execute, he] using h
      have h1 := step_uses s mid e he
      have h2 := ih mid hr
      simp only [Event.refCount]
      omega

end State
end REWB
