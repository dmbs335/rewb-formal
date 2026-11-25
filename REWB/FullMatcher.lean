import REWB.CompleteNormalization
import REWB.BlockMatcher

/-! A complete executable matcher for an arbitrary source expression,
    under the at-most-two-executed-references semantics. Pattern
    preprocessing constructs the concrete finite list of normal forms.
    The nested cases use the verified blocked matchers; the remaining
    cases use direct DFA acceptance or exact split enumeration.

    This closes the full semantic pipeline from the original expression
    to a Boolean decision. It makes no subquadratic running-time claim. -/
namespace REWB.FullMatcher
open REWB.CompleteNormalization (Form)
variable {α : Type}

/-- Exact one-reference matcher, including an empty captured word. -/
def once [DecidableEq α] (A B C E : DFA α) (w : Word α) : Bool :=
  Reference.consume A w fun r0=>
  Reference.choose B r0 fun u r1=>
  Reference.consume C r1 fun r2=>
  Reference.copy u r2 (Reference.acceptB E)

theorem once_correct [DecidableEq α] (A B C E : DFA α) (w : Word α) :
    once A B C E w=true ↔ MatchesWithin (CompleteNormalization.once A B C E) w 2 := by
  rw [CompleteNormalization.once_matches]
  simp only [once,Reference.consume_iff,Reference.choose_iff,Reference.copy_iff,
    Reference.acceptB_iff,List.append_assoc]
  constructor
  · rintro ⟨a,r0,h0,ha,u,r1,h1,hu,c,r2,h2,hc,e,h3,he⟩
    exact ⟨a,u,c,e,ha,hu,hc,he,by rw [h0,h1,h2,h3]⟩
  · rintro ⟨a,u,c,e,ha,hu,hc,he,rfl⟩
    exact ⟨a,_,rfl,ha,u,_,rfl,hu,c,_,rfl,hc,e,rfl,he⟩

/-- All six constructors produced by the normalizer have an executable
    decision. No externally supplied mask, equality oracle, or factor
    decomposition is an input to this dispatcher. -/
def form [DecidableEq α] : Form α→Word α→Bool
  | .regular A,w => Reference.acceptB A w
  | .once A B C E,w => once A B C E w
  | .sameValue P,w => Reference.same P w
  | .independent P,w => Reference.independent P w
  | .nested1 P,w => BlockMatcher.match1 P w
  | .nested2 P,w => BlockMatcher.match2 P w

theorem form_correct [DecidableEq α] (F : Form α) (w : Word α) :
    form F w=true ↔ MatchesWithin F.expr w 2 := by
  cases F with
  | regular A =>
    exact (Reference.acceptB_iff A w).trans (CompleteNormalization.atom_matches A w).symm
  | once A B C E => exact once_correct A B C E w
  | sameValue P => exact Reference.same_correct P w
  | independent P => exact Reference.independent_correct P w
  | nested1 P => exact BlockMatcher.match1_correct P w
  | nested2 P => exact BlockMatcher.match2_correct P w

/-- The compiled value can be retained and reused for multiple words. -/
abbrev Compiled (α : Type) := List (Form α)

def compile (p : Expr α) : Compiled α := CompleteNormalization.forms p

def run [DecidableEq α] (compiled : Compiled α) (w : Word α) : Bool :=
  compiled.any (fun F=>form F w)

theorem run_correct [DecidableEq α] (compiled : Compiled α) (w : Word α) :
    run compiled w=true ↔ ∃ F∈compiled,MatchesWithin F.expr w 2 := by
  simp only [run,List.any_eq_true,form_correct]

/-- Pattern compilation followed by the concrete normal-form matchers
    is exact for every original expression and every input word. -/
theorem compile_correct [DecidableEq α] (p : Expr α) :
    Spec.CorrectMatcher p (run (compile p)) := by
  intro w
  rw [run_correct]
  exact (CompleteNormalization.forms_correct p w).symm

def matchWord [DecidableEq α] (p : Expr α) (w : Word α) : Bool :=
  run (compile p) w

theorem matchWord_correct [DecidableEq α] (p : Expr α) (w : Word α) :
    matchWord p w=true ↔ MatchesWithin p w 2 := compile_correct p w

/-- The original correctness contract has an actual executable witness. -/
theorem correctMatcher [DecidableEq α] (p : Expr α) :
    Spec.CorrectMatcher p (matchWord p) := compile_correct p

/-- A constructive decision procedure, without installing a global
    instance or changing the operational definition of matching. -/
def decideMatches [DecidableEq α] (p : Expr α) (w : Word α) :
    Decidable (MatchesWithin p w 2) :=
  if h : matchWord p w=true then
    .isTrue ((matchWord_correct p w).mp h)
  else
    .isFalse (fun hm=>h ((matchWord_correct p w).mpr hm))

end REWB.FullMatcher
