import REWB.ResidualActualForms
import REWB.ResidualActualIndependent

/-! Complete actual dispatch for all six constructors produced by the
fixed-pattern normalizer. Nested cases build their own all-start rows;
same-value and once cases use proved fixed-pattern reductions; independent
captures use two all-start rows and a linear regular-gap join.

The Boolean correctness theorem is unconditional. Numeric fields preserve
the existing accounted-work scope. Pattern normalization is reusable
fixed-pattern preprocessing, separate from these text-work counters. -/
namespace REWB.ResidualActual.Matcher
open REWB.CompleteNormalization (Form)
variable {σ : Nat}

structure Execution where
  answer : Bool
  accountedWork : Nat
  fixedPatternBuilds : Nat

def form : Form (Fin σ)→Array (Fin σ)→Fin σ→Execution
  | .regular A,text,_ =>
    ⟨A.final (A.run A.initial text.toList),3*text.size+5,0⟩
  | .once A B C E,text,fallback =>
    let out:=ResidualActual.once A B C E text fallback
    ⟨out.answer,out.accountedWork+3,out.fixedPatternBuilds⟩
  | .sameValue P,text,fallback =>
    let out:=ResidualActual.same P text fallback
    ⟨out.answer,out.accountedWork+3,out.fixedPatternBuilds⟩
  | .independent P,text,fallback =>
    let out:=Independent.execute P text fallback
    ⟨out.answer,out.accountedWork+3,out.fixedPatternBuilds⟩
  | .nested1 P,text,fallback =>
    let out:=P1.auto P text fallback
    ⟨out.answer,out.accountedWork+3,out.fixedPatternBuilds⟩
  | .nested2 P,text,fallback =>
    let out:=P2.auto P text fallback
    ⟨out.answer,out.accountedWork+3,out.fixedPatternBuilds⟩

theorem form_correct (F : Form (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) :
    (form F text fallback).answer=true ↔ MatchesWithin F.expr text.toList 2 := by
  cases F with
  | regular A => exact (CompleteNormalization.atom_matches A text.toList).symm
  | once A B C E => exact ResidualActual.once_correct A B C E text fallback
  | sameValue P => exact ResidualActual.same_correct P text fallback
  | independent P => exact Independent.execute_correct P text fallback
  | nested1 P => exact P1.auto_correct P text fallback
  | nested2 P => exact P2.auto_correct P text fallback

abbrev Compiled (σ : Nat) := List (Form (Fin σ))

def compile (p : Expr (Fin σ)) : Compiled σ := CompleteNormalization.forms p

def run (compiled : Compiled σ) (text : Array (Fin σ)) (fallback : Fin σ) : Execution :=
  match compiled with
  | [] => ⟨false,1,0⟩
  | F::rest =>
    let one:=form F text fallback
    let tail:=run rest text fallback
    ⟨one.answer || tail.answer,one.accountedWork+tail.accountedWork+3,
      one.fixedPatternBuilds+tail.fixedPatternBuilds⟩

theorem run_correct (compiled : Compiled σ) (text : Array (Fin σ)) (fallback : Fin σ) :
    (run compiled text fallback).answer=true ↔ ∃F,F∈compiled ∧ MatchesWithin F.expr text.toList 2 := by
  induction compiled with
  | nil => simp [run]
  | cons F rest ih => simp only [run,Bool.or_eq_true,form_correct,ih,List.mem_cons,exists_eq_or_imp]

theorem run_work (compiled : Compiled σ) (text : Array (Fin σ)) (fallback : Fin σ) :
    (run compiled text fallback).accountedWork=
      (compiled.map fun F=>(form F text fallback).accountedWork+3).sum+1 := by
  induction compiled with
  | nil => rfl
  | cons F rest ih =>
    simp only [run,List.map_cons,List.sum_cons,ih]
    omega

theorem run_builds (compiled : Compiled σ) (text : Array (Fin σ)) (fallback : Fin σ) :
    (run compiled text fallback).fixedPatternBuilds=
      (compiled.map fun F=>(form F text fallback).fixedPatternBuilds).sum := by
  induction compiled with
  | nil => rfl
  | cons F rest ih => simp only [run,List.map_cons,List.sum_cons,ih]

def solve (p : Expr (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) : Execution :=
  run (compile p) text fallback

theorem solve_correct (p : Expr (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) :
    (solve p text fallback).answer=true ↔ MatchesWithin p text.toList 2 := by
  rw [solve,run_correct]
  exact (CompleteNormalization.forms_correct p text.toList).symm

def matchWord (p : Expr (Fin σ)) (fallback : Fin σ) (w : Word (Fin σ)) : Bool :=
  (solve p w.toArray fallback).answer

theorem matchWord_correct (p : Expr (Fin σ)) (fallback : Fin σ) (w : Word (Fin σ)) :
    matchWord p fallback w=true ↔ MatchesWithin p w 2 := by
  simpa only [matchWord,List.toList_toArray] using solve_correct p w.toArray fallback

/-- An executable witness using the actual accelerated dispatch for every
normal-form constructor, including empty captures and zero-reference paths. -/
theorem correctMatcher (p : Expr (Fin σ)) (fallback : Fin σ) :
    Spec.CorrectMatcher p (matchWord p fallback) := matchWord_correct p fallback

end REWB.ResidualActual.Matcher
