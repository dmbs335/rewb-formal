import REWB.MaskedPeriodicRun

/-! Whole-period and common-suffix maps are read from the same shared
    range index. No rotation or fragment word is rescanned per query.
    The external tail map is immutable run-level input, computed once
    for that tail or obtained from an existing suffix transformation index.
-/
namespace REWB.MaskedPeriodic
open REWB.MaskedFiniteAction.Maps REWB.MaskedCut REWB.MaskedCut.DFAIndex REWB.Spec
variable {α : Type}

structure ContextResult (b c e : DFA α) where
  period : Option (Joint b c e)
  after : Option (Map e.stateCount)
  products : Nat
  visits : Nat

def contexts (b c e : DFA α) (idx : Index.Tree (jointEnum b c e))
    (start eta q : Nat) (tail : Map e.stateCount) : ContextResult b c e :=
  let whole := DyadicIndex.query (ops (jointOps b c e) (jointEnum b c e)) idx start (start+q)
  let fragment := DyadicIndex.query (ops (jointOps b c e) (jointEnum b c e)) idx start (start+eta)
  ⟨whole.answer.map Summary.total,
    fragment.answer.map (fun part=>mul part.total.2.2 tail),
    whole.products+fragment.products,whole.visits+fragment.visits⟩

theorem contexts_value (b c e : DFA α) (w tail : Word α) (start eta q : Nat)
    (he : eta≤q) (hn : start+q≤w.length) :
    (contexts b c e (DFAIndex.build b c e w).1 start eta q (wordMap e tail)).period=
      some (jointWord b c e (slice w start (start+q))) ∧
    (contexts b c e (DFAIndex.build b c e w).1 start eta q (wordMap e tail)).after=
      some (wordMap e (slice w start (start+eta)++tail)) := by
  have hn' : start+q≤(letters b c e w).length := by simpa only [letters_length] using hn
  simp only [contexts,DFAIndex.build]
  rw [Index.range_value (jointOps b c e) (jointEnum b c e) (letters b c e w)
    start (start+q) (by omega) hn',
    Index.range_value (jointOps b c e) (jointEnum b c e) (letters b c e w)
      start (start+eta) (by omega) (by omega)]
  simp only [Option.map,trace_total,letters_slice,letters_product,jointWord,wordMap_append,and_self]

theorem contexts_bounds (b c e : DFA α) (w : Word α) (start eta q : Nat)
    (tail : Map e.stateCount) (he : eta≤q) (hn : start+q≤w.length) :
    (contexts b c e (DFAIndex.build b c e w).1 start eta q tail).products≤2 ∧
    (contexts b c e (DFAIndex.build b c e w).1 start eta q tail).visits≤2*(Nat.log2 w.length+2) := by
  have hn' : start+q≤(letters b c e w).length := by simpa only [letters_length] using hn
  have hw := Index.range_bounds (jointOps b c e) (jointEnum b c e) (letters b c e w)
    start (start+q) (by omega) hn'
  have hf := Index.range_bounds (jointOps b c e) (jointEnum b c e) (letters b c e w)
    start (start+eta) (by omega) (by omega)
  simp only [letters_length] at hw hf
  simp only [contexts,DFAIndex.build]
  constructor <;> omega

end REWB.MaskedPeriodic
