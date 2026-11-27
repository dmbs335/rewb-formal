import REWB.BoundaryBorderRegularRows

/-! Kernel checks for clipping, noninjective transitions, zero-count
point handling, and the full text-built regular border query. Physical
witnesses are checked on slices; large index values are not evaluated
inside kernel proofs. -/
namespace REWB.BoundaryBorder.Regular.Regression
open REWB.Spec

theorem clipped_alignment :
    (align 1 3 5 12).1=some (7,1) ∧
    (align 1 3 11 12).1=none ∧
    (align 4 0 0 12).1=none := by decide

def allWords : DFA (Fin 2) := ⟨1,0,fun _ _=>0,fun _=>true⟩
def epsilon : DFA (Fin 2) := ⟨2,0,fun _ _=>1,fun q=>decide (q=0)⟩
def alternating : Word (Fin 2) := [0,1,0,1,0,1,0,1]

theorem product_noninjective :
    (productStep (Vector.ofFn (fun _ : Fin 2=>1)) (Vector.ofFn (fun _ : Fin 2=>0))).get 0=2 ∧
    (productStep (Vector.ofFn (fun _ : Fin 2=>1)) (Vector.ofFn (fun _ : Fin 2=>0))).get 3=2 := by
  decide

theorem zero_count_point (A B E : DFA (Fin 2)) (w : Word (Fin 2)) (p a j r : Nat) :
    (query A B E (BoundaryApplication.Range.build A w) (BoundaryApplication.Range.build B w)
      (BoundaryApplication.Range.build E w) p 0 0 a j r).1=
    (point A B E (BoundaryApplication.Range.build A w) (BoundaryApplication.Range.build B w)
      (BoundaryApplication.Range.build E w) p a j r).1 := by
  simp only [query,if_pos rfl]
  rfl

/-- The capture ends strictly inside a shared periodic suffix. A and E
require epsilon, selecting source zero and the exact target end. -/
theorem strict_partial_accept :
    (dyadic epsilon allWords epsilon (WindowIndex.prepare alternating.toArray 0)
      (BoundaryApplication.Range.build epsilon alternating)
      (BoundaryApplication.Range.build allWords alternating)
      (BoundaryApplication.Range.build epsilon alternating) 3 4 7).1=true := by
  apply (dyadic_correct epsilon allWords epsilon alternating 0 3 4 7 (by decide) (by decide)).mpr
  refine ⟨0,by decide,by decide,by decide,?_,?_,?_⟩
  all_goals unfold DFA.accepts; decide

/-- Right-end clipping removes the only A-accepted start; it cannot be
reintroduced by AP alignment or epsilon acceptance in a later slice. -/
theorem right_clipped_reject :
    (dyadic epsilon allWords epsilon (WindowIndex.prepare alternating.toArray 0)
      (BoundaryApplication.Range.build epsilon alternating)
      (BoundaryApplication.Range.build allWords alternating)
      (BoundaryApplication.Range.build epsilon alternating) 3 4 6).1=false := by
  cases hv : (dyadic epsilon allWords epsilon (WindowIndex.prepare alternating.toArray 0)
      (BoundaryApplication.Range.build epsilon alternating)
      (BoundaryApplication.Range.build allWords alternating)
      (BoundaryApplication.Range.build epsilon alternating) 3 4 6).1 with
  | false => rfl
  | true =>
    obtain ⟨p,hp,hr,he,hpred⟩:=
      (dyadic_correct epsilon allWords epsilon alternating 0 3 4 6 (by decide) (by decide)).mp hv
    have hn : ∀p : Fin 3,¬(endAt 4 3 p.val≤6 ∧
        Predicate epsilon allWords epsilon alternating p.val 3 4 6) := by
      unfold Predicate DFA.accepts
      decide
    exact False.elim (hn ⟨p,hp⟩ ⟨hr,hpred⟩)

theorem empty_positive (A B E : DFA (Fin 2)) :
    (dyadic A B E (WindowIndex.prepare (#[] : Array (Fin 2)) 0)
      (BoundaryApplication.Range.build A []) (BoundaryApplication.Range.build B [])
      (BoundaryApplication.Range.build E []) 0 0 0).1=false := by
  cases hv : (dyadic A B E (WindowIndex.prepare (#[] : Array (Fin 2)) 0)
      (BoundaryApplication.Range.build A []) (BoundaryApplication.Range.build B [])
      (BoundaryApplication.Range.build E []) 0 0 0).1 with
  | false => rfl
  | true =>
    obtain ⟨p,hp,_⟩:=(dyadic_correct A B E [] 0 0 0 0 (by decide) (by decide)).mp hv
    omega

end REWB.BoundaryBorder.Regular.Regression
