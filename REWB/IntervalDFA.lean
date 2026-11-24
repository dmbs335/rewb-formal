import REWB.MaskScan

/-! All interval states of one DFA. Row l scans the suffix starting at l
    once, starting at the initial state. Query (l,r) reads cell (l,r-l).
    This quadratic-space reference index avoids relying on a yet-unverified
    constant-time linear-space monoid index. -/
namespace REWB.IntervalDFA
open REWB.Spec (slice)
variable {α : Type}

def rows (d : DFA α) : Word α → List (List (Fin d.stateCount))
  | [] => [[d.initial]]
  | c::cs => MaskScan.prefixStates d d.initial (c::cs) :: rows d cs

theorem rows_get (d : DFA α) (w : Word α) (l : Nat) (hl : l ≤ w.length) :
    (rows d w)[l]? = some (MaskScan.prefixStates d d.initial (w.drop l)) := by
  induction w generalizing l with
  | nil =>
    have he : l=0 := by simpa using hl
    subst l
    rfl
  | cons c cs ih =>
    cases l with
    | zero => rfl
    | succ l =>
      have h : l ≤ cs.length := by simpa using hl
      exact ih l h

def build (d : DFA α) (w : Word α) : Array (Array (Fin d.stateCount)) :=
  ((rows d w).map List.toArray).toArray

def lookup (d : DFA α) (idx : Array (Array (Fin d.stateCount))) (l r : Nat) :
    Option (Fin d.stateCount) :=
  (idx[l]?).bind (fun row => row[r-l]?)

theorem lookup_correct (d : DFA α) (w : Word α) (l r : Nat)
    (hl : l≤r) (hr : r≤w.length) :
    lookup d (build d w) l r = some (d.run d.initial (slice w l r)) := by
  have hk : r-l ≤ (w.drop l).length := by rw [List.length_drop]; omega
  unfold lookup build
  simp only [List.getElem?_toArray,List.getElem?_map,rows_get d w l (by omega),
    Option.map,Option.bind,MaskScan.prefixStates_get d (w.drop l) (r-l) hk d.initial,slice]

def stateAt (d : DFA α) (idx : Array (Array (Fin d.stateCount))) (l r : Nat) :
    Fin d.stateCount :=
  (lookup d idx l r).getD d.initial

theorem stateAt_correct (d : DFA α) (w : Word α) (l r : Nat)
    (hl : l≤r) (hr : r≤w.length) :
    stateAt d (build d w) l r = d.run d.initial (slice w l r) := by
  unfold stateAt
  rw [lookup_correct d w l r hl hr]
  rfl

/-- Each prefix scan performs exactly one DFA transition per symbol.
    The count is computed in the same recursive traversal as its row. -/
def countedPrefix (d : DFA α) : Fin d.stateCount → Word α → List (Fin d.stateCount) × Nat
  | q, [] => ([q],0)
  | q, c::cs =>
    let rest := countedPrefix d (d.step q c) cs
    (q::rest.1,rest.2+1)

theorem countedPrefix_spec (d : DFA α) (w : Word α) (q : Fin d.stateCount) :
    countedPrefix d q w = (MaskScan.prefixStates d q w,w.length) := by
  induction w generalizing q with
  | nil => rfl
  | cons c cs ih =>
    change (q::(countedPrefix d (d.step q c) cs).1,
      (countedPrefix d (d.step q c) cs).2+1) = _
    rw [ih]
    rfl

def countedRows (d : DFA α) : Word α → List (List (Fin d.stateCount)) × Nat
  | [] => ([[d.initial]],0)
  | c::cs =>
    let row := countedPrefix d d.initial (c::cs)
    let rest := countedRows d cs
    (row.1::rest.1,row.2+rest.2)

theorem countedRows_correct (d : DFA α) (w : Word α) :
    (countedRows d w).1=rows d w := by
  induction w with
  | nil => rfl
  | cons c cs ih =>
    change (countedPrefix d d.initial (c::cs)).1 :: (countedRows d cs).1 = _
    rw [countedPrefix_spec,ih]
    rfl

/-- Twice the actual transition count is n(n+1). -/
theorem countedRows_cost (d : DFA α) (w : Word α) :
    2*(countedRows d w).2 = w.length*(w.length+1) := by
  induction w with
  | nil => rfl
  | cons c cs ih =>
    change 2*((countedPrefix d d.initial (c::cs)).2+(countedRows d cs).2) =
      (cs.length+1)*(cs.length+1+1)
    rw [countedPrefix_spec]
    change 2*((cs.length+1)+(countedRows d cs).2) = _
    rw [Nat.mul_add,ih]
    simp only [Nat.add_mul,Nat.mul_add,Nat.one_mul,Nat.mul_one]
    omega

def countedBuild (d : DFA α) (w : Word α) :
    Array (Array (Fin d.stateCount)) × Nat :=
  let r := countedRows d w
  ((r.1.map List.toArray).toArray,r.2)

theorem countedBuild_correct (d : DFA α) (w : Word α) :
    (countedBuild d w).1=build d w := by
  change ((countedRows d w).1.map List.toArray).toArray = (rows d w).map List.toArray |>.toArray
  rw [countedRows_correct]

theorem countedBuild_cost (d : DFA α) (w : Word α) :
    2*(countedBuild d w).2 = w.length*(w.length+1) :=
  countedRows_cost d w

end REWB.IntervalDFA
