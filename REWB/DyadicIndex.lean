import REWB.RangeProducts

/-! General, noncommutative range products via a dyadic cut hierarchy.
    The counters are attached to the executable construction and query.
    The query uses at most one monoid multiplication and traverses one path.
    This is not yet the flat direct-addressed disjoint sparse table. -/
namespace REWB.DyadicIndex
open REWB.RangeProducts
open REWB.Spec (slice)

variable {M : Type}

inductive Tree (M : Type) where
  | leaf : List M → Tree M
  | node : CutIndex M → Tree M → Tree M → Tree M

def build (o : Ops M) : Nat → List M → Tree M × Nat
  | 0, xs => (.leaf xs, 0)
  | h+1, xs =>
    let left := xs.take (2^h)
    let right := xs.drop (2^h)
    let row := buildCut o left right
    let a := build o h left
    let b := build o h right
    (.node row.1 a.1 b.1, row.2 + a.2 + b.2)

structure Result (M : Type) where
  answer : Option M
  products : Nat
  visits : Nat

def Result.bump (x : Result M) : Result M :=
  { x with visits := x.visits + 1 }

def query (o : Ops M) : Tree M → Nat → Nat → Result M
  | .leaf xs, l, r =>
    let v := slice xs l r
    ⟨some (product o v), v.length, 1⟩
  | .node row a b, l, r =>
    if r ≤ row.cut then
      (query o a l r).bump
    else if row.cut ≤ l then
      (query o b (l-row.cut) (r-row.cut)).bump
    else
      ⟨queryCut o row l r, 1, 1⟩

private theorem lengths (xs : List M) (k : Nat) :
    (xs.take k).length + (xs.drop k).length = xs.length := by
  rw [List.length_take, List.length_drop]
  omega

theorem build_cost (o : Ops M) (h : Nat) (xs : List M) :
    (build o h xs).2 = h * xs.length := by
  induction h generalizing xs with
  | zero => simp only [build,Nat.zero_mul]
  | succ h ih =>
    change (buildCut o (xs.take (2^h)) (xs.drop (2^h))).2 +
      (build o h (xs.take (2^h))).2 + (build o h (xs.drop (2^h))).2 =
        (h+1)*xs.length
    rw [cut_cost, ih, ih, Nat.add_assoc, ← Nat.mul_add, lengths,
      Nat.add_mul, Nat.one_mul]
    omega

def storedCells : Tree M → Nat
  | .leaf xs => xs.length
  | .node row a b =>
    row.leftSuffix.size + row.rightPrefix.size + storedCells a + storedCells b

/-- Storage counts actual stored monoid cells, including the empty cells
    of both rows at each split. Node metadata is not included. -/
theorem build_cells (o : Ops M) (h : Nat) (xs : List M) :
    storedCells (build o h xs).1 + 2 = (h+1)*xs.length + 2^(h+1) := by
  induction h generalizing xs with
  | zero =>
    change xs.length + 2 = (0+1)*xs.length + 2^(0+1)
    simp
  | succ h ih =>
    let l := xs.take (2^h)
    let r := xs.drop (2^h)
    have hs : l.length+r.length=xs.length := lengths xs _
    have ha := ih l
    have hb := ih r
    change (buildCut o l r).1.leftSuffix.size +
      (buildCut o l r).1.rightPrefix.size +
      storedCells (build o h l).1 + storedCells (build o h r).1 + 2 =
      (h+1+1)*xs.length + 2^(h+1+1)
    rw [cut_words,hs,Nat.add_mul,Nat.one_mul,Nat.pow_succ]
    have hm : (h+1)*l.length + (h+1)*r.length = (h+1)*xs.length := by
      rw [← Nat.mul_add,hs]
    omega

private theorem take_left (x y : List M) (k : Nat) (hk : k ≤ x.length) :
    (x ++ y).take k = x.take k := by
  induction x generalizing k with
  | nil =>
    have h : k=0 := by simpa using hk
    subst k
    rfl
  | cons c cs ih =>
    cases k with
    | zero => rfl
    | succ k =>
      have h : k ≤ cs.length := by simpa using hk
      change c :: (cs ++ y).take k = c :: cs.take k
      rw [ih k h]

private theorem drop_left (x y : List M) (k : Nat) (hk : k ≤ x.length) :
    (x ++ y).drop k = x.drop k ++ y := by
  induction x generalizing k with
  | nil =>
    have h : k=0 := by simpa using hk
    subst k
    rfl
  | cons c cs ih =>
    cases k with
    | zero => rfl
    | succ k =>
      have h : k ≤ cs.length := by simpa using hk
      exact ih k h

private theorem drop_past (x y : List M) (k : Nat) :
    (x ++ y).drop (x.length+k) = y.drop k := by
  induction x with
  | nil => simp only [List.nil_append,List.length_nil,Nat.zero_add]
  | cons c cs ih =>
    change (c :: (cs ++ y)).drop (cs.length+1+k) = y.drop k
    have h : cs.length+1+k = (cs.length+k)+1 := by omega
    rw [h]
    exact ih

theorem slice_left (x y : List M) (l r : Nat) (hl : l ≤ r) (hr : r ≤ x.length) :
    slice (x++y) l r = slice x l r := by
  unfold slice
  rw [drop_left x y l (by omega)]
  apply take_left
  rw [List.length_drop]
  omega

theorem slice_right (x y : List M) (l r : Nat) (hl : x.length ≤ l) (hr : l ≤ r) :
    slice (x++y) l r = slice y (l-x.length) (r-x.length) := by
  unfold slice
  have he : l=x.length+(l-x.length) := by omega
  have hdrop : (x++y).drop l = y.drop (l-x.length) := by
    calc
      (x++y).drop l = (x++y).drop (x.length+(l-x.length)) :=
        congrArg (fun k => (x++y).drop k) he
      _ = _ := drop_past x y _
  rw [hdrop,show r-x.length-(l-x.length)=r-l by omega]

theorem query_correct (o : Ops M) (h : Nat) (xs : List M) (l r : Nat)
    (hl : l ≤ r) (hr : r ≤ xs.length) :
    (query o (build o h xs).1 l r).answer = some (product o (slice xs l r)) := by
  induction h generalizing xs l r with
  | zero => rfl
  | succ h ih =>
    let x := xs.take (2^h)
    let y := xs.drop (2^h)
    have hjoin : x++y=xs := List.take_append_drop _ _
    have hlen : x.length+y.length=xs.length := lengths xs _
    change (query o (.node (buildCut o x y).1
      (build o h x).1 (build o h y).1) l r).answer = _
    simp only [query]
    change (if r ≤ x.length then (query o (build o h x).1 l r).bump
      else if x.length ≤ l then
        (query o (build o h y).1 (l-x.length) (r-x.length)).bump
      else ⟨queryCut o (buildCut o x y).1 l r,1,1⟩).answer = _
    by_cases hx : r ≤ x.length
    · rw [if_pos hx]
      change (query o (build o h x).1 l r).answer = _
      rw [ih x l r hl hx]
      exact congrArg (fun z => some (product o z))
        ((slice_left x y l r hl hx).symm.trans (congrArg (fun z => slice z l r) hjoin))
    · rw [if_neg hx]
      by_cases hy : x.length ≤ l
      · rw [if_pos hy]
        change (query o (build o h y).1 (l-x.length) (r-x.length)).answer = _
        rw [ih y _ _ (by omega) (by omega)]
        exact congrArg (fun z => some (product o z))
          ((slice_right x y l r hy hl).symm.trans (congrArg (fun z => slice z l r) hjoin))
      · rw [if_neg hy]
        change queryCut o (buildCut o x y).1 l r = _
        rw [queryCut_correct o x y l r (by omega) (by omega) (by omega),hjoin]

theorem query_bounds (o : Ops M) (h : Nat) (xs : List M) (l r : Nat)
    (hcap : xs.length ≤ 2^h) (hl : l ≤ r) (hr : r ≤ xs.length) :
    (query o (build o h xs).1 l r).products ≤ 1 ∧
      (query o (build o h xs).1 l r).visits ≤ h+1 := by
  induction h generalizing xs l r with
  | zero =>
    change (slice xs l r).length ≤ 1 ∧ 1 ≤ 0+1
    have hs := OuterColumn.slice_length xs l r hl hr
    simp only [Nat.pow_zero] at hcap
    omega
  | succ h ih =>
    let x := xs.take (2^h)
    let y := xs.drop (2^h)
    have hlen : x.length+y.length=xs.length := lengths xs _
    have hcx : x.length ≤ 2^h := by
      dsimp [x]
      rw [List.length_take]
      omega
    have hcy : y.length ≤ 2^h := by
      dsimp [y]
      rw [List.length_drop]
      rw [Nat.pow_succ] at hcap
      omega
    change (query o (.node (buildCut o x y).1
      (build o h x).1 (build o h y).1) l r).products ≤ 1 ∧
      (query o (.node (buildCut o x y).1
      (build o h x).1 (build o h y).1) l r).visits ≤ h+1+1
    simp only [query]
    change (if r ≤ x.length then (query o (build o h x).1 l r).bump
      else if x.length ≤ l then
        (query o (build o h y).1 (l-x.length) (r-x.length)).bump
      else ⟨queryCut o (buildCut o x y).1 l r,1,1⟩).products ≤ 1 ∧
      (if r ≤ x.length then (query o (build o h x).1 l r).bump
      else if x.length ≤ l then
        (query o (build o h y).1 (l-x.length) (r-x.length)).bump
      else ⟨queryCut o (buildCut o x y).1 l r,1,1⟩).visits ≤ h+1+1
    by_cases hx : r ≤ x.length
    · simp only [hx,if_true,Result.bump]
      have hh := ih x l r hcx hl hx
      exact ⟨hh.1,by omega⟩
    · simp only [hx,if_false]
      by_cases hy : x.length ≤ l
      · simp only [hy,if_true,Result.bump]
        have hh := ih y (l-x.length) (r-x.length) hcy (by omega) (by omega)
        exact ⟨hh.1,by omega⟩
      · simp only [hy,if_false]
        omega

def heightFor (n : Nat) : Nat := Nat.log2 n + 1

theorem capacity (n : Nat) : n ≤ 2^(heightFor n) := by
  unfold heightFor
  exact Nat.le_of_lt (Nat.lt_log2_self (n := n))

def buildFor (o : Ops M) (xs : List M) : Tree M × Nat :=
  build o (heightFor xs.length) xs

theorem buildFor_cost (o : Ops M) (xs : List M) :
    (buildFor o xs).2 = (Nat.log2 xs.length+1)*xs.length :=
  build_cost o _ xs

theorem queryFor_spec (o : Ops M) (xs : List M) (l r : Nat)
    (hl : l ≤ r) (hr : r ≤ xs.length) :
    (query o (buildFor o xs).1 l r).answer = some (product o (slice xs l r)) ∧
    (query o (buildFor o xs).1 l r).products ≤ 1 ∧
    (query o (buildFor o xs).1 l r).visits ≤ Nat.log2 xs.length+2 := by
  exact ⟨query_correct o _ xs l r hl hr,
    query_bounds o _ xs l r (capacity xs.length) hl hr⟩

end REWB.DyadicIndex
