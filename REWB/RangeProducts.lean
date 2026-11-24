import REWB.NestedColumns

/-! Executable noncommutative range products. The counters count monoid
    multiplications in the actual row-building functions; they do not
    silently equate arbitrary Lean evaluation with word-RAM cost. -/
namespace REWB.RangeProducts

structure Ops (M : Type) where
  one : M
  mul : M → M → M
  one_mul : ∀ a, mul one a = a
  mul_one : ∀ a, mul a one = a
  assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)

variable {M : Type}

def product (o : Ops M) : List M → M
  | [] => o.one
  | x :: xs => o.mul x (product o xs)

theorem product_append (o : Ops M) (x y : List M) :
    product o (x ++ y) = o.mul (product o x) (product o y) := by
  induction x with
  | nil => simp only [List.nil_append,product,o.one_mul]
  | cons a xs ih =>
    change o.mul a (product o (xs ++ y)) =
      o.mul (o.mul a (product o xs)) (product o y)
    rw [ih,o.assoc]

/-- Prefix row, with explicit number of monoid products. -/
def prefixScan (o : Ops M) (acc : M) : List M → List M × Nat
  | [] => ([acc],0)
  | x :: xs =>
    let tail := prefixScan o (o.mul acc x) xs
    (acc :: tail.1,tail.2+1)

/-- Suffix row, full product, and explicit number of monoid products. -/
def suffixScan (o : Ops M) : List M → M × List M × Nat
  | [] => (o.one,[o.one],0)
  | x :: xs =>
    let tail := suffixScan o xs
    let p := o.mul x tail.1
    (p,p :: tail.2.1,tail.2.2+1)

theorem prefix_cost (o : Ops M) (acc : M) (xs : List M) :
    (prefixScan o acc xs).2 = xs.length := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    change (prefixScan o (o.mul acc x) xs).2+1 = xs.length+1
    rw [ih]

theorem suffix_cost (o : Ops M) (xs : List M) :
    (suffixScan o xs).2.2 = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (suffixScan o xs).2.2+1 = xs.length+1
    rw [ih]

theorem prefix_size (o : Ops M) (acc : M) (xs : List M) :
    (prefixScan o acc xs).1.length = xs.length+1 := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    change (prefixScan o (o.mul acc x) xs).1.length+1 = xs.length+1+1
    rw [ih]

theorem suffix_size (o : Ops M) (xs : List M) :
    (suffixScan o xs).2.1.length = xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (suffixScan o xs).2.1.length+1 = xs.length+1+1
    rw [ih]

theorem suffix_product (o : Ops M) (xs : List M) :
    (suffixScan o xs).1 = product o xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change o.mul x (suffixScan o xs).1 = o.mul x (product o xs)
    rw [ih]

theorem prefix_get (o : Ops M) (acc : M) (xs : List M) (i : Nat)
    (hi : i ≤ xs.length) :
    (prefixScan o acc xs).1[i]? = some (o.mul acc (product o (xs.take i))) := by
  induction xs generalizing acc i with
  | nil =>
    have h : i=0 := by simpa using hi
    subst i
    simp [prefixScan, product, o.mul_one]
  | cons x xs ih =>
    cases i with
    | zero => simp [prefixScan,product,o.mul_one]
    | succ i =>
      have h : i ≤ xs.length := by simpa using hi
      change (prefixScan o (o.mul acc x) xs).1[i]? =
        some (o.mul acc (o.mul x (product o (xs.take i))))
      rw [ih _ _ h,o.assoc]

theorem suffix_get (o : Ops M) (xs : List M) (i : Nat)
    (hi : i ≤ xs.length) :
    (suffixScan o xs).2.1[i]? = some (product o (xs.drop i)) := by
  induction xs generalizing i with
  | nil =>
    have h : i=0 := by simpa using hi
    subst i
    rfl
  | cons x xs ih =>
    cases i with
    | zero =>
      change some (o.mul x (suffixScan o xs).1) =
        some (o.mul x (product o xs))
      rw [suffix_product]
    | succ i =>
      have h : i ≤ xs.length := by simpa using hi
      exact ih i h

structure CutIndex (M : Type) where
  cut : Nat
  len : Nat
  leftSuffix : Array M
  rightPrefix : Array M

/-- Build exactly one suffix and one prefix row. No quadratic table. -/
def buildCut (o : Ops M) (left right : List M) : CutIndex M × Nat :=
  let ls := suffixScan o left
  let rs := prefixScan o o.one right
  (⟨left.length,left.length+right.length,ls.2.1.toArray,rs.1.toArray⟩,
    ls.2.2+rs.2)

theorem cut_cost (o : Ops M) (left right : List M) :
    (buildCut o left right).2 = left.length+right.length := by
  simp only [buildCut,suffix_cost,prefix_cost]

theorem cut_words (o : Ops M) (left right : List M) :
    (buildCut o left right).1.leftSuffix.size +
      (buildCut o left right).1.rightPrefix.size = left.length+right.length+2 := by
  simp only [buildCut,List.size_toArray,suffix_size,prefix_size]
  omega

/-- A crossing range uses two indexed reads and one ordered product.
    Empty ranges at the cut are supported. -/
def queryCut (o : Ops M) (idx : CutIndex M) (l r : Nat) : Option M :=
  if l ≤ idx.cut && idx.cut ≤ r && r ≤ idx.len then
    (idx.leftSuffix[l]?).bind fun a =>
      (idx.rightPrefix[r-idx.cut]?).map fun b => o.mul a b
  else none

private theorem drop_append_left (x y : List M) (l : Nat) (hl : l ≤ x.length) :
    (x ++ y).drop l = x.drop l ++ y := by
  induction x generalizing l with
  | nil =>
    have h : l=0 := by simpa using hl
    subst l
    rfl
  | cons a xs ih =>
    cases l with
    | zero => rfl
    | succ l =>
      have h : l ≤ xs.length := by simpa using hl
      exact ih l h

private theorem take_append_left (x y : List M) (k : Nat) :
    (x ++ y).take (x.length+k) = x ++ y.take k := by
  induction x with
  | nil => simp only [List.length_nil, Nat.zero_add, List.nil_append]
  | cons a xs ih =>
    change (a :: (xs ++ y)).take (xs.length+1+k) = a :: (xs ++ y.take k)
    have h : xs.length+1+k = (xs.length+k)+1 := by omega
    rw [h]
    change a :: (xs ++ y).take (xs.length+k) = a :: (xs ++ y.take k)
    rw [ih]

theorem crossing_slice (left right : List M) (l r : Nat)
    (hl : l ≤ left.length) (hr : left.length ≤ r) :
    Spec.slice (left ++ right) l r =
      left.drop l ++ right.take (r-left.length) := by
  unfold Spec.slice
  rw [drop_append_left left right l hl]
  have h : r-l = (left.drop l).length + (r-left.length) := by
    rw [List.length_drop]; omega
  rw [h,take_append_left]

theorem queryCut_correct (o : Ops M) (left right : List M) (l r : Nat)
    (hl : l ≤ left.length) (hc : left.length ≤ r)
    (hr : r ≤ left.length+right.length) :
    queryCut o (buildCut o left right).1 l r =
      some (product o (Spec.slice (left ++ right) l r)) := by
  have hj : r-left.length ≤ right.length := by omega
  unfold queryCut
  simp only [buildCut,hl,hc,hr,decide_true,Bool.true_and,if_true]
  rw [show ((suffixScan o left).2.1.toArray[l]?) =
      some (product o (left.drop l)) by simpa using suffix_get o left l hl]
  rw [show ((prefixScan o o.one right).1.toArray[r-left.length]?) =
      some (product o (right.take (r-left.length))) by
      simpa only [List.getElem?_toArray,o.one_mul] using prefix_get o o.one right _ hj]
  simp only [Option.bind,Option.map,crossing_slice left right l r hl hc,product_append]

/-- A one-letter DFA transition is a noncommutative monoid element. -/
def dfaOps {α : Type} (d : DFA α) : Ops (Fin d.stateCount → Fin d.stateCount) where
  one := id
  mul := fun f g q => g (f q)
  one_mul := fun _ => rfl
  mul_one := fun _ => rfl
  assoc := fun _ _ _ => rfl

theorem dfa_product {α : Type} (d : DFA α) (w : Word α) :
    product (dfaOps d) (w.map (fun c q => d.step q c)) = d.transition w := by
  induction w with
  | nil => rfl
  | cons c cs ih =>
    funext q
    change product (dfaOps d) (cs.map (fun c q => d.step q c)) (d.step q c) =
      d.run (d.step q c) cs
    rw [ih]
    rfl

end REWB.RangeProducts
