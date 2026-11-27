import Std

/-! A concrete two-cell, null-terminated representation of word lists.
Each non-null node stores its payload at `p` and its successor at `p+1`.
Fresh allocation copies nodes above the previous arena frontier. These
are representation lemmas; actual instruction traces are proved in
`WordRAMLists`, rather than postulating traversal as a unit operation. -/
namespace REWB.WordRAM.ListHeap

abbrev Heap := Nat → Nat

inductive ListAt (heap : Heap) (limit : Nat) : Nat → List Nat → Prop
  | nil : ListAt heap limit 0 []
  | cons {p q x xs} (positive : 0 < p) (allocated : p+1 < limit)
      (value : heap p = x) (next : heap (p+1) = q)
      (tail : ListAt heap limit q xs) : ListAt heap limit p (x::xs)

theorem ListAt.nil_pointer {h : Heap} {b p : Nat} (hx : ListAt h b p []) : p = 0 := by
  cases hx
  rfl

theorem ListAt.cons_fields {h : Heap} {b p x : Nat} {xs : List Nat}
    (hx : ListAt h b p (x::xs)) :
    ∃ q, 0 < p ∧ p+1 < b ∧ h p = x ∧ h (p+1) = q ∧ ListAt h b q xs := by
  cases hx with
  | cons hp ha hv hn ht => exact ⟨_,hp,ha,hv,hn,ht⟩

theorem ListAt.pointer_lt {h : Heap} {b p : Nat} {xs : List Nat}
    (hx : ListAt h b p xs) (hb : 0 < b) : p < b := by
  cases hx with
  | nil => exact hb
  | cons hp ha => omega

theorem ListAt.mono {h : Heap} {b c p : Nat} {xs : List Nat}
    (hx : ListAt h b p xs) (hbc : b ≤ c) : ListAt h c p xs := by
  induction hx with
  | nil => exact .nil
  | cons hp ha hv hn ht ih => exact .cons hp (by omega) hv hn ih

theorem ListAt.frame {h g : Heap} {b p : Nat} {xs : List Nat}
    (hx : ListAt h b p xs) (hg : ∀ a, a < b → g a = h a) :
    ListAt g b p xs := by
  induction hx with
  | nil => exact .nil
  | cons hp ha hv hn ht ih =>
    exact .cons hp ha (by rw [hg _ (by omega)]; exact hv)
      (by rw [hg _ ha]; exact hn) ih

def push (h : Heap) (fresh x tail : Nat) : Heap :=
  fun i => if i = fresh+1 then tail else if i = fresh then x else h i

theorem push_below (h : Heap) (fresh x tail i : Nat) (hi : i < fresh) :
    push h fresh x tail i = h i := by
  simp [push, show i ≠ fresh+1 by omega, show i ≠ fresh by omega]

theorem push_value (h : Heap) (fresh x tail : Nat) :
    push h fresh x tail fresh = x := by simp [push]

theorem push_next (h : Heap) (fresh x tail : Nat) :
    push h fresh x tail (fresh+1) = tail := by simp [push]

theorem push_rep {h : Heap} {fresh tail : Nat} {xs : List Nat}
    (hf : 0 < fresh) (hx : ListAt h fresh tail xs) (x : Nat) :
    ListAt (push h fresh x tail) (fresh+2) fresh (x::xs) := by
  apply ListAt.cons hf (by omega) (push_value h fresh x tail) (push_next h fresh x tail)
  exact (hx.frame (fun i hi => push_below h fresh x tail i hi)).mono (by omega)

structure CopyResult where
  heap : Heap
  pointer : Nat
  frontier : Nat

/-- Value-level specification of copying a list onto a reversed accumulator.
The RAM program obtains payloads from memory; this recursive specification
is used only to state and prove its output relation. -/
def copyReverse (h : Heap) (fresh acc : Nat) : List Nat → CopyResult
  | [] => ⟨h,acc,fresh⟩
  | x::xs => copyReverse (push h fresh x acc) (fresh+2) fresh xs

theorem copyReverse_frontier (h : Heap) (fresh acc : Nat) (xs : List Nat) :
    (copyReverse h fresh acc xs).frontier = fresh+2*xs.length := by
  induction xs generalizing h fresh acc with
  | nil => simp [copyReverse]
  | cons x xs ih => simp only [copyReverse,ih,List.length_cons]; omega

theorem copyReverse_below (h : Heap) (fresh acc : Nat) (xs : List Nat)
    (i : Nat) (hi : i < fresh) :
    (copyReverse h fresh acc xs).heap i = h i := by
  induction xs generalizing h fresh acc with
  | nil => rfl
  | cons x xs ih =>
    rw [copyReverse,ih _ _ _ (by omega)]
    exact push_below h fresh x acc i hi

theorem copyReverse_rep {h : Heap} {fresh acc : Nat} {ys : List Nat}
    (hf : 0 < fresh) (hy : ListAt h fresh acc ys) (xs : List Nat) :
    let out := copyReverse h fresh acc xs
    ListAt out.heap out.frontier out.pointer (xs.reverse++ys) := by
  induction xs generalizing h fresh acc ys with
  | nil => simpa [copyReverse] using hy
  | cons x xs ih =>
    have hh := ih (h := push h fresh x acc) (fresh := fresh+2) (acc := fresh)
      (ys := x::ys) (by omega) (push_rep hf hy x)
    simpa only [copyReverse,List.reverse_cons,List.append_assoc,List.singleton_append] using hh

theorem copyReverse_preserves {h : Heap} {fresh acc p : Nat} {xs ys : List Nat}
    (hy : ListAt h fresh p ys) :
    ListAt (copyReverse h fresh acc xs).heap (copyReverse h fresh acc xs).frontier p ys := by
  apply ListAt.mono (hy.frame (fun i hi => copyReverse_below h fresh acc xs i hi))
  rw [copyReverse_frontier]
  omega

theorem push_values_bounded {h : Heap} {fresh x tail limit : Nat}
    (hh : ∀ a, h a < limit) (hx : x < limit) (ht : tail < limit) :
    ∀ a, push h fresh x tail a < limit := by
  intro a
  unfold push
  split
  · exact ht
  · split
    · exact hx
    · exact hh a

theorem copyReverse_values_bounded {h : Heap} {fresh acc limit : Nat} {xs : List Nat}
    (hh : ∀ a, h a < limit) (hx : ∀ x ∈ xs, x < limit)
    (ha : acc < limit) (hf : fresh+2*xs.length ≤ limit) :
    ∀ a, (copyReverse h fresh acc xs).heap a < limit := by
  induction xs generalizing h fresh acc with
  | nil => exact hh
  | cons x xs ih =>
    apply ih (push_values_bounded hh (hx x (by simp)) ha)
      (fun y hy => hx y (by simp [hy]))
    · simp only [List.length_cons] at hf
      omega
    · simp only [List.length_cons] at hf
      omega

end REWB.WordRAM.ListHeap
