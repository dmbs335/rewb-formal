import REWB.BoundaryIndexMixed
import REWB.BoundaryTrieLocus

/-! One shared range index of materialized DFA transition maps. Edges of
the compressed reversed-text trie query forward intervals in this index;
no edge word is constructed and no inverse transition is used. Counters
retain the existing dyadic index's actual product/visit convention. -/
namespace REWB.BoundaryApplication.Range
open REWB.Spec (slice)
open REWB.BoundaryIndex
variable {α : Type} {k : Nat}

abbrev Map (k : Nat) := Vector (Fin k) k

def one (k : Nat) : Map k := Counted.identity k
def mul (a b : Map k) : Map k := (Counted.compose b a).1

@[simp] theorem one_get (q : Fin k) : (one k).get q=q := Counted.identity_get q
@[simp] theorem mul_get (a b : Map k) (q : Fin k) : (mul a b).get q=b.get (a.get q) :=
  Counted.compose_get b a q

def ops (k : Nat) : RangeProducts.Ops (Map k) where
  one:=one k
  mul:=mul
  one_mul a:=by
    apply Vector.ext
    intro i hi
    change (mul (one k) a).get ⟨i,hi⟩=a.get ⟨i,hi⟩
    simp only [mul_get,one_get]
  mul_one a:=by
    apply Vector.ext
    intro i hi
    change (mul a (one k)).get ⟨i,hi⟩=a.get ⟨i,hi⟩
    simp only [mul_get,one_get]
  assoc a b c:=by
    apply Vector.ext
    intro i hi
    change (mul (mul a b) c).get ⟨i,hi⟩=(mul a (mul b c)).get ⟨i,hi⟩
    simp only [mul_get]

def letter (d : DFA α) (c : α) : Map d.stateCount := Vector.ofFn (fun q=>d.step q c)
def letters (d : DFA α) (w : Word α) : List (Map d.stateCount) := w.map (letter d)

@[simp] theorem letter_get (d : DFA α) (c : α) (q : Fin d.stateCount) :
    (letter d c).get q=d.step q c := by simp [letter]

theorem product_run (d : DFA α) (w : Word α) (q : Fin d.stateCount) :
    (RangeProducts.product (ops d.stateCount) (letters d w)).get q=d.run q w := by
  induction w generalizing q with
  | nil => simp only [letters,List.map_nil,RangeProducts.product,ops,one_get,DFA.run]
  | cons c w ih =>
    change (mul (letter d c) (RangeProducts.product (ops d.stateCount) (letters d w))).get q=_
    rw [mul_get,letter_get,ih]
    rfl

theorem letters_slice (d : DFA α) (w : Word α) (l r : Nat) :
    slice (letters d w) l r=letters d (slice w l r) := by
  simp only [slice,letters,List.map_drop,List.map_take]

structure Index (d : DFA α) where
  tree : DyadicIndex.Tree (Map d.stateCount)
  length : Nat
  products : Nat
  letterCells : Nat

def build (d : DFA α) (w : Word α) : Index d :=
  let r:=DyadicIndex.buildFor (ops d.stateCount) (letters d w)
  ⟨r.1,w.length,r.2,w.length*d.stateCount⟩

theorem build_length (d : DFA α) (w : Word α) : (build d w).length=w.length := rfl

structure Result (k : Nat) where
  map : Map k
  products : Nat
  visits : Nat

def query (d : DFA α) (idx : Index d) (l r : Nat) : Result d.stateCount :=
  let ans:=DyadicIndex.query (ops d.stateCount) idx.tree l r
  ⟨ans.answer.getD (one d.stateCount),ans.products,ans.visits⟩

theorem query_correct (d : DFA α) (w : Word α) (l r : Nat)
    (hl : l≤r) (hr : r≤w.length) (q : Fin d.stateCount) :
    (query d (build d w) l r).map.get q=d.run q (slice w l r) := by
  have hh:=(DyadicIndex.queryFor_spec (ops d.stateCount) (letters d w) l r hl
    (by simpa only [letters,List.length_map] using hr)).1
  simp only [query,build]
  rw [hh,Option.getD_some,letters_slice,product_run]

theorem query_bounds (d : DFA α) (w : Word α) (l r : Nat)
    (hl : l≤r) (hr : r≤w.length) :
    (query d (build d w) l r).products≤1 ∧
      (query d (build d w) l r).visits≤w.length.log2+2 := by
  have hh:=(DyadicIndex.queryFor_spec (ops d.stateCount) (letters d w) l r hl
    (by simpa only [letters,List.length_map] using hr)).2
  simpa only [query,build,letters,List.length_map] using hh

theorem build_products (d : DFA α) (w : Word α) :
    (build d w).products=(w.length.log2+1)*w.length := by
  simp only [build,DyadicIndex.buildFor_cost,letters,List.length_map]

/-- Pattern-dependent map-cell operations plus range-tree visits. The
unit scalar and allocator model remains that of the shared range index. -/
def Result.work (r : Result k) : Nat := k*r.products+8*r.visits+1

theorem query_work (d : DFA α) (w : Word α) (l r : Nat)
    (hl : l≤r) (hr : r≤w.length) :
    (query d (build d w) l r).work≤d.stateCount+8*(w.length.log2+2)+1 := by
  have hh:=query_bounds d w l r hl hr
  have hp:=Nat.mul_le_mul_left d.stateCount hh.1
  unfold Result.work
  omega

end REWB.BoundaryApplication.Range
