import REWB.BoundaryIndexCounted

/-! Materialized finite vectors of Boolean transition matrices.

    The k entries represent a fixed-pattern action universe.  Shortening a
    common word prefix reindexes this vector; k must not enumerate text
    positions or q phases.  Reindexing is precomposition and permits
    noninjective maps.  It is different from existential-image recoloring.

    Matrix multiplication counts all predecessor probes and output Boolean
    cells. Reindexing counts written matrix-vector entries; the immutable
    matrices are shared.  Map composition writes a fresh finite vector, so
    future reads never traverse a chain of deferred functions. -/
namespace REWB.MaskedFiniteAction
open REWB.FiniteRelation

abbrev View (k m : Nat) := Fin k → Rel (Fin m)

namespace View
variable {k m : Nat}

def one : View k m := fun _ => ident
def mul (a b : View k m) : View k m := fun i => comp (finEnum m) (a i) (b i)
def reindex (g : Fin k → Fin k) (a : View k m) : View k m := fun i => a (g i)

theorem one_mul (a : View k m) : mul one a=a := by
  funext i
  exact ident_left _ _

theorem mul_one (a : View k m) : mul a one=a := by
  funext i
  exact ident_right _ _

theorem mul_assoc (a b c : View k m) : mul (mul a b) c=mul a (mul b c) := by
  funext i
  exact comp_assoc _ _ _ _

def ops : RangeProducts.Ops (View k m) :=
  ⟨one,mul,one_mul,mul_one,mul_assoc⟩

theorem reindex_id (a : View k m) : reindex id a=a := rfl

/-- Precomposition reverses the written order of the two index maps. -/
theorem reindex_comp (g f : Fin k → Fin k) (a : View k m) :
    reindex g (reindex f a)=reindex (fun i => f (g i)) a := rfl

theorem reindex_one (g : Fin k → Fin k) : reindex g (one : View k m)=one := rfl

theorem reindex_mul (g : Fin k → Fin k) (a b : View k m) :
    reindex g (mul a b)=mul (reindex g a) (reindex g b) := rfl

def product : List (View k m) → View k m := RangeProducts.product ops

theorem product_append (xs ys : List (View k m)) :
    product (xs++ys)=mul (product xs) (product ys) :=
  RangeProducts.product_append ops xs ys

theorem reindex_product (g : Fin k → Fin k) (xs : List (View k m)) :
    reindex g (product xs)=product (xs.map (reindex g)) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change reindex g (mul a (product xs))=mul (reindex g a) (product (xs.map (reindex g)))
    rw [reindex_mul,ih]

end View

abbrev Matrix (m : Nat) := Vector (Vector Bool m) m

structure Table (k m : Nat) where
  cells : Vector (Matrix m) k

namespace Table
variable {k m : Nat}

def view (a : Table k m) : View k m := fun i p q => ((a.cells.get i).get p).get q

def ofView (a : View k m) : Table k m :=
  ⟨Vector.ofFn (fun i => Vector.ofFn (fun p => Vector.ofFn (fun q => a i p q)))⟩

@[simp] theorem view_ofView (a : View k m) : (ofView a).view=a := by
  funext i p q
  simp only [view,ofView,BoundaryIndex.Table.get_ofFn]

def one : Table k m := ofView View.one

@[simp] theorem view_one : (one : Table k m).view=View.one := view_ofView _

end Table

namespace Counted
open REWB.BoundaryIndex.Counted (scan scan_value scan_steps rowWork rowWork_uniform sum_ofFn_const)
variable {k m : Nat}

/-- Fully materialized pointwise Boolean matrix multiplication. -/
def mul (a b : Table k m) : Table k m × Nat :=
  let results := Vector.ofFn (fun i : Fin k => Vector.ofFn (fun p : Fin m =>
    Vector.ofFn (fun q : Fin m =>
      scan (fun s : Fin m => a.view i p s && b.view i s q) (List.ofFn id))))
  let out := Vector.ofFn (fun i => Vector.ofFn (fun p =>
    Vector.ofFn (fun q => (((results.get i).get p).get q).1)))
  (⟨out⟩,(List.ofFn (fun i =>
    (List.ofFn (fun p => rowWork ((results.get i).get p))).sum)).sum)

theorem mul_view (a b : Table k m) : (mul a b).1.view=View.mul a.view b.view := by
  funext i p q
  simp only [mul,Table.view,BoundaryIndex.Table.get_ofFn,View.mul,
    FiniteRelation.comp,FiniteRelation.any,FiniteRelation.finEnum,scan_value]

theorem mul_steps (a b : Table k m) : (mul a b).2=k*(m*(m*(m+1))) := by
  unfold mul
  simp only [BoundaryIndex.Table.get_ofFn]
  have hh (i : Fin k) (p : Fin m) :
      rowWork (Vector.ofFn (fun q : Fin m =>
        scan (fun s : Fin m => a.view i p s && b.view i s q) (List.ofFn id)))=m*(m+1) := by
    apply rowWork_uniform
    intro q
    simp only [BoundaryIndex.Table.get_ofFn,scan_steps,List.length_ofFn]
  simp only [hh,sum_ofFn_const]

/-- Sharing immutable matrices is safe: only the vector of matrix entries
    changes. No inverse or injectivity premise is used. -/
def reindex (g : Vector (Fin k) k) (a : Table k m) : Table k m × Nat :=
  (⟨Vector.ofFn (fun i => a.cells.get (g.get i))⟩,k)

theorem reindex_view (g : Vector (Fin k) k) (a : Table k m) :
    (reindex g a).1.view=View.reindex g.get a.view := by
  funext i p q
  simp only [reindex,Table.view,BoundaryIndex.Table.get_ofFn,View.reindex]

theorem reindex_steps (g : Vector (Fin k) k) (a : Table k m) :
    (reindex g a).2=k := rfl

def compose (f g : Vector (Fin k) k) : Vector (Fin k) k × Nat :=
  BoundaryIndex.Counted.compose f g

@[simp] theorem compose_get (f g : Vector (Fin k) k) (i : Fin k) :
    (compose f g).1.get i=f.get (g.get i) :=
  BoundaryIndex.Counted.compose_get f g i

theorem compose_steps (f g : Vector (Fin k) k) : (compose f g).2=k := rfl

def identity (k : Nat) : Vector (Fin k) k := BoundaryIndex.Counted.identity k

@[simp] theorem identity_get (i : Fin k) : (identity k).get i=i :=
  BoundaryIndex.Counted.identity_get i

end Counted
end REWB.MaskedFiniteAction
