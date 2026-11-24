import REWB.MarkedTransfer

/-! Materialized Boolean transition matrices. The canonical table stores
    a Boolean for every ordered pair in a fixed enumeration. It contains
    no chain of deferred relation compositions. -/
namespace REWB.MatrixTable
open FiniteRelation

variable {S : Type} [DecidableEq S]

abbrev Cell (S : Type) := S × S × Bool

def rows (xs ys : List S) (r : Rel S) : List (Cell S) :=
  xs.flatMap (fun p => ys.map (fun q => (p,q,r p q)))

def tabulate (e : Enumeration S) (r : Rel S) : List (Cell S) :=
  rows e.elems e.elems r

def read (data : List (Cell S)) : Rel S :=
  fun p q => data.any (fun c => decide (c=(p,q,true)))

theorem rows_length (xs ys : List S) (r : Rel S) :
    (rows xs ys r).length = xs.length * ys.length := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    change ((ys.map (fun q => (p,q,r p q))) ++ rows xs ys r).length =
      (xs.length+1)*ys.length
    rw [List.length_append,List.length_map,ih,Nat.add_mul]
    omega

theorem tabulate_length (e : Enumeration S) (r : Rel S) :
    (tabulate e r).length = e.elems.length * e.elems.length :=
  rows_length _ _ _

theorem read_true (data : List (Cell S)) (p q : S) :
    read data p q = true ↔ (p,q,true) ∈ data := by
  simp only [read,List.any_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨c,hc,rfl⟩
    exact hc
  · intro h
    exact ⟨_,h,rfl⟩

theorem tabulate_read (e : Enumeration S) (r : Rel S) :
    read (tabulate e r) = r := by
  funext p q
  have h : read (tabulate e r) p q = true ↔ r p q = true := by
    rw [read_true]
    simp only [tabulate,rows,List.mem_flatMap,List.mem_map]
    constructor
    · rintro ⟨x,_,y,_,he⟩
      have hh : x=p ∧ y=q ∧ r x y=true := by simpa using he
      rcases hh with ⟨rfl,rfl,hh⟩
      exact hh
    · intro h
      exact ⟨p,e.complete p,q,e.complete q,by simp [h]⟩
  cases hx : read (tabulate e r) p q <;> cases hy : r p q <;> simp_all

structure Matrix (e : Enumeration S) where
  data : List (Cell S)
  canonical : data = tabulate e (read data)

def ofRel (e : Enumeration S) (r : Rel S) : Matrix e :=
  ⟨tabulate e r,by rw [tabulate_read]⟩

def denote {e : Enumeration S} (a : Matrix e) : Rel S := read a.data

theorem denote_ofRel (e : Enumeration S) (r : Rel S) :
    denote (ofRel e r) = r := tabulate_read e r

theorem matrix_ext {e : Enumeration S} (a b : Matrix e)
    (h : denote a = denote b) : a=b := by
  cases a with
  | mk ad ha =>
    cases b with
    | mk bd hb =>
      change read ad = read bd at h
      have he : ad=bd := ha.trans ((congrArg (tabulate e) h).trans hb.symm)
      subst bd
      rfl

theorem matrix_size {e : Enumeration S} (a : Matrix e) :
    a.data.length = e.elems.length * e.elems.length := by
  rw [a.canonical,tabulate_length]

def one (e : Enumeration S) : Matrix e := ofRel e ident

def mul (e : Enumeration S) (a b : Matrix e) : Matrix e :=
  ofRel e (comp e (denote a) (denote b))

theorem denote_one (e : Enumeration S) : denote (one e) = ident :=
  denote_ofRel e ident

theorem denote_mul (e : Enumeration S) (a b : Matrix e) :
    denote (mul e a b) = comp e (denote a) (denote b) :=
  denote_ofRel _ _

theorem one_mul (e : Enumeration S) (a : Matrix e) : mul e (one e) a = a := by
  apply matrix_ext
  rw [denote_mul,denote_one,ident_left]

theorem mul_one (e : Enumeration S) (a : Matrix e) : mul e a (one e) = a := by
  apply matrix_ext
  rw [denote_mul,denote_one,ident_right]

theorem mul_assoc (e : Enumeration S) (a b c : Matrix e) :
    mul e (mul e a b) c = mul e a (mul e b c) := by
  apply matrix_ext
  simp only [denote_mul,comp_assoc]

def ops (e : Enumeration S) : RangeProducts.Ops (Matrix e) :=
  ⟨one e,mul e,one_mul e,mul_one e,mul_assoc e⟩

theorem denote_product (e : Enumeration S) (xs : List (Matrix e)) :
    denote (RangeProducts.product (ops e) xs) =
      RangeProducts.product (FiniteRelation.ops e) (xs.map denote) := by
  induction xs with
  | nil => exact denote_one e
  | cons a xs ih =>
    change denote (mul e a (RangeProducts.product (ops e) xs)) =
      comp e (denote a) (RangeProducts.product (FiniteRelation.ops e) (xs.map denote))
    rw [denote_mul,ih]

/-- The count here is the number of cells produced, not a whole-runtime
    measurement. Every matrix has exactly m² cells where m is the size of the
    fixed state enumeration. -/
theorem mul_cells (e : Enumeration S) (a b : Matrix e) :
    (mul e a b).data.length = e.elems.length * e.elems.length :=
  matrix_size _

end REWB.MatrixTable

namespace REWB.MarkedTransfer
open FiniteRelation
variable {α : Type}

def matrixLetters (d b : DFA α) (w : MarkedDP.MarkedWord α) :
    List (MatrixTable.Matrix (enum d b)) :=
  w.map (fun x => MatrixTable.ofRel (enum d b) (letter d b x))

theorem matrixLetters_length (d b : DFA α) (w : MarkedDP.MarkedWord α) :
    (matrixLetters d b w).length = w.length := by simp [matrixLetters]

theorem matrix_product_correct (d b : DFA α) (w : MarkedDP.MarkedWord α) :
    MatrixTable.denote
      (RangeProducts.product (MatrixTable.ops (enum d b)) (matrixLetters d b w)) =
        transfer d b w := by
  rw [MatrixTable.denote_product]
  unfold matrixLetters transfer
  simp only [List.map_map,Function.comp_def,MatrixTable.denote_ofRel]

end REWB.MarkedTransfer
