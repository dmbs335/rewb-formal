import REWB.PeriodicConstructionWindows
import REWB.MaskedCutIndex

/-! Counted finite-table primitives for the joint cut index. Every list
traversal and table materialization returns its own counter. The generic
interface below is instantiated by materialized DFA maps in the companion
module; its bounds are hypotheses only for this reusable loop lemma. -/
namespace REWB.PeriodicConstruction.Cut
open REWB.FiniteRelation

variable {M : Type} [DecidableEq M]

/-- A retained enumeration, whose equality proof has no runtime content. -/
structure Universe (e : Enumeration M) where
  values : List M
  values_eq : values=e.elems

structure Primitives (o : RangeProducts.Ops M) where
  unit : Result M
  multiply : M→M→Result M
  equal : M→M→Result Bool
  unit_value : unit.1=o.one
  multiply_value : ∀a b,(multiply a b).1=o.mul a b
  equal_value : ∀a b,(equal a b).1=decide (a=b)

def any (f : X→Result Bool) : List X→Result Bool
  | []=>(false,1)
  | x::xs=>
    let a:=f x
    if a.1 then (true,a.2+2)
    else let b:=any f xs; (b.1,a.2+b.2+2)

theorem any_value (f : X→Result Bool) (xs : List X) :
    (any f xs).1=xs.any (fun x=>(f x).1) := by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>
    simp only [any,List.any_cons]
    cases h : (f x).1 <;> simp only [h,if_true,if_false,Bool.false_eq_true,ih,Bool.false_or,Bool.true_or]

theorem any_work (f : X→Result Bool) (xs : List X) (C : Nat)
    (hc : ∀x,x∈xs→(f x).2≤C) :
    (any f xs).2≤xs.length*(C+2)+1 := by
  induction xs with
  | nil=>simp [any]
  | cons x xs ih=>
    have ha:=hc x List.mem_cons_self
    have hb:=ih (fun y hy=>hc y (List.mem_cons_of_mem x hy))
    simp only [any,List.length_cons,Nat.add_mul,Nat.one_mul]
    split <;> dsimp only <;> omega

def finiteAny {e : Enumeration M} (u : Universe e) (f : M→Result Bool) : Result Bool :=
  any f u.values

theorem finiteAny_value {e : Enumeration M} (u : Universe e) (f : M→Result Bool) :
    (finiteAny u f).1=FiniteRelation.any e (fun x=>(f x).1) := by
  simp only [finiteAny,any_value,u.values_eq,FiniteRelation.any]

theorem finiteAny_work {e : Enumeration M} (u : Universe e) (f : M→Result Bool)
    (C : Nat) (hc : ∀x,(f x).2≤C) :
    (finiteAny u f).2≤e.elems.length*(C+2)+1 := by
  simpa only [finiteAny,u.values_eq] using any_work f u.values C (fun x _=>hc x)

def rows (values : List M) (f : M→M→Result Bool) : Result (List (MatrixTable.Cell M)) :=
  CountedProjection.flatMap (fun p=>
    CountedProjection.map (fun q=>let a:=f p q; ((p,q,a.1),a.2+1)) values) values

theorem rows_value (values : List M) (f : M→M→Result Bool) :
    (rows values f).1=MatrixTable.rows values values (fun p q=>(f p q).1) := by
  simp only [rows,CountedProjection.flatMap_value,CountedProjection.map_value,MatrixTable.rows]

def table {e : Enumeration M} (u : Universe e) (f : M→M→Result Bool) :
    Result (MatrixTable.Matrix e) :=
  let r:=rows u.values f
  (⟨r.1,by
    change (rows u.values f).1=MatrixTable.tabulate e (MatrixTable.read (rows u.values f).1)
    rw [rows_value,u.values_eq]
    change MatrixTable.tabulate e _=MatrixTable.tabulate e (MatrixTable.read (MatrixTable.tabulate e _))
    rw [MatrixTable.tabulate_read]⟩,r.2+1)

theorem table_value {e : Enumeration M} (u : Universe e) (f : M→M→Result Bool) :
    (table u f).1=MatrixTable.ofRel e (fun p q=>(f p q).1) := by
  apply MatrixTable.matrix_ext
  change MatrixTable.read (rows u.values f).1=MatrixTable.read _
  rw [rows_value,u.values_eq]
  rfl

def tableCost (N C : Nat) : Nat := N*(N*(C+3)+3)+2

theorem table_work {e : Enumeration M} (u : Universe e) (f : M→M→Result Bool)
    (C : Nat) (hc : ∀p q,(f p q).2≤C) :
    (table u f).2≤tableCost e.elems.length C := by
  have h:=flatMap_bound
    (fun p=>CountedProjection.map (fun q=>let a:=f p q; ((p,q,a.1),a.2+1)) u.values)
    u.values (u.values.length*(C+2)+1) u.values.length
    (by intro p _; exact map_bound _ _ (C+1) (by intro q _; exact Nat.add_le_add_right (hc p q) 1))
    (by intro p _; simp only [CountedProjection.map_value,List.length_map,Nat.le_refl])
  simp only [table,rows,tableCost,u.values_eq]
  simp only [u.values_eq] at h
  have he : e.elems.length*(C+2)+1+e.elems.length+2=
      e.elems.length*(C+3)+3 := by simp only [Nat.mul_add]; omega
  rw [he] at h
  omega

def read {o : RangeProducts.Ops M} (k : Primitives o) {e : Enumeration M}
    (a : MatrixTable.Matrix e) (p s : M) : Result Bool :=
  any (fun cell=>
    let left:=k.equal cell.1 p
    let right:=k.equal cell.2.1 s
    (left.1 && right.1 && cell.2.2,left.2+right.2+3)) a.data

theorem read_value {o : RangeProducts.Ops M} (k : Primitives o) {e : Enumeration M}
    (a : MatrixTable.Matrix e) (p s : M) :
    (read k a p s).1=MatrixTable.denote a p s := by
  simp only [read,any_value,k.equal_value,MatrixTable.denote,MatrixTable.read]
  congr 1
  funext cell
  rcases cell with ⟨x,y,b⟩
  cases b <;> simp [Bool.and_assoc]

def readCost (N E : Nat) : Nat := N*N*(2*E+5)+1

theorem read_work {o : RangeProducts.Ops M} (k : Primitives o) {e : Enumeration M}
    (a : MatrixTable.Matrix e) (p s : M) (E : Nat)
    (he : ∀x y,(k.equal x y).2≤E) :
    (read k a p s).2≤readCost e.elems.length E := by
  have h:=any_work
    (fun cell : MatrixTable.Cell M=>
      let left:=k.equal cell.1 p
      let right:=k.equal cell.2.1 s
      (left.1 && right.1 && cell.2.2,left.2+right.2+3)) a.data (2*E+3)
    (by intro cell _; have h1:=he cell.1 p; have h2:=he cell.2.1 s; dsimp only; omega)
  simpa only [read,readCost,MatrixTable.matrix_size,Nat.add_assoc,Nat.reduceAdd] using h

end REWB.PeriodicConstruction.Cut
