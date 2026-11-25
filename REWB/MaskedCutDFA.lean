import REWB.MaskedCutIndex
import REWB.MaskedFiniteActionMaps

/-! Joint cut tuples for three pattern automata.  The finite universe is
the product of their materialized transformation universes.  Its size
depends only on the automata.  A range-index entry retains both sides of
one cut, so different automata cannot accidentally choose different cuts.
-/
namespace REWB.MaskedCut.DFAIndex
open REWB.FiniteRelation
open REWB.RangeProducts (Ops product)
open REWB.MaskedFiniteAction.Maps
open REWB.Spec (slice)

variable {α : Type}

def mapOps (m : Nat) : Ops (Map m) where
  one := identity m
  mul := REWB.MaskedFiniteAction.Maps.mul
  one_mul := by
    intro a
    apply Vector.ext
    intro i hi
    change (REWB.MaskedFiniteAction.Maps.mul (identity m) a).get ⟨i,hi⟩=a.get ⟨i,hi⟩
    simp only [mul_get,identity,BoundaryIndex.Table.get_ofFn,id_eq]
  mul_one := by
    intro a
    apply Vector.ext
    intro i hi
    change (REWB.MaskedFiniteAction.Maps.mul a (identity m)).get ⟨i,hi⟩=a.get ⟨i,hi⟩
    simp only [mul_get,identity,BoundaryIndex.Table.get_ofFn,id_eq]
  assoc := REWB.MaskedFiniteAction.Maps.mul_assoc

def prodOps {X Y : Type} (a : Ops X) (b : Ops Y) : Ops (X×Y) where
  one := (a.one,b.one)
  mul := fun x y=>(a.mul x.1 y.1,b.mul x.2 y.2)
  one_mul := by intro x; simp only [a.one_mul,b.one_mul]
  mul_one := by intro x; simp only [a.mul_one,b.mul_one]
  assoc := by intro x y z; simp only [a.assoc,b.assoc]

def prodEnum {X Y : Type} (a : Enumeration X) (b : Enumeration Y) : Enumeration (X×Y) :=
  ⟨a.elems.flatMap (fun x=>b.elems.map (fun y=>(x,y))),by
    intro x
    exact List.mem_flatMap.mpr ⟨x.1,a.complete _,List.mem_map.mpr ⟨x.2,b.complete _,rfl⟩⟩⟩

theorem prodEnum_length {X Y : Type} (a : Enumeration X) (b : Enumeration Y) :
    (prodEnum a b).elems.length=a.elems.length*b.elems.length := by
  change (a.elems.flatMap (fun x=>b.elems.map (fun y=>(x,y)))).length=_
  induction a.elems with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons,List.length_append,List.length_map,ih,List.length_cons,
      Nat.add_mul,Nat.one_mul]
    omega

def mapEnum (m : Nat) : Enumeration (Map m) := ⟨allMaps m,universe_complete m⟩

abbrev Joint (b c e : DFA α) := Map b.stateCount × Map c.stateCount × Map e.stateCount

def jointOps (b c e : DFA α) : Ops (Joint b c e) :=
  prodOps (mapOps b.stateCount) (prodOps (mapOps c.stateCount) (mapOps e.stateCount))

def jointEnum (b c e : DFA α) : Enumeration (Joint b c e) :=
  prodEnum (mapEnum b.stateCount) (prodEnum (mapEnum c.stateCount) (mapEnum e.stateCount))

theorem jointEnum_length (b c e : DFA α) :
    (jointEnum b c e).elems.length=
      b.stateCount^b.stateCount*(c.stateCount^c.stateCount*e.stateCount^e.stateCount) := by
  simp only [jointEnum,prodEnum_length]
  change count b.stateCount*(count c.stateCount*count e.stateCount)=_
  rw [count_eq,count_eq,count_eq]

def jointWord (b c e : DFA α) (w : Word α) : Joint b c e :=
  (wordMap b w,wordMap c w,wordMap e w)

def letters (b c e : DFA α) (w : Word α) : List (Joint b c e) :=
  w.map (fun x=>jointWord b c e [x])

theorem jointWord_nil (b c e : DFA α) :
    jointWord b c e []=(jointOps b c e).one := rfl

theorem jointWord_append (b c e : DFA α) (u v : Word α) :
    jointWord b c e (u++v)=(jointOps b c e).mul (jointWord b c e u) (jointWord b c e v) := by
  simp only [jointWord,wordMap_append,jointOps,prodOps,mapOps]

theorem letters_product (b c e : DFA α) (w : Word α) :
    product (jointOps b c e) (letters b c e w)=jointWord b c e w := by
  induction w with
  | nil => rfl
  | cons x xs ih =>
    change (jointOps b c e).mul (jointWord b c e [x])
      (product (jointOps b c e) (letters b c e xs))=jointWord b c e ([x]++xs)
    rw [ih,jointWord_append]

theorem letters_length (b c e : DFA α) (w : Word α) :
    (letters b c e w).length=w.length := List.length_map _

theorem letters_slice (b c e : DFA α) (w : Word α) (l r : Nat) :
    slice (letters b c e w) l r=letters b c e (slice w l r) := by
  simp only [letters,slice,List.map_drop,List.map_take]

def build (b c e : DFA α) (w : Word α) : Index.Tree (jointEnum b c e)×Nat :=
  Index.build (jointOps b c e) (jointEnum b c e) (letters b c e w)

theorem build_products (b c e : DFA α) (w : Word α) :
    (build b c e w).2=(Nat.log2 w.length+1)*w.length := by
  simp only [build,Index.build_products,letters_length]

theorem query_correct (b c e : DFA α) (w : Word α) (l lo hi r : Nat)
    (p s : Joint b c e) (hl : l≤lo) (hb : lo≤hi) (hr : hi≤r) (hn : r≤w.length) :
    (Index.query (jointOps b c e) (jointEnum b c e) (build b c e w).1 l lo hi r).answer.map
      (fun table=>MatrixTable.denote table p s)=some true ↔
        ∃ i,lo≤i ∧ i≤hi ∧ jointWord b c e (slice w l i)=p ∧
          jointWord b c e (slice w i r)=s := by
  have hh := Index.query_correct (jointOps b c e) (jointEnum b c e) (letters b c e w)
    l lo hi r p s hl hb hr (by simpa only [letters_length] using hn)
  simpa only [build,letters_slice,letters_product] using hh

/-- The E suffix stops at mid; the C suffix continues to r.  Both come
from the very same cut i.  The tail needs no inverse transformation. -/
def constrained (b c e : DFA α) (p s tail : Joint b c e) : Joint b c e :=
  (p.1,REWB.MaskedFiniteAction.Maps.mul s.2.1 tail.2.1,s.2.2)

theorem constrained_exact (b c e : DFA α) (w : Word α) (l i mid r : Nat)
    (hi : i≤mid) (hr : mid≤r) :
    constrained b c e (jointWord b c e (slice w l i))
      (jointWord b c e (slice w i mid)) (jointWord b c e (slice w mid r))=
        (wordMap b (slice w l i),wordMap c (slice w i r),wordMap e (slice w i mid)) := by
  simp only [constrained,jointWord]
  rw [← wordMap_append,← OuterColumn.slice_split w i mid r hi hr]

end REWB.MaskedCut.DFAIndex
