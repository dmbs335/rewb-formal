import REWB.MaskedCut
import REWB.OuterColumn

/-! A shared range index for joint prefix/suffix transformations.

Three indexed ranges impose a closed interval of allowed cuts.  No query
enumerates the cut positions.  The matrix rows and columns are finite
monoid elements, not text positions.  Thus one doubled-period index serves
all rotations with a pattern-only matrix dimension.

The counters below count actual summary products and hierarchy visits.
Each summary product and output table is materialized over the fixed
enumeration; the cost of the finite monoid operations is a separate
pattern-only factor.
-/
namespace REWB.MaskedCut.Index
open REWB.FiniteRelation
open REWB.RangeProducts (Ops product)
open REWB.Spec (slice)

variable {M : Type} [DecidableEq M]

abbrev Tree (e : Enumeration M) := DyadicIndex.Tree (Summary e)

def build (o : Ops M) (e : Enumeration M) (xs : List M) : Tree e×Nat :=
  DyadicIndex.buildFor (ops o e) (xs.map (atom o e))

theorem build_products (o : Ops M) (e : Enumeration M) (xs : List M) :
    (build o e xs).2=(Nat.log2 xs.length+1)*xs.length := by
  simp only [build,DyadicIndex.buildFor_cost,List.length_map]

theorem range_value (o : Ops M) (e : Enumeration M) (xs : List M) (l r : Nat)
    (hl : l≤r) (hr : r≤xs.length) :
    (DyadicIndex.query (ops o e) (build o e xs).1 l r).answer=
      some (trace o e (slice xs l r)) := by
  have hh := (DyadicIndex.queryFor_spec (ops o e) (xs.map (atom o e)) l r hl
    (by simpa only [List.length_map] using hr)).1
  simpa only [build,trace,slice,List.map_drop,List.map_take] using hh

theorem range_bounds (o : Ops M) (e : Enumeration M) (xs : List M) (l r : Nat)
    (hl : l≤r) (hr : r≤xs.length) :
    (DyadicIndex.query (ops o e) (build o e xs).1 l r).products≤1 ∧
    (DyadicIndex.query (ops o e) (build o e xs).1 l r).visits≤Nat.log2 xs.length+2 := by
  have hh := (DyadicIndex.queryFor_spec (ops o e) (xs.map (atom o e)) l r hl
    (by simpa only [List.length_map] using hr)).2
  simpa only [build,List.length_map] using hh

/-- Transport both sides of one middle cut through fixed outside words. -/
def window (o : Ops M) (e : Enumeration M) (left middle right : Summary e) :
    MatrixTable.Matrix e :=
  MatrixTable.ofRel e (fun p s=>any e (fun u=>any e (fun v=>
    closed o middle u v && decide (o.mul left.total u=p ∧ o.mul v right.total=s))))

theorem window_true (o : Ops M) (e : Enumeration M) (left middle right : Summary e)
    (p s : M) :
    MatrixTable.denote (window o e left middle right) p s=true ↔
      ∃ u v,closed o middle u v=true ∧
        o.mul left.total u=p ∧ o.mul v right.total=s := by
  simp only [window,MatrixTable.denote_ofRel,any_true,Bool.and_eq_true,decide_eq_true_eq]

theorem window_trace (o : Ops M) (e : Enumeration M) (x y z : List M) (p s : M) :
    MatrixTable.denote (window o e (trace o e x) (trace o e y) (trace o e z)) p s=true ↔
      ∃ i,i≤y.length ∧ product o (x++y.take i)=p ∧ product o (y.drop i++z)=s := by
  rw [window_true]
  simp only [trace_closed,trace_total,RangeProducts.product_append]
  constructor
  · rintro ⟨u,v,⟨i,hi,hp,hs⟩,he,hf⟩
    exact ⟨i,hi,by rw [hp,he],by rw [hs,hf]⟩
  · rintro ⟨i,hi,hp,hs⟩
    exact ⟨product o (y.take i),product o (y.drop i),⟨i,hi,rfl,rfl⟩,hp,hs⟩

structure Result (e : Enumeration M) where
  answer : Option (MatrixTable.Matrix e)
  products : Nat
  visits : Nat

/-- All cuts a≤i≤b inside [l,r). Empty words and a=b are supported. -/
def query (o : Ops M) (e : Enumeration M) (idx : Tree e) (l a b r : Nat) : Result e :=
  let left := DyadicIndex.query (ops o e) idx l a
  let middle := DyadicIndex.query (ops o e) idx a b
  let right := DyadicIndex.query (ops o e) idx b r
  ⟨left.answer.bind (fun x=>middle.answer.bind (fun y=>right.answer.map (window o e x y))),
    left.products+middle.products+right.products,left.visits+middle.visits+right.visits⟩

theorem query_value (o : Ops M) (e : Enumeration M) (xs : List M) (l a b r : Nat)
    (hla : l≤a) (hab : a≤b) (hbr : b≤r) (hr : r≤xs.length) :
    (query o e (build o e xs).1 l a b r).answer=some
      (window o e (trace o e (slice xs l a)) (trace o e (slice xs a b))
        (trace o e (slice xs b r))) := by
  simp only [query]
  rw [range_value o e xs l a hla (by omega),range_value o e xs a b hab (by omega),
    range_value o e xs b r hbr hr]
  rfl

private theorem take_slice (xs : List M) (l i r : Nat)
    (hli : l≤i) (hir : i≤r) (hr : r≤xs.length) :
    (slice xs l r).take (i-l)=slice xs l i := by
  have hh := OuterColumn.slice_length xs l i hli (by omega)
  rw [OuterColumn.slice_split xs l i r hli hir,← hh,List.take_left]

private theorem drop_slice (xs : List M) (l i r : Nat)
    (hli : l≤i) (hir : i≤r) (hr : r≤xs.length) :
    (slice xs l r).drop (i-l)=slice xs i r := by
  have hh := OuterColumn.slice_length xs l i hli (by omega)
  rw [OuterColumn.slice_split xs l i r hli hir,← hh,List.drop_left]

theorem query_correct (o : Ops M) (e : Enumeration M) (xs : List M)
    (l a b r : Nat) (p s : M)
    (hla : l≤a) (hab : a≤b) (hbr : b≤r) (hr : r≤xs.length) :
    (query o e (build o e xs).1 l a b r).answer.map
      (fun table=>MatrixTable.denote table p s)=some true ↔
        ∃ i,a≤i ∧ i≤b ∧ product o (slice xs l i)=p ∧ product o (slice xs i r)=s := by
  rw [query_value _ _ _ _ _ _ _ hla hab hbr hr]
  simp only [Option.map,Option.some.injEq,window_trace]
  have hlen := OuterColumn.slice_length xs a b hab (by omega)
  constructor
  · rintro ⟨j,hj,hp,hs⟩
    have hai : a≤a+j := by omega
    have hib : a+j≤b := by omega
    have he : a+j-a=j := by omega
    rw [← he,take_slice xs a (a+j) b hai hib (by omega),
      ← OuterColumn.slice_split xs l a (a+j) hla hai] at hp
    rw [← he,drop_slice xs a (a+j) b hai hib (by omega),
      ← OuterColumn.slice_split xs (a+j) b r hib hbr] at hs
    exact ⟨a+j,hai,hib,hp,hs⟩
  · rintro ⟨i,hai,hib,hp,hs⟩
    refine ⟨i-a,by omega,?_,?_⟩
    · rw [take_slice xs a i b hai hib (by omega),
        ← OuterColumn.slice_split xs l a i hla hai]
      exact hp
    · rw [drop_slice xs a i b hai hib (by omega),
        ← OuterColumn.slice_split xs i b r hib hbr]
      exact hs

theorem query_bounds (o : Ops M) (e : Enumeration M) (xs : List M) (l a b r : Nat)
    (hla : l≤a) (hab : a≤b) (hbr : b≤r) (hr : r≤xs.length) :
    (query o e (build o e xs).1 l a b r).products≤3 ∧
    (query o e (build o e xs).1 l a b r).visits≤3*(Nat.log2 xs.length+2) := by
  have h1 := range_bounds o e xs l a hla (by omega)
  have h2 := range_bounds o e xs a b hab (by omega)
  have h3 := range_bounds o e xs b r hbr hr
  simp only [query]
  constructor <;> omega

theorem window_cells (o : Ops M) (e : Enumeration M) (left middle right : Summary e) :
    (window o e left middle right).data.length=e.elems.length*e.elems.length :=
  MatrixTable.matrix_size _

end REWB.MaskedCut.Index
