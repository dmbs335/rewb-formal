import REWB.PeriodicConstructionCutSummary

/-! Primitive substitution along the actual dyadic query path. The first
component retains the original answer, product count and visit count.
The second component also charges list slicing at the (singleton) leaves,
array reads, finite products and scalar control. -/
namespace REWB.PeriodicConstruction.Cut

structure ProductOps {M : Type} (o : RangeProducts.Ops M) where
  unit : Result M
  multiply : M→M→Result M
  unit_value : unit.1=o.one
  multiply_value : ∀a b,(multiply a b).1=o.mul a b

variable {M : Type} {o : RangeProducts.Ops M}

def split : Nat→List M→Result (List M×List M)
  | 0,xs=>(([],xs),1)
  | _+1,[]=>(([],[]),1)
  | n+1,x::xs=>let r:=split n xs; ((x::r.1.1,r.1.2),r.2+2)

theorem split_value (n : Nat) (xs : List M) : (split n xs).1=(xs.take n,xs.drop n) := by
  induction n generalizing xs with
  | zero=>rfl
  | succ n ih=>cases xs with
    | nil=>rfl
    | cons x xs=>simp only [split,List.take_succ_cons,List.drop_succ_cons,ih]

theorem split_work (n : Nat) (xs : List M) : (split n xs).2≤2*xs.length+1 := by
  induction n generalizing xs with
  | zero=>simp only [split]; omega
  | succ n ih=>cases xs with
    | nil=>exact Nat.le_refl _
    | cons x xs=>have h:=ih xs; simp only [split,List.length_cons,Nat.mul_add,Nat.mul_one]; omega

def sliced (xs : List M) (l r : Nat) : Result (List M) :=
  let before:=split l xs
  let inside:=split (r-l) before.1.2
  (inside.1.1,before.2+inside.2+2)

theorem sliced_value (xs : List M) (l r : Nat) : (sliced xs l r).1=Spec.slice xs l r := by
  simp only [sliced,split_value,Spec.slice]

theorem sliced_work (xs : List M) (l r : Nat) : (sliced xs l r).2≤4*xs.length+4 := by
  have h1:=split_work l xs
  have h2:=split_work (r-l) (split l xs).1.2
  have hl : (split l xs).1.2.length≤xs.length := by rw [split_value,List.length_drop]; omega
  dsimp only [sliced]
  omega

def product (k : ProductOps o) : List M→Result (M×Nat)
  | []=>((k.unit.1,0),k.unit.2+1)
  | x::xs=>
    let tail:=product k xs
    let p:=k.multiply x tail.1.1
    ((p.1,tail.1.2+1),tail.2+p.2+3)

theorem product_value (k : ProductOps o) (xs : List M) :
    (product k xs).1=(RangeProducts.product o xs,xs.length) := by
  induction xs with
  | nil=>simp only [product,k.unit_value,RangeProducts.product,List.length_nil]
  | cons x xs ih=>simp only [product,ih,k.multiply_value,RangeProducts.product,List.length_cons]

theorem product_work (k : ProductOps o) (xs : List M) (C : Nat)
    (hu : k.unit.2≤C) (hm : ∀a b,(k.multiply a b).2≤C) :
    (product k xs).2≤xs.length*(C+3)+C+1 := by
  induction xs with
  | nil=>simp only [product,List.length_nil,Nat.zero_mul,Nat.zero_add]; omega
  | cons x xs ih=>
    have h:=hm x (product k xs).1.1
    simp only [product,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

def crossing (k : ProductOps o) (idx : RangeProducts.CutIndex M) (l r : Nat) : Result (Option M) :=
  if l≤idx.cut && idx.cut≤r && r≤idx.len then
    match idx.leftSuffix[l]?,idx.rightPrefix[r-idx.cut]? with
    | some a,some b=>let p:=k.multiply a b; (some p.1,p.2+10)
    | _,_=>(none,10)
  else (none,5)

theorem crossing_value (k : ProductOps o) (idx : RangeProducts.CutIndex M) (l r : Nat) :
    (crossing k idx l r).1=RangeProducts.queryCut o idx l r := by
  unfold crossing RangeProducts.queryCut
  split
  · cases ha : idx.leftSuffix[l]? <;> cases hb : idx.rightPrefix[r-idx.cut]? <;>
      simp only [ha,hb,Option.bind,Option.map,k.multiply_value]
  · rfl

theorem crossing_work (k : ProductOps o) (idx : RangeProducts.CutIndex M) (l r : Nat)
    (C : Nat) (hm : ∀a b,(k.multiply a b).2≤C) : (crossing k idx l r).2≤C+10 := by
  unfold crossing
  split
  · split
    · exact Nat.add_le_add_right (hm _ _) 10
    · omega
  · omega

def rangeQuery (k : ProductOps o) : DyadicIndex.Tree M→Nat→Nat→Result (DyadicIndex.Result M)
  | .leaf xs,l,r=>
    let s:=sliced xs l r
    let p:=product k s.1
    (⟨some p.1.1,p.1.2,1⟩,s.2+p.2+3)
  | .node row left right,l,r=>
    if r≤row.cut then
      let q:=rangeQuery k left l r
      (q.1.bump,q.2+4)
    else if row.cut≤l then
      let q:=rangeQuery k right (l-row.cut) (r-row.cut)
      (q.1.bump,q.2+6)
    else
      let q:=crossing k row l r
      (⟨q.1,1,1⟩,q.2+6)

theorem rangeQuery_value (k : ProductOps o) (idx : DyadicIndex.Tree M) (l r : Nat) :
    (rangeQuery k idx l r).1=DyadicIndex.query o idx l r := by
  induction idx generalizing l r with
  | leaf xs=>simp only [rangeQuery,product_value,sliced_value,DyadicIndex.query]
  | node row left right ihl ihr=>
    simp only [rangeQuery,DyadicIndex.query]
    split
    · simp only [ihl]
    · split
      · simp only [ihr]
      · simp only [crossing_value]

def Tiny : DyadicIndex.Tree M→Prop
  | .leaf xs=>xs.length≤1
  | .node _ a b=>Tiny a ∧ Tiny b

theorem rangeQuery_work (k : ProductOps o) (idx : DyadicIndex.Tree M) (l r : Nat)
    (C : Nat) (hu : k.unit.2≤C) (hm : ∀a b,(k.multiply a b).2≤C) (ht : Tiny idx) :
    (rangeQuery k idx l r).2≤
      (2*C+20)*((DyadicIndex.query o idx l r).products+(DyadicIndex.query o idx l r).visits) := by
  induction idx generalizing l r with
  | leaf xs=>
    have hs:=sliced_work xs l r
    have hp:=product_work k (sliced xs l r).1 C hu hm
    have hn : (sliced xs l r).1.length≤1 := by
      rw [sliced_value]
      simp only [Spec.slice,List.length_take,List.length_drop]
      exact Nat.le_trans (Nat.min_le_right _ _) (Nat.le_trans (Nat.sub_le _ _) ht)
    have hmul:=Nat.mul_le_mul_right (C+3) hn
    have hpos : 1≤(Spec.slice xs l r).length+1 := by omega
    have hbig:=Nat.mul_le_mul_left (2*C+20) hpos
    change (sliced xs l r).2+(product k (sliced xs l r).1).2+3≤_
    change xs.length≤1 at ht
    simp only [DyadicIndex.query,Nat.mul_one] at hmul hbig ⊢
    omega
  | node row a b ia ib=>
    rcases ht with ⟨hta,htb⟩
    simp only [rangeQuery,DyadicIndex.query]
    split
    · have h:=ia l r hta
      simp only [DyadicIndex.Result.bump,Nat.mul_add,Nat.mul_one] at *
      omega
    · split
      · have h:=ib (l-row.cut) (r-row.cut) htb
        simp only [DyadicIndex.Result.bump,Nat.mul_add,Nat.mul_one] at *
        omega
      · have h:=crossing_work k row l r C hm
        dsimp only
        omega

theorem build_tiny (o : RangeProducts.Ops M) (h : Nat) (xs : List M)
    (hc : xs.length≤2^h) : Tiny (DyadicIndex.build o h xs).1 := by
  induction h generalizing xs with
  | zero=>simpa only [DyadicIndex.build,Tiny,Nat.pow_zero] using hc
  | succ h ih=>
    constructor
    · apply ih
      simp only [List.length_take]
      exact Nat.min_le_left _ _
    · apply ih
      simp only [List.length_drop]
      rw [Nat.pow_succ] at hc
      omega

theorem buildFor_tiny (o : RangeProducts.Ops M) (xs : List M) :
    Tiny (DyadicIndex.buildFor o xs).1 := build_tiny o _ xs (DyadicIndex.capacity xs.length)

def summaryProducts {M : Type} [DecidableEq M] {o : RangeProducts.Ops M}
    {e : FiniteRelation.Enumeration M} (k : Primitives o) (u : Universe e) :
    ProductOps (MaskedCut.ops o e) where
  unit:=summaryOne k u
  multiply:=summaryMul k u
  unit_value:=summaryOne_value k u
  multiply_value:=summaryMul_value k u

def summaryCost (N C : Nat) : Nat := oneCost N C+mulCost N C

theorem summaryProducts_unit {M : Type} [DecidableEq M] {o : RangeProducts.Ops M}
    {e : FiniteRelation.Enumeration M} (k : Primitives o) (u : Universe e) (C : Nat)
    (hu : k.unit.2≤C) :
    (summaryProducts k u).unit.2≤summaryCost e.elems.length C := by
  have h:=summaryOne_work k u C hu
  exact Nat.le_trans h (Nat.le_add_right _ _)

theorem summaryProducts_mul {M : Type} [DecidableEq M] {o : RangeProducts.Ops M}
    {e : FiniteRelation.Enumeration M} (k : Primitives o) (u : Universe e) (C : Nat)
    (hm : ∀a b,(k.multiply a b).2≤C) (he : ∀a b,(k.equal a b).2≤C)
    (a b : MaskedCut.Summary e) :
    ((summaryProducts k u).multiply a b).2≤summaryCost e.elems.length C := by
  have h:=summaryMul_work k u a b C hm he
  exact Nat.le_trans h (Nat.le_add_left _ _)

end REWB.PeriodicConstruction.Cut
