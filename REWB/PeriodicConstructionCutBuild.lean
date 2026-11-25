import REWB.PeriodicConstructionCutQuery

/-! Actual substitution of finite products in the dyadic construction.
Prefix/suffix materialization, splitting, array conversion and the full
binary shape are included. The returned old product counter is retained
separately from the structural-operation counter. -/
namespace REWB.PeriodicConstruction.Cut
variable {M : Type} {o : RangeProducts.Ops M}

def prefixScan (k : ProductOps o) (acc : M) : List M→Result (List M×Nat)
  | []=>(([acc],0),1)
  | x::xs=>
    let step:=k.multiply acc x
    let tail:=prefixScan k step.1 xs
    ((acc::tail.1.1,tail.1.2+1),step.2+tail.2+3)

theorem prefix_value (k : ProductOps o) (acc : M) (xs : List M) :
    (prefixScan k acc xs).1=RangeProducts.prefixScan o acc xs := by
  induction xs generalizing acc with
  | nil=>rfl
  | cons x xs ih=>simp only [prefixScan,ih,k.multiply_value,RangeProducts.prefixScan]

theorem prefix_work (k : ProductOps o) (acc : M) (xs : List M) (C : Nat)
    (hm : ∀a b,(k.multiply a b).2≤C) :
    (prefixScan k acc xs).2≤xs.length*(C+3)+1 := by
  induction xs generalizing acc with
  | nil=>simp [prefixScan]
  | cons x xs ih=>
    have ht:=ih (k.multiply acc x).1
    have hs:=hm acc x
    simp only [prefixScan,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

def suffix (k : ProductOps o) : List M→Result (M×List M×Nat)
  | []=>((k.unit.1,[k.unit.1],0),k.unit.2+2)
  | x::xs=>
    let tail:=suffix k xs
    let step:=k.multiply x tail.1.1
    ((step.1,step.1::tail.1.2.1,tail.1.2.2+1),tail.2+step.2+3)

theorem suffix_value (k : ProductOps o) (xs : List M) :
    (suffix k xs).1=RangeProducts.suffixScan o xs := by
  induction xs with
  | nil=>simp only [suffix,k.unit_value,RangeProducts.suffixScan]
  | cons x xs ih=>simp only [suffix,ih,k.multiply_value,RangeProducts.suffixScan]

theorem suffix_work (k : ProductOps o) (xs : List M) (C : Nat)
    (hu : k.unit.2≤C) (hm : ∀a b,(k.multiply a b).2≤C) :
    (suffix k xs).2≤xs.length*(C+3)+C+2 := by
  induction xs with
  | nil=>simp only [suffix,List.length_nil,Nat.zero_mul,Nat.zero_add]; omega
  | cons x xs ih=>
    have hs:=hm x (suffix k xs).1.1
    simp only [suffix,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

def buildCut (k : ProductOps o) (left right : List M) : Result (RangeProducts.CutIndex M×Nat) :=
  let l:=suffix k left
  let r:=prefixScan k k.unit.1 right
  let sizeL:=l.1.2.2
  let sizeR:=r.1.2
  ((⟨sizeL,sizeL+sizeR,l.1.2.1.toArray,r.1.1.toArray⟩,sizeL+sizeR),
    l.2+r.2+k.unit.2+sizeL+sizeR+7)

theorem buildCut_value (k : ProductOps o) (left right : List M) :
    (buildCut k left right).1=RangeProducts.buildCut o left right := by
  simp only [buildCut,prefix_value,suffix_value,k.unit_value,RangeProducts.prefix_cost,
    RangeProducts.suffix_cost,RangeProducts.buildCut]

theorem buildCut_work (k : ProductOps o) (left right : List M) (C : Nat)
    (hu : k.unit.2≤C) (hm : ∀a b,(k.multiply a b).2≤C) :
    (buildCut k left right).2≤(left.length+right.length)*(C+4)+2*C+10 := by
  have hl:=suffix_work k left C hu hm
  have hr:=prefix_work k k.unit.1 right C hm
  simp only [buildCut,prefix_value,suffix_value,RangeProducts.prefix_cost,
    RangeProducts.suffix_cost,Nat.add_mul,Nat.mul_add]
  simp only [Nat.mul_add] at hl hr
  omega

def power : Nat→Result Nat
  | 0=>(1,1)
  | h+1=>let p:=power h; (2*p.1,p.2+2)

theorem power_value (h : Nat) : (power h).1=2^h := by
  induction h with
  | zero=>rfl
  | succ h ih=>simp only [power,ih,Nat.pow_succ,Nat.mul_comm]

theorem power_work (h : Nat) : (power h).2=2*h+1 := by
  induction h with
  | zero=>rfl
  | succ h ih=>simp only [power,ih,Nat.mul_add,Nat.mul_one]

def build (k : ProductOps o) : Nat→List M→Result (DyadicIndex.Tree M×Nat)
  | 0,xs=>((.leaf xs,0),1)
  | h+1,xs=>
    let p:=power h
    let parts:=split p.1 xs
    let row:=buildCut k parts.1.1 parts.1.2
    let left:=build k h parts.1.1
    let right:=build k h parts.1.2
    ((.node row.1.1 left.1.1 right.1.1,row.1.2+left.1.2+right.1.2),
      p.2+parts.2+row.2+left.2+right.2+4)

theorem build_value (k : ProductOps o) (h : Nat) (xs : List M) :
    (build k h xs).1=DyadicIndex.build o h xs := by
  induction h generalizing xs with
  | zero=>rfl
  | succ h ih=>simp only [build,ih,power_value,split_value,buildCut_value,DyadicIndex.build]

theorem power_large (h : Nat) : h+1≤2^h := by
  induction h with
  | zero=>exact Nat.le_refl _
  | succ h ih=>rw [Nat.pow_succ]; omega

theorem build_work (k : ProductOps o) (h : Nat) (xs : List M) (C : Nat)
    (hu : k.unit.2≤C) (hm : ∀a b,(k.multiply a b).2≤C) :
    (build k h xs).2≤(C+20)*(h+1)*(xs.length+2^(h+1)) := by
  induction h generalizing xs with
  | zero=>
    simp only [build,Nat.zero_add,Nat.mul_one,Nat.pow_one,Nat.add_mul,Nat.mul_add,Nat.mul_one]
    omega
  | succ h ih=>
    let parts:=split (power h).1 xs
    have hlen : parts.1.1.length+parts.1.2.length=xs.length := by
      simp only [parts,split_value,List.length_take,List.length_drop]
      omega
    have hl:=ih parts.1.1
    have hr:=ih parts.1.2
    have hb:=buildCut_work k parts.1.1 parts.1.2 C hu hm
    have hs:=split_work (power h).1 xs
    have hp:=power_work h
    have hlarge:=power_large (h+1)
    have htwo : 2≤2^(h+1+1) := by rw [Nat.pow_succ]; have := Nat.two_pow_pos (h+1); omega
    have hc:=Nat.mul_le_mul_left C htwo
    have hh : 2*h+15≤20*2^(h+1+1) := by rw [Nat.pow_succ]; omega
    have hnode : (power h).2+parts.2+(buildCut k parts.1.1 parts.1.2).2+4≤
        (C+20)*(xs.length+2^(h+1+1)) := by
      rw [hlen] at hb
      dsimp only [parts] at *
      have hb' : (buildCut k (split (power h).1 xs).1.1 (split (power h).1 xs).1.2).2≤
          C*xs.length+4*xs.length+2*C+10 := by
        simpa only [Nat.mul_add,Nat.mul_comm] using hb
      simp only [Nat.add_mul,Nat.mul_add,Nat.mul_one] at hc ⊢
      omega
    have he : (C+20)*(h+1)*(parts.1.1.length+2^(h+1))+
        (C+20)*(h+1)*(parts.1.2.length+2^(h+1))=
        (C+20)*(h+1)*(xs.length+2^(h+1+1)) := by
      rw [← Nat.mul_add]
      have hx : parts.1.1.length+2^(h+1)+ (parts.1.2.length+2^(h+1))=
          xs.length+2^(h+1+1) := by rw [Nat.pow_succ]; omega
      rw [hx]
    have hchildren:=Nat.add_le_add hl hr
    rw [he] at hchildren
    have ht:=Nat.add_le_add hnode hchildren
    change (power h).2+parts.2+(buildCut k parts.1.1 parts.1.2).2+
      (build k h parts.1.1).2+(build k h parts.1.2).2+4≤_
    have hbnd : (C+20)*(h+1+1)*(xs.length+2^(h+1+1))=
      (C+20)*(xs.length+2^(h+1+1))+
      (C+20)*(h+1)*(xs.length+2^(h+1+1)) := by
      simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one]
      omega
    rw [hbnd]
    omega

def lengthCount : List M→Result Nat
  | []=>(0,1)
  | _::xs=>let r:=lengthCount xs; (r.1+1,r.2+2)

theorem lengthCount_value (xs : List M) : (lengthCount xs).1=xs.length := by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>simp only [lengthCount,ih,List.length_cons]

theorem lengthCount_work (xs : List M) : (lengthCount xs).2=2*xs.length+1 := by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>simp only [lengthCount,ih,List.length_cons,Nat.mul_add,Nat.mul_one]

def logarithm (n : Nat) : Result Nat :=
  if h : 2≤n then
    let r:=logarithm (n/2)
    (r.1+1,r.2+3)
  else (0,1)
termination_by n
decreasing_by exact Nat.log2_terminates n h

theorem logarithm_value (n : Nat) : (logarithm n).1=n.log2 := by
  unfold logarithm Nat.log2
  split
  · dsimp only
    rw [logarithm_value]
  · rfl
termination_by n
decreasing_by exact Nat.log2_terminates n (by assumption)

theorem logarithm_work (n : Nat) : (logarithm n).2=3*n.log2+1 := by
  unfold logarithm Nat.log2
  split
  · dsimp only
    rw [logarithm_work]
    omega
  · rfl
termination_by n
decreasing_by exact Nat.log2_terminates n (by assumption)

def buildFor (k : ProductOps o) (xs : List M) : Result (DyadicIndex.Tree M×Nat) :=
  let n:=lengthCount xs
  let h:=logarithm n.1
  let tree:=build k (h.1+1) xs
  (tree.1,n.2+h.2+tree.2+3)

theorem buildFor_value (k : ProductOps o) (xs : List M) :
    (buildFor k xs).1=DyadicIndex.buildFor o xs := by
  simp only [buildFor,build_value,lengthCount_value,logarithm_value,DyadicIndex.buildFor,DyadicIndex.heightFor]

theorem pow_log_bound (n : Nat) : 2^(n.log2+1+1)≤4*(n+1) := by
  by_cases hn : n=0
  · subst n; simp only [Nat.log2_zero]; decide
  · have h:=Nat.log2_self_le hn
    simp only [Nat.pow_succ]
    omega

def buildCost (C n : Nat) : Nat := 6*(C+20)*(n+1)*(n.log2+2)

theorem buildFor_work (k : ProductOps o) (xs : List M) (C : Nat)
    (hu : k.unit.2≤C) (hm : ∀a b,(k.multiply a b).2≤C) :
    (buildFor k xs).2≤buildCost C xs.length := by
  have hb:=build_work k (xs.length.log2+1) xs C hu hm
  have hp:=pow_log_bound xs.length
  have hl:=Nat.log2_le_self xs.length
  have hn : xs.length+2^(xs.length.log2+1+1)≤5*(xs.length+1) := by omega
  have hm1:=Nat.mul_le_mul_left ((C+20)*(xs.length.log2+1+1)) hn
  have he1 : (C+20)*(xs.length.log2+1+1)*(5*(xs.length+1))=
      5*((C+20)*(xs.length+1)*(xs.length.log2+2)) := by
    have hh : xs.length.log2+1+1=xs.length.log2+2 := by omega
    rw [hh]
    ac_rfl
  rw [he1] at hm1
  have hb':=(Nat.le_trans hb hm1)
  have hmin : 20*(xs.length+1)≤(C+20)*(xs.length+1)*(xs.length.log2+2) := by
    have h1:=Nat.mul_le_mul_right (xs.length+1) (show 20≤C+20 by omega)
    have h2:=Nat.mul_le_mul_left ((C+20)*(xs.length+1))
      (show 1≤xs.length.log2+2 by omega)
    simp only [Nat.mul_one] at h2
    exact Nat.le_trans h1 h2
  simp only [buildFor,lengthCount_value,lengthCount_work,logarithm_value,logarithm_work,buildCost]
  have he2 : 6*(C+20)*(xs.length+1)*(xs.length.log2+2)=
      6*((C+20)*(xs.length+1)*(xs.length.log2+2)) := by ac_rfl
  rw [he2]
  omega

open REWB.MaskedCut.DFAIndex

def buildDFA (B C E : DFA α) (w : Word α) : Result (MaskedCut.Index.Tree (jointEnum B C E)×Nat) :=
  let env:=prepare B C E
  let maps:=letters B C E w
  let atoms:=CountedProjection.map (summaryAtom env.1.kernel env.1.catalog) maps.1
  let algebra:=summaryProducts env.1.kernel env.1.catalog
  let tree:=buildFor algebra atoms.1
  (tree.1,env.2+maps.2+atoms.2+algebra.unit.2+tree.2+5)

theorem buildDFA_value (B C E : DFA α) (w : Word α) :
    (buildDFA B C E w).1=MaskedCut.DFAIndex.build B C E w := by
  simp only [buildDFA,buildFor_value,CountedProjection.map_value,summaryAtom_value,letters_value,
    MaskedCut.DFAIndex.build,MaskedCut.Index.build]

def buildDFACost (b c e n : Nat) : Nat :=
  prepareCost b c e+n*(primitiveCost b c e+1)+
    n*(atomCost (cardinality b c e) (primitiveCost b c e)+1)+
    oneCost (cardinality b c e) (primitiveCost b c e)+
    buildCost (summaryCost (cardinality b c e) (primitiveCost b c e)) n+7

theorem buildDFA_work (B C E : DFA α) (w : Word α) :
    (buildDFA B C E w).2≤buildDFACost B.stateCount C.stateCount E.stateCount w.length := by
  have hp:=prepare_work B C E
  have hl:=letters_work B C E w
  have hu:=summaryOne_work (prepare B C E).1.kernel (prepare B C E).1.catalog
    (primitiveCost B.stateCount C.stateCount E.stateCount) (primitives_unit B C E)
  rw [enum_cardinality] at hu
  have ha:=map_bound (summaryAtom (prepare B C E).1.kernel (prepare B C E).1.catalog)
    (letters B C E w).1
    (atomCost (jointEnum B C E).elems.length (primitiveCost B.stateCount C.stateCount E.stateCount))
    (fun x _=>summaryAtom_work _ _ x _ (primitives_unit B C E) (primitives_equal B C E))
  have hb:=buildFor_work (summaryProducts (prepare B C E).1.kernel (prepare B C E).1.catalog)
    (CountedProjection.map (summaryAtom (prepare B C E).1.kernel (prepare B C E).1.catalog)
      (letters B C E w).1).1
    (summaryCost (jointEnum B C E).elems.length (primitiveCost B.stateCount C.stateCount E.stateCount))
    (summaryProducts_unit _ _ _ (primitives_unit B C E))
    (summaryProducts_mul _ _ _ (primitives_mul B C E) (primitives_equal B C E))
  have hlen : (letters B C E w).1.length=w.length := by rw [letters_value,MaskedCut.DFAIndex.letters_length]
  have hlen2 : (CountedProjection.map (summaryAtom (prepare B C E).1.kernel (prepare B C E).1.catalog)
      (letters B C E w).1).1.length=w.length := by
    simp only [CountedProjection.map_value,List.length_map,hlen]
  rw [hlen,enum_cardinality] at ha
  rw [hlen2,enum_cardinality] at hb
  dsimp only [buildDFA,buildDFACost,summaryProducts]
  omega

end REWB.PeriodicConstruction.Cut
