import REWB.MaskedClusterBank
import REWB.BoundaryRangeTable
import REWB.CountedProjection

/-! Measured construction of the fixed-pattern replay catalog and lazy
action maps. The list enumeration, index lookup, composition, encoding
and materialization paths have explicit counters. Enumeration work is a
function of the two DFA state counts only. Vector equality is charged
by its full fixed-state length, including the pair and array headers.
No text length, run period, source position or answer predicate enters
the construction budgets. -/
namespace REWB.MaskedFiniteConstruction
open REWB.MaskedFiniteAction REWB.MaskedCluster
abbrev Result (X : Type) := X×Nat

def vectors (m : Nat) : (n : Nat)→Result (List (Vector (Fin m) n))
  | 0=>([#v[]],1)
  | n+1=>
    let smaller:=vectors m n
    let symbols:=List.ofFn (fun x : Fin m=>x)
    let out:=CountedProjection.flatMap
      (fun v=>CountedProjection.map (fun x=>(v.push x,n+2)) symbols) smaller.1
    (out.1,smaller.2+m+out.2+3)

theorem vectors_value (m n : Nat) : (vectors m n).1=Maps.vectors m n := by
  induction n with
  | zero=>rfl
  | succ n ih=>
    simp only [vectors,CountedProjection.flatMap_value,CountedProjection.map_value,ih,Maps.vectors]

def enumeration (c e : Nat) : Result (List (ReplayMaps.Value c e)) :=
  let left:=vectors c c
  let right:=vectors e e
  let pairs:=CountedProjection.flatMap
    (fun a=>CountedProjection.map (fun b=>((a,b),1)) right.1) left.1
  (pairs.1,left.2+right.2+pairs.2+2)

theorem enumeration_value (c e : Nat) :
    (enumeration c e).1=(ReplayMaps.enumeration c e).elems := by
  simp only [enumeration,CountedProjection.flatMap_value,CountedProjection.map_value,vectors_value,
    ReplayMaps.enumeration,MaskedCut.DFAIndex.prodEnum,MaskedCut.DFAIndex.mapEnum,Maps.allMaps]

def lookup (fallback : X) : List X→Nat→Result X
  | [],_=>(fallback,1)
  | x::_,0=>(x,1)
  | _::xs,i+1=>let tail:=lookup fallback xs i; (tail.1,tail.2+1)

theorem lookup_value (fallback : X) (xs : List X) (i : Nat) :
    (lookup fallback xs i).1=xs[i]?.getD fallback := by
  induction xs generalizing i with
  | nil=>rfl
  | cons x xs ih=>
    cases i with
    | zero=>rfl
    | succ i=>simpa only [lookup,List.getElem?_cons_succ] using ih i

theorem lookup_work (fallback : X) (xs : List X) (i : Nat) :
    (lookup fallback xs i).2≤xs.length+1 := by
  induction xs generalizing i with
  | nil=>exact Nat.le_refl _
  | cons x xs ih=>
    cases i with
    | zero=>simp only [lookup,List.length_cons]; omega
    | succ i=>have hh:=ih i; simp only [lookup,List.length_cons]; omega

def index [BEq X] (comparison : Nat) (x : X) : List X→Result Nat
  | []=>(0,1)
  | a::xs=>if a==x then (0,comparison+1)
    else let tail:=index comparison x xs; (tail.1+1,tail.2+comparison+1)

theorem index_value [BEq X] (comparison : Nat) (x : X) (xs : List X) :
    (index comparison x xs).1=xs.idxOf x := by
  induction xs with
  | nil=>rfl
  | cons a xs ih=>
    simp only [index,List.idxOf_cons]
    split <;> simp_all

theorem index_work [BEq X] (comparison : Nat) (x : X) (xs : List X) :
    (index comparison x xs).2≤xs.length*(comparison+1)+1 := by
  induction xs with
  | nil=>simp only [index,List.length_nil,Nat.zero_mul,Nat.zero_add,Nat.le_refl]
  | cons a xs ih=>
    simp only [index,List.length_cons,Nat.add_mul,Nat.one_mul]
    split <;> dsimp only <;> omega

def decode (c e : Nat) (i : Fin (ReplayMaps.count c e)) : Result (ReplayMaps.Value c e) :=
  let values:=enumeration c e
  let found:=lookup (ReplayMaps.one c e) values.1 i.val
  (found.1,values.2+found.2+2)

theorem decode_value (c e : Nat) (i : Fin (ReplayMaps.count c e)) :
    (decode c e i).1=ReplayMaps.decode c e i := by
  simp only [decode,lookup_value,enumeration_value,ReplayMaps.decode]

def decodeBudget (c e : Nat) : Nat := (enumeration c e).2+ReplayMaps.count c e+3

theorem decode_work (c e : Nat) (i : Fin (ReplayMaps.count c e)) :
    (decode c e i).2≤decodeBudget c e := by
  have hh:=lookup_work (ReplayMaps.one c e) (enumeration c e).1 i.val
  have hn : (enumeration c e).1.length=ReplayMaps.count c e := by rw [enumeration_value]; rfl
  rw [hn] at hh
  unfold decode decodeBudget
  dsimp only
  omega

def equalityBudget (c e : Nat) : Nat := 2*c+2*e+5

def encode {c e : Nat} (value : ReplayMaps.Value c e) : Result (Fin (ReplayMaps.count c e)) :=
  let values:=enumeration c e
  let found:=index (equalityBudget c e) value values.1
  (⟨found.1,by
    change (index (equalityBudget c e) value (enumeration c e).1).1<ReplayMaps.count c e
    rw [index_value,enumeration_value]
    exact List.idxOf_lt_length ((ReplayMaps.enumeration c e).complete value)⟩,
    values.2+found.2+2)

theorem encode_value {c e : Nat} (value : ReplayMaps.Value c e) :
    (encode value).1=ReplayMaps.encode value := by
  apply Fin.ext
  simp only [encode,index_value,enumeration_value,ReplayMaps.encode]

def encodeBudget (c e : Nat) : Nat :=
  (enumeration c e).2+ReplayMaps.count c e*(equalityBudget c e+1)+3

theorem encode_work {c e : Nat} (value : ReplayMaps.Value c e) :
    (encode value).2≤encodeBudget c e := by
  have hh:=index_work (equalityBudget c e) value (enumeration c e).1
  have hn : (enumeration c e).1.length=ReplayMaps.count c e := by rw [enumeration_value]; rfl
  rw [hn] at hh
  dsimp only [encode,encodeBudget]
  omega

def rightAction {c e : Nat} (z : ReplayMaps.Value c e) :
    Result (Vector (Fin (ReplayMaps.count c e)) (ReplayMaps.count c e)) :=
  let rows:=BoundaryRange.Table.build fun i : Fin (ReplayMaps.count c e)=>
    let decoded:=decode c e i
    let composed:=ReplayMaps.mulCounted decoded.1 z
    let encoded:=encode composed.1
    (encoded.1,decoded.2+composed.2+encoded.2+3)
  (Vector.ofFn (BoundaryRange.Table.get rows),rows.work+ReplayMaps.count c e+2)

theorem rightAction_value {c e : Nat} (z : ReplayMaps.Value c e) :
    (rightAction z).1=ReplayMaps.rightAction z := by
  apply Vector.ext
  intro i hi
  change (rightAction z).1.get ⟨i,hi⟩=(ReplayMaps.rightAction z).get ⟨i,hi⟩
  simp only [rightAction,BoundaryRange.Table.vector_get_ofFn,BoundaryRange.Table.get_build,
    encode_value,ReplayMaps.mulCounted_value,decode_value,ReplayMaps.rightAction_get]

def actionBudget (c e : Nat) : Nat :=
  ReplayMaps.count c e*(decodeBudget c e+(c+e)+encodeBudget c e+6)+1+ReplayMaps.count c e+2

theorem rightAction_work {c e : Nat} (z : ReplayMaps.Value c e) :
    (rightAction z).2≤actionBudget c e := by
  have hh:=BoundaryRange.Table.build_work_le
    (fun i : Fin (ReplayMaps.count c e)=>
      let decoded:=decode c e i
      let composed:=ReplayMaps.mulCounted decoded.1 z
      let encoded:=encode composed.1
      (encoded.1,decoded.2+composed.2+encoded.2+3))
    (decodeBudget c e+(c+e)+encodeBudget c e+3) (by
      intro i
      have hd:=decode_work c e i
      have he:=encode_work (ReplayMaps.mulCounted (decode c e i).1 z).1
      simp only [ReplayMaps.mulCounted_steps]
      omega)
  dsimp only at hh
  dsimp only [rightAction,actionBudget]
  simp only [Nat.add_assoc,Nat.reduceAdd] at hh ⊢
  omega

def bankAction {c e : Nat} (z : ReplayMaps.Value c e) :
    Result (Vector (Fin (2*ReplayMaps.count c e)) (2*ReplayMaps.count c e)) :=
  let action:=rightAction z
  let rows:=BoundaryRange.Table.build fun key : Fin (2*ReplayMaps.count c e)=>
    (MaskedCluster.code (ReplayMaps.count c e) (codeMode _ key) (action.1.get (codeState _ key)),6)
  (Vector.ofFn (BoundaryRange.Table.get rows),action.2+rows.work+2*ReplayMaps.count c e+2)

theorem bankAction_value {c e : Nat} (z : ReplayMaps.Value c e) :
    (bankAction z).1=MaskedCluster.bankAction z := by
  apply Vector.ext
  intro i hi
  change (bankAction z).1.get ⟨i,hi⟩=(MaskedCluster.bankAction z).get ⟨i,hi⟩
  simp only [bankAction,BoundaryRange.Table.vector_get_ofFn,BoundaryRange.Table.get_build,
    rightAction_value,MaskedCluster.bankAction_get]

def bankActionBudget (c e : Nat) : Nat := actionBudget c e+20*ReplayMaps.count c e+3

theorem bankAction_work {c e : Nat} (z : ReplayMaps.Value c e) :
    (bankAction z).2≤bankActionBudget c e := by
  have ha:=rightAction_work z
  have hh:=BoundaryRange.Table.build_work_le
    (fun key : Fin (2*ReplayMaps.count c e)=>
      (MaskedCluster.code (ReplayMaps.count c e) (codeMode _ key) ((rightAction z).1.get (codeState _ key)),6)) 6
    (fun _=>Nat.le_refl _)
  dsimp only [bankAction,bankActionBudget]
  simp only [Nat.mul_assoc] at hh
  omega

def prepare (c e : Nat) : Result (ReplayMaps.Prepared c e) :=
  let rows:=BoundaryRange.Table.build (decode c e)
  let values:=Vector.ofFn (BoundaryRange.Table.get rows)
  (⟨values,by
      intro i
      simp only [values,rows,BoundaryRange.Table.vector_get_ofFn,BoundaryRange.Table.get_build,decode_value]⟩,
    rows.work+ReplayMaps.count c e+2)

theorem prepared_ext {c e : Nat} (a b : ReplayMaps.Prepared c e) (hv : a.values=b.values) : a=b := by
  cases a
  cases b
  cases hv
  rfl

theorem prepare_value (c e : Nat) : (prepare c e).1=ReplayMaps.prepare c e := by
  apply prepared_ext
  apply Vector.ext
  intro i hi
  change (prepare c e).1.values.get ⟨i,hi⟩=(ReplayMaps.prepare c e).values.get ⟨i,hi⟩
  simp only [prepare,BoundaryRange.Table.vector_get_ofFn,BoundaryRange.Table.get_build,decode_value,
    ReplayMaps.prepare,ReplayMaps.catalog_get]

def prepareBudget (c e : Nat) : Nat :=
  ReplayMaps.count c e*(decodeBudget c e+3)+1+ReplayMaps.count c e+2

theorem prepare_work (c e : Nat) : (prepare c e).2≤prepareBudget c e := by
  have hh:=BoundaryRange.Table.build_work_le (decode c e) (decodeBudget c e) (decode_work c e)
  dsimp only [prepare,prepareBudget]
  omega

/-- This coefficient pays for either a catalog construction or one
lifted action construction. It depends only on fixed pattern states. -/
def fixedBudget (c e : Nat) : Nat := prepareBudget c e+bankActionBudget c e+1

theorem prepare_fixed (c e : Nat) : (prepare c e).2≤fixedBudget c e :=
  Nat.le_trans (prepare_work c e) (by unfold fixedBudget; omega)

theorem bankAction_fixed {c e : Nat} (z : ReplayMaps.Value c e) :
    (bankAction z).2≤fixedBudget c e :=
  Nat.le_trans (bankAction_work z) (by unfold fixedBudget; omega)

end REWB.MaskedFiniteConstruction
