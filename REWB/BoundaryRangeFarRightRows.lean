import REWB.BoundaryRangeFarRightRequests
import REWB.BoundaryIndexCounted

/-! Materialized finite-state unions of the pending all-start outputs.
Each endpoint examines every K state once; the output is an immutable
array, with no lookup closures or delayed row reconstruction. -/
namespace REWB.BoundaryRange.FarRight
open REWB.OneUseRange REWB.BoundaryIndex
variable {σ : Nat}

def unionPoint {m : Nat} (rows : Vector (Array Bool) m) (states : List (Fin m)) (y : Nat) : Bool×Nat :=
  let out:=Counted.scan (fun k=>FarAggregate.bit (rows.get k) y) states
  (out.1,6*out.2+1)

theorem unionPoint_correct {m : Nat} (rows : Vector (Array Bool) m) (states : List (Fin m)) (y : Nat) :
    (unionPoint rows states y).1=true ↔ ∃k,k∈states ∧ FarAggregate.bit (rows.get k) y=true := by
  simp only [unionPoint,Counted.scan_value,List.any_eq_true]

theorem unionPoint_work {m : Nat} (rows : Vector (Array Bool) m) (states : List (Fin m)) (y : Nat) :
    (unionPoint rows states y).2=6*states.length+1 := by simp only [unionPoint,Counted.scan_steps]

structure Union where
  bits : Array Bool
  work : Nat

def unionRow (K : DFA (Fin σ)) (n : Nat) (rows : Vector (Array Bool) K.stateCount) : Union :=
  let states:=List.finRange K.stateCount
  let answers:=Vector.ofFn fun y : Fin (n+1)=>unionPoint rows states y.val
  ⟨(answers.map Prod.fst).toArray,Counted.rowWork answers+3*(n+1)+2*K.stateCount+3⟩

theorem unionRow_correct (K : DFA (Fin σ)) (n : Nat) (rows : Vector (Array Bool) K.stateCount)
    (y : Nat) (hy : y≤n) :
    FarAggregate.bit (unionRow K n rows).bits y=true ↔ ∃k,FarAggregate.bit (rows.get k) y=true := by
  unfold FarAggregate.bit unionRow
  have hlt : y<n+1 := by omega
  rw [Array.getElem?_eq_getElem (by simpa using hlt)]
  change ((Vector.ofFn fun z : Fin (n+1)=>unionPoint rows (List.finRange K.stateCount) z.val).map Prod.fst).get ⟨y,hlt⟩=true ↔ _
  simp only [Vector.get,Vector.toArray_map,Vector.toArray_ofFn,Array.getElem_map,Array.getElem_ofFn]
  rw [unionPoint_correct]
  simp only [List.finRange,List.mem_ofFn,exists_eq,true_and]
  rfl

def unionBudget (K : DFA (Fin σ)) (n : Nat) : Nat := (n+1)*(6*K.stateCount+2)+3*(n+1)+2*K.stateCount+3

theorem unionRow_work (K : DFA (Fin σ)) (n : Nat) (rows : Vector (Array Bool) K.stateCount) :
    (unionRow K n rows).work=unionBudget K n := by
  have hh:=Counted.rowWork_uniform
    (Vector.ofFn fun y : Fin (n+1)=>unionPoint rows (List.finRange K.stateCount) y.val)
    (6*K.stateCount+1) (by intro i; simp only [BoundaryIndex.Table.get_ofFn,unionPoint_work,List.length_finRange])
  unfold unionRow unionBudget
  dsimp only
  rw [hh]

end REWB.BoundaryRange.FarRight
