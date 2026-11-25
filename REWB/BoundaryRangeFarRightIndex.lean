import REWB.BoundaryRangeFarRightRows

/-! The far-right cache is finished from the finite output rows of the
materialized mask requests. A backwards E aggregate is built once for
each K entry state. Online queries make one K range query and one
bounded aggregate-array read. -/
namespace REWB.BoundaryRange.FarRight
open REWB.BoundaryApplication REWB.OneUseRange
variable {σ : Nat}

structure Index (K : DFA (Fin σ)) where
  ranges : Range.Index K
  rows : Table.Index (fun _ : Fin K.stateCount=>FarAggregate.Index)
  grid : Nat
  length : Nat
  work : Nat

def assemble (K E : DFA (Fin σ)) (w : Word (Fin σ)) (requests : Requests K w) (bits : Input K) : Index K :=
  let reversed:=w.reverse.toArray
  let reverseE:=Automata.reverse E
  let rows:=Table.build fun q : Fin K.stateCount=>
    let joined:=unionRow K requests.length (bits.get q)
    let aggregate:=FarAggregate.build reverseE reversed joined.bits
    (aggregate,joined.work+aggregate.work+3)
  ⟨requests.ranges,rows,requests.grid,requests.length,requests.work+rows.work+2*requests.length+9⟩

def build (K E : DFA (Fin σ)) (w : Word (Fin σ)) (grid : Nat) (bits : Input K) : Index K :=
  assemble K E w (prepare K w grid) bits

@[simp] theorem build_get (K E : DFA (Fin σ)) (w : Word (Fin σ)) (grid : Nat) (bits : Input K)
    (q : Fin K.stateCount) :
    Table.get (build K E w grid bits).rows q=
      FarAggregate.build (Automata.reverse E) w.reverse.toArray (unionRow K w.length (bits.get q)).bits := by
  simp only [build,assemble,Table.get_build]
  rfl

def query (K : DFA (Fin σ)) (idx : Index K) (left right : Nat) : Bool×Nat :=
  if left≤idx.grid ∧ right≤idx.length then
    let transition:=Range.query K idx.ranges left idx.grid
    let row:=Table.get idx.rows (transition.map.get K.initial)
    let out:=FarAggregate.query row (idx.length-right)
    (out.1,transition.work+out.2+7)
  else (false,3)

end REWB.BoundaryRange.FarRight
