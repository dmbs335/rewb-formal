import REWB.BoundaryRangeFarRightCorrect

/-! Actual mask, finite-union and reverse-E aggregate counters.
The all-start output arrays are inputs, and their generation cost is
not included. No all-start provenance is needed for these bounds. -/
namespace REWB.BoundaryRange.FarRight
open REWB.BoundaryApplication REWB.OneUseRange
variable {σ : Nat}

def aggregateBudget (E : DFA (Fin σ)) (n : Nat) : Nat := (6*(Automata.reverse E).stateCount+7)*(n+1)

def finishBudget (K E : DFA (Fin σ)) (n : Nat) : Nat :=
  K.stateCount*(unionBudget K n+aggregateBudget E n+6)+1+2*n+9

theorem assemble_work (K E : DFA (Fin σ)) (w : Word (Fin σ)) (requests : Requests K w) (bits : Input K) :
    (assemble K E w requests bits).work≤requests.work+finishBudget K E w.length := by
  have ht:=Table.build_work_le (fun q : Fin K.stateCount=>
      let joined:=unionRow K requests.length (bits.get q)
      let aggregate:=FarAggregate.build (Automata.reverse E) w.reverse.toArray joined.bits
      (aggregate,joined.work+aggregate.work+3)) (unionBudget K w.length+aggregateBudget E w.length+3) (by
        intro q
        have hu : (unionRow K requests.length (bits.get q)).work=unionBudget K w.length := by
          rw [unionRow_work,requests.length_eq]
        have ha:=FarAggregate.build_work (Automata.reverse E) w.reverse.toArray
          (unionRow K requests.length (bits.get q)).bits
        rw [List.size_toArray,List.length_reverse] at ha
        dsimp only
        unfold aggregateBudget
        omega)
  change (assemble K E w requests bits).rows.work≤_ at ht
  simp only [Nat.add_assoc,Nat.reduceAdd] at ht
  change requests.work+(assemble K E w requests bits).rows.work+2*requests.length+9≤_
  rw [requests.length_eq]
  unfold finishBudget
  simp only [Nat.add_assoc] at ht ⊢
  omega

def buildBudget (K E : DFA (Fin σ)) (n : Nat) : Nat := prepareBudget K n+finishBudget K E n

theorem build_work (K E : DFA (Fin σ)) (w : Word (Fin σ)) (grid : Nat) (bits : Input K) :
    (build K E w grid bits).work≤buildBudget K E w.length := by
  have hh:=assemble_work K E w (prepare K w grid) bits
  have hp:=prepare_work K w grid
  unfold buildBudget
  exact Nat.le_trans hh (Nat.add_le_add_right hp _)

def queryBudget (K : DFA (Fin σ)) (n : Nat) : Nat := K.stateCount+8*(n.log2+2)+12

theorem query_work (K E : DFA (Fin σ)) (w : Word (Fin σ)) (grid : Nat) (hg : grid≤w.length)
    (bits : Input K) (left right : Nat) :
    (query K (build K E w grid bits) left right).2≤queryBudget K w.length := by
  unfold query
  change ((if left≤grid ∧ right≤w.length then _ else _) : Bool×Nat).2≤_
  split
  · rename_i h
    let q:=(Range.query K (Range.build K w) left grid).map.get K.initial
    have hp:=Range.query_work K w left grid h.1 hg
    have ha:=FarAggregate.query_work (Table.get (build K E w grid bits).rows q) (w.length-right)
    change (Range.query K (Range.build K w) left grid).work+
      (FarAggregate.query (Table.get (build K E w grid bits).rows q) (w.length-right)).2+7≤_
    unfold queryBudget
    omega
  · dsimp only
    unfold queryBudget
    omega

end REWB.BoundaryRange.FarRight
