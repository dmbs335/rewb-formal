import REWB.OneUseRangeFarSemantics
import REWB.OneUseRangeFarAggregateSound

/-! Eager finite row banks from actual immutable bit arrays. Each row
builds the backwards A aggregate once. Its provenance is a separate
explicit proposition: this module never supplies an all-start answer
oracle or asserts that the input arrays have already been computed. -/
namespace REWB.OneUseRange.FarBank
open REWB.BoundaryApplication REWB.BoundaryRange REWB.Spec
variable {σ : Nat}

abbrev Input (E : DFA (Fin σ)) := Vector (Array Bool) (TableColor.count E)

def Ready (B C E : DFA (Fin σ)) (w : Word (Fin σ)) (grid : Nat) (bits : Input E) : Prop :=
  ∀c : TableColor.Key E,∀i,i≤grid→
    (FarAggregate.bit (bits.get c) i=true ↔
      Spec.maskedStart B C (FarSelection.variant E c) (w.take grid) (fun _=>true) i)

structure Index (E : DFA (Fin σ)) where
  rows : Table.Index (fun _ : TableColor.Key E=>FarAggregate.Index)
  grid : Nat
  work : Nat

def build (A E : DFA (Fin σ)) (w : Word (Fin σ)) (grid : Nat) (bits : Input E) : Index E :=
  let prefixText:=(w.take grid).toArray
  let rows:=Table.build fun c : TableColor.Key E=>
    let row:=FarAggregate.build A prefixText (bits.get c)
    (row,row.work+1)
  ⟨rows,grid,rows.work+2*grid+5⟩

@[simp] theorem build_get (A E : DFA (Fin σ)) (w : Word (Fin σ)) (grid : Nat)
    (bits : Input E) (c : TableColor.Key E) :
    Table.get (build A E w grid bits).rows c=FarAggregate.build A (w.take grid).toArray (bits.get c) := by
  simp only [build,Table.get_build]

def queryCore (E : DFA (Fin σ)) (idx : Index E) (ranges : Range.Index E)
    (colors : TableColor.Index E) (length left right : Nat) : Bool×Nat :=
  if idx.grid≤right ∧ right≤length then
    let key:=FarSelection.keyCore E ranges colors idx.grid right
    let found:=FarAggregate.query (Table.get idx.rows key.1) left
    (found.1,key.2+found.2+4)
  else (false,2)

def query {E : DFA (Fin σ)} {w : Word (Fin σ)} (idx : Index E)
    (selection : FarSelection.Index E w) (left right : Nat) : Bool×Nat :=
  queryCore E idx selection.ranges selection.colors selection.length left right

theorem query_bits (A E : DFA (Fin σ)) (w : Word (Fin σ)) (grid : Nat) (bits : Input E)
    (left right : Nat) (hgr : grid≤right) (hr : right≤w.length) :
    (query (build A E w grid bits) (FarSelection.build E w) left right).1=true ↔
      ∃i,left≤i ∧ i≤grid ∧
        FarAggregate.bit (bits.get (FarSelection.key (FarSelection.build E w) grid right).1) i=true ∧
        A.accepts (slice w left i) := by
  unfold query queryCore
  change ((if grid≤right ∧ right≤w.length then _ else _) : Bool×Nat).1=true ↔ _
  rw [if_pos ⟨hgr,hr⟩]
  simp only [build_get]
  exact FarAggregate.query_prefix_correct A w grid (by omega) _ left

theorem query_correct (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (grid : Nat) (bits : Input E)
    (ready : Ready B C E w grid bits) (left right : Nat) (hgr : grid≤right) (hr : right≤w.length) :
    (query (build A E w grid bits) (FarSelection.build E w) left right).1=true ↔
      Border.FarTarget A B C E w left right grid := by
  rw [query_bits A E w grid bits left right hgr hr,FarSelection.farTarget_iff A B C E w left right grid hgr hr]
  constructor
  · rintro ⟨i,hli,hig,hb,hA⟩
    exact ⟨i,hli,hig,hA,(ready _ i hig).mp hb⟩
  · rintro ⟨i,hli,hig,hA,hb⟩
    exact ⟨i,hli,hig,(ready _ i hig).mpr hb,hA⟩

def buildBudget (A E : DFA (Fin σ)) (grid : Nat) : Nat :=
  TableColor.count E*((6*A.stateCount+7)*(grid+1)+4)+2*grid+6

theorem build_work (A E : DFA (Fin σ)) (w : Word (Fin σ)) (grid : Nat) (bits : Input E) :
    (build A E w grid bits).work≤buildBudget A E grid := by
  have hsize : (w.take grid).toArray.size≤grid := by simp only [List.size_toArray,List.length_take]; omega
  have ht:=Table.build_work_le (fun c : TableColor.Key E=>
      let row:=FarAggregate.build A (w.take grid).toArray (bits.get c)
      (row,row.work+1)) ((6*A.stateCount+7)*(grid+1)+1) (by
        intro c
        have h:=FarAggregate.build_work A (w.take grid).toArray (bits.get c)
        have hm:=Nat.mul_le_mul_left (6*A.stateCount+7) (Nat.add_le_add_right hsize 1)
        dsimp only
        omega)
  simp only [Nat.add_assoc,Nat.reduceAdd] at ht
  change (build A E w grid bits).rows.work≤TableColor.count E*((6*A.stateCount+7)*(grid+1)+4)+1 at ht
  change (build A E w grid bits).rows.work+2*grid+5≤_
  unfold buildBudget
  omega

def queryBudget (E : DFA (Fin σ)) (n : Nat) : Nat := FarSelection.keyBudget E n+8

theorem query_work (A E : DFA (Fin σ)) (w : Word (Fin σ)) (grid : Nat) (bits : Input E)
    (left right : Nat) :
    (query (build A E w grid bits) (FarSelection.build E w) left right).2≤queryBudget E w.length := by
  unfold query queryCore
  change ((if grid≤right ∧ right≤w.length then _ else _) : Bool×Nat).2≤_
  split
  · rename_i h
    have hk:=FarSelection.key_work E w grid right h.1 h.2
    have ha:=FarAggregate.query_work
      (Table.get (build A E w grid bits).rows (FarSelection.key (FarSelection.build E w) grid right).1) left
    change (FarSelection.key (FarSelection.build E w) grid right).2+
      (FarAggregate.query
        (Table.get (build A E w grid bits).rows (FarSelection.key (FarSelection.build E w) grid right).1) left).2+4≤_
    unfold queryBudget
    omega
  · dsimp only
    unfold queryBudget
    omega

end REWB.OneUseRange.FarBank
