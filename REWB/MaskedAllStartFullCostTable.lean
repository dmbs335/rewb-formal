import REWB.BoundaryRangeTable

/-! One materialized pass for factories returning their original payload
and original counter together with measured construction work. The old
dependent table is reconstructed only from stored cells; factories are
never called during projection or summation. Both ledgers are retained.
-/
namespace REWB.MaskedAllStart.FullCost.Table
open REWB.BoundaryRange
universe u
variable {n : Nat} {F : Fin n→Type u}

theorem vector_get_map {X Y : Type u} (f : X→Y) (xs : Vector X n) (i : Fin n) :
    (xs.map f).get i=f (xs.get i) := by simp [Vector.get]

def restoreCell (cell : BoundaryRange.Table.Cell (fun i=>F i×Nat)) : BoundaryRange.Table.Cell F :=
  ⟨cell.key,cell.value.1,cell.value.2⟩

def restore (idx : BoundaryRange.Table.Index (fun i=>F i×Nat)) : BoundaryRange.Table.Index F :=
  let cells:=idx.cells.map restoreCell
  ⟨cells,by
    intro i
    simpa only [cells,vector_get_map,restoreCell] using idx.keyed i,
    (List.ofFn fun i=>(cells.get i).work+3).sum+1⟩

theorem index_ext (a b : BoundaryRange.Table.Index F)
    (hc : a.cells=b.cells) (hw : a.work=b.work) : a=b := by
  cases a
  cases b
  cases hc
  cases hw
  rfl

theorem restore_build (make : (i : Fin n)→(F i×Nat)×Nat) :
    restore (BoundaryRange.Table.build make)=BoundaryRange.Table.build (fun i=>(make i).1) := by
  have hc : (BoundaryRange.Table.build make).cells.map restoreCell=
      (BoundaryRange.Table.build (fun i=>(make i).1)).cells := by
    apply Vector.ext
    intro i hi
    change ((BoundaryRange.Table.build make).cells.map restoreCell).get ⟨i,hi⟩=
      (BoundaryRange.Table.build (fun i=>(make i).1)).cells.get ⟨i,hi⟩
    simp only [vector_get_map,BoundaryRange.Table.build,BoundaryRange.Table.vector_get_ofFn] <;> rfl
  apply index_ext
  · exact hc
  · change (List.ofFn fun i=>(((BoundaryRange.Table.build make).cells.map restoreCell).get i).work+3).sum+1=_
    rw [hc]
    rfl

def build (make : (i : Fin n)→(F i×Nat)×Nat) : BoundaryRange.Table.Index F×Nat :=
  let rows:=BoundaryRange.Table.build make
  let old:=restore rows
  (old,rows.work+10*n+5)

theorem build_value (make : (i : Fin n)→(F i×Nat)×Nat) :
    (build make).1=BoundaryRange.Table.build (fun i=>(make i).1) :=
  restore_build make

theorem get_build (make : (i : Fin n)→(F i×Nat)×Nat) (i : Fin n) :
    BoundaryRange.Table.get (build make).1 i=(make i).1.1 := by
  rw [build_value,BoundaryRange.Table.get_build]

theorem build_work (make : (i : Fin n)→(F i×Nat)×Nat) :
    (build make).2=(List.ofFn fun i=>(make i).2+3).sum+1+10*n+5 := by
  simp only [build,BoundaryRange.Table.build_work]

theorem build_work_le (make : (i : Fin n)→(F i×Nat)×Nat) (bound : Nat)
    (hm : ∀i,(make i).2≤bound) : (build make).2≤n*(bound+3)+1+10*n+5 := by
  have hh:=BoundaryRange.Table.build_work_le make bound hm
  simp only [build]
  omega

end REWB.MaskedAllStart.FullCost.Table
