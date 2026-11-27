import REWB.ResidualCachedP1
import REWB.ResidualCachedP2
import REWB.MaskedAllStartRowsCorrect

/-! Actual finite-variant input production. Every all-start row factory
is evaluated once by a materialized table. Projection reads the cached
payloads; it never calls a row factory again. The returned work includes
these projections and the fixed-pattern-build counter folds. -/
namespace REWB.ResidualActual
open REWB.BoundaryRange REWB.ResidualCached
variable {σ : Nat}

universe u v

theorem vector_get_map {α : Type u} {β : Type v} {n : Nat}
    (f : α→β) (xs : Vector α n) (i : Fin n) :
    (xs.map f).get i=f (xs.get i) := by simp [Vector.get]

def projectCell {n : Nat} {F : Fin n→Type u} {G : Fin n→Type v}
    (f : (i : Fin n)→F i→G i) (cell : Table.Cell F) : Table.Cell G :=
  ⟨cell.key,f cell.key cell.value,cell.work⟩

theorem projectCell_read {n : Nat} {F : Fin n→Type u} {G : Fin n→Type v}
    (f : (i : Fin n)→F i→G i) (cell : Table.Cell F) (i : Fin n)
    (h : cell.key=i) :
    (projectCell f cell).read i h=f i (cell.read i h) := by
  cases h
  rfl

/-- A cached-payload projection. Its scalar counter covers the vector
map. A nested projection's extra work is charged by the caller. -/
def project {n : Nat} {F : Fin n→Type u} {G : Fin n→Type v}
    (idx : Table.Index F) (f : (i : Fin n)→F i→G i) : Table.Index G :=
  ⟨idx.cells.map (projectCell f),by
    intro i
    simpa only [vector_get_map,projectCell] using idx.keyed i,
    idx.work+4*n+1⟩

theorem project_get {n : Nat} {F : Fin n→Type u} {G : Fin n→Type v}
    (idx : Table.Index F) (f : (i : Fin n)→F i→G i) (i : Fin n) :
    Table.get (project idx f) i=f i (Table.get idx i) := by
  simp only [Table.get,project,vector_get_map]
  exact projectCell_read f _ i (idx.keyed i)

theorem project_work {n : Nat} {F : Fin n→Type u} {G : Fin n→Type v}
    (idx : Table.Index F) (f : (i : Fin n)→F i→G i) :
    (project idx f).work=idx.work+4*n+1 := rfl

namespace P1

structure Rows (P : SevenDFA (Fin σ)) (n width : Nat) where
  bits : ResidualCached.P1.Inputs P n width
  work : Nat
  fixedPatternBuilds : Nat

def inputs (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) : Rows P w.length width :=
  let rows:=Table.build fun g : Fin P.G.stateCount=>
    let out:=MaskedAllStart.Rows.boundary P.A P.B P.C (gap P g) P.D w fallback width
    (out,out.work+3)
  let bits:=Vector.ofFn fun g=>(Table.get rows g).bits
  let builds:=(List.ofFn fun g=>(Table.get rows g).fixedPatternBuilds).sum
  ⟨bits,rows.work+12*P.G.stateCount+5,builds⟩

theorem inputs_get (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) (g : Fin P.G.stateCount) :
    (inputs P w fallback width).bits.get g=
      (MaskedAllStart.Rows.boundary P.A P.B P.C (gap P g) P.D w fallback width).bits := by
  simp only [inputs,Table.vector_get_ofFn,Table.get_build]

theorem inputs_ready (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) : ResidualCached.P1.Ready P w width (inputs P w fallback width).bits := by
  intro g
  rw [inputs_get]
  exact MaskedAllStart.Rows.boundary_ready P.A P.B P.C (gap P g) P.D w fallback width

theorem inputs_work (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) :
    (inputs P w fallback width).work=
      (List.ofFn fun g : Fin P.G.stateCount=>
        (MaskedAllStart.Rows.boundary P.A P.B P.C (gap P g) P.D w fallback width).work+6).sum+1+
        12*P.G.stateCount+5 := by
  simp only [inputs,Table.build_work,Nat.add_assoc,Nat.reduceAdd]

theorem inputs_builds (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) :
    (inputs P w fallback width).fixedPatternBuilds=
      (List.ofFn fun g : Fin P.G.stateCount=>
        (MaskedAllStart.Rows.boundary P.A P.B P.C (gap P g) P.D w fallback width).fixedPatternBuilds).sum := by
  simp only [inputs,Table.get_build]

end P1

namespace P2

structure Rows (P : SevenDFA (Fin σ)) (n width : Nat) where
  bits : ResidualCached.P2.Inputs P n width
  work : Nat
  fixedPatternBuilds : Nat

def forwardRows (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (width : Nat) :=
  Table.build fun q : Fin P.G.stateCount=>
    let cells:=Table.build fun c : TableColor.Key P.H=>
      let out:=MaskedAllStart.Rows.forward P.C P.D (suffix P q c) w fallback width
      (out,out.work+3)
    (cells,cells.work+3)

def backwardRows (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (width : Nat) :=
  Table.build fun a : Fin P.A.stateCount=>
    let cells:=Table.build fun g : Fin P.G.stateCount=>
      let out:=MaskedAllStart.Rows.backward (front P a g) P.C P.D w fallback width
      (out,out.work+3)
    (cells,cells.work+3)

def inputs (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) : Rows P w.length width :=
  let forward:=forwardRows P w fallback width
  let backward:=backwardRows P w fallback width
  let forwardBits:=project forward fun _ cells=>project cells fun _ row=>row.bits
  let backwardBits:=project backward fun _ cells=>project cells fun _ row=>row.bits
  let builds:=(List.ofFn fun q=>(List.ofFn fun c=>(Table.get (Table.get forward q) c).fixedPatternBuilds).sum).sum+
    (List.ofFn fun a=>(List.ofFn fun g=>(Table.get (Table.get backward a) g).fixedPatternBuilds).sum).sum
  let entries:=P.G.stateCount*TableColor.count P.H+P.A.stateCount*P.G.stateCount
  ⟨⟨forwardBits,backwardBits⟩,
    forwardBits.work+backwardBits.work+
      P.G.stateCount*(4*TableColor.count P.H+1)+P.A.stateCount*(4*P.G.stateCount+1)+12*entries+7,
    builds⟩

theorem inputs_forward (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) (q : Fin P.G.stateCount) (c : TableColor.Key P.H) :
    Table.get (Table.get (inputs P w fallback width).bits.forward q) c=
      (MaskedAllStart.Rows.forward P.C P.D (suffix P q c) w fallback width).bits := by
  simp only [inputs,project_get,forwardRows,Table.get_build]

theorem inputs_backward (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) (a : Fin P.A.stateCount) (g : Fin P.G.stateCount) :
    Table.get (Table.get (inputs P w fallback width).bits.backward a) g=
      (MaskedAllStart.Rows.backward (front P a g) P.C P.D w fallback width).bits := by
  simp only [inputs,project_get,backwardRows,Table.get_build]

theorem inputs_ready (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) : ResidualCached.P2.Ready P w width (inputs P w fallback width).bits := by
  intro a g q c
  rw [inputs_forward,inputs_backward]
  exact MaskedAllStart.Rows.oneUse_ready (front P a g) P.C P.D (suffix P q c) w fallback width

theorem inputs_work (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) :
    (inputs P w fallback width).work=
      (forwardRows P w fallback width).work+4*P.G.stateCount+1+
      ((backwardRows P w fallback width).work+4*P.A.stateCount+1)+
      P.G.stateCount*(4*TableColor.count P.H+1)+P.A.stateCount*(4*P.G.stateCount+1)+
      12*(P.G.stateCount*TableColor.count P.H+P.A.stateCount*P.G.stateCount)+7 := rfl

theorem forwardRows_work (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) :
    (forwardRows P w fallback width).work=
      (List.ofFn fun q : Fin P.G.stateCount=>
        (List.ofFn fun c : TableColor.Key P.H=>
          (MaskedAllStart.Rows.forward P.C P.D (suffix P q c) w fallback width).work+6).sum+7).sum+1 := by
  simp only [forwardRows,Table.build_work,Nat.add_assoc,Nat.reduceAdd]

theorem backwardRows_work (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) :
    (backwardRows P w fallback width).work=
      (List.ofFn fun a : Fin P.A.stateCount=>
        (List.ofFn fun g : Fin P.G.stateCount=>
          (MaskedAllStart.Rows.backward (front P a g) P.C P.D w fallback width).work+6).sum+7).sum+1 := by
  simp only [backwardRows,Table.build_work,Nat.add_assoc,Nat.reduceAdd]

theorem inputs_builds (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) :
    (inputs P w fallback width).fixedPatternBuilds=
      (List.ofFn fun q : Fin P.G.stateCount=>(List.ofFn fun c : TableColor.Key P.H=>
        (MaskedAllStart.Rows.forward P.C P.D (suffix P q c) w fallback width).fixedPatternBuilds).sum).sum+
      (List.ofFn fun a : Fin P.A.stateCount=>(List.ofFn fun g : Fin P.G.stateCount=>
        (MaskedAllStart.Rows.backward (front P a g) P.C P.D w fallback width).fixedPatternBuilds).sum).sum := by
  simp only [inputs,forwardRows,backwardRows,Table.get_build]

end P2
end REWB.ResidualActual
