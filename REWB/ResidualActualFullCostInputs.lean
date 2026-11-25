import REWB.MaskedAllStartFullCostRows
import REWB.ResidualActualRows

/-! Actual construction-counted finite P1/P2 input tables. All row
factories run once, and all bitmap/old-ledger projections read stored
cells. The first projection is exactly the old complete cached input
record; its unconditional Ready theorem is therefore inherited. -/
namespace REWB.ResidualActual.FullCost
open REWB.BoundaryRange REWB.ResidualCached
variable {σ : Nat}

namespace P1

def inputs (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) : ResidualActual.P1.Rows P w.length width×Nat :=
  let ⟨rows,work⟩:=MaskedAllStart.FullCost.Table.build fun g : Fin P.G.stateCount=>
    let ⟨out,fullWork⟩:=MaskedAllStart.FullCost.Rows.boundary P.A P.B P.C (gap P g) P.D w fallback width
    ((out,out.work+3),fullWork+3)
  let bits:=Vector.ofFn fun g=>(Table.get rows g).bits
  let builds:=(List.ofFn fun g=>(Table.get rows g).fixedPatternBuilds).sum
  (⟨bits,rows.work+12*P.G.stateCount+5,builds⟩,work+12*P.G.stateCount+5)

theorem inputs_value (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (width : Nat) :
    (inputs P w fallback width).1=ResidualActual.P1.inputs P w fallback width := by
  simp only [inputs,ResidualActual.P1.inputs,MaskedAllStart.FullCost.Table.build_value,
    MaskedAllStart.FullCost.Rows.boundary_value]

theorem inputs_ready (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) : ResidualCached.P1.Ready P w width (inputs P w fallback width).1.bits := by
  rw [inputs_value]
  exact ResidualActual.P1.inputs_ready P w fallback width

theorem inputs_work (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) :
    (inputs P w fallback width).2=
      (List.ofFn fun g : Fin P.G.stateCount=>
        (MaskedAllStart.FullCost.Rows.boundary P.A P.B P.C (gap P g) P.D w fallback width).2+6).sum+
        1+10*P.G.stateCount+5+12*P.G.stateCount+5 := by
  simp only [inputs,MaskedAllStart.FullCost.Table.build_work,Nat.add_assoc,Nat.reduceAdd]

theorem inputs_builds (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) :
    (inputs P w fallback width).1.fixedPatternBuilds=
      (List.ofFn fun g : Fin P.G.stateCount=>
        (MaskedAllStart.FullCost.Rows.boundary P.A P.B P.C (gap P g) P.D w fallback width).1.fixedPatternBuilds).sum := by
  simp only [inputs,MaskedAllStart.FullCost.Table.get_build]

end P1

namespace P2

def forwardRows (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (width : Nat) :=
  MaskedAllStart.FullCost.Table.build fun q : Fin P.G.stateCount=>
    let ⟨cells,innerWork⟩:=MaskedAllStart.FullCost.Table.build fun c : TableColor.Key P.H=>
      let ⟨out,fullWork⟩:=MaskedAllStart.FullCost.Rows.forward P.C P.D (suffix P q c) w fallback width
      ((out,out.work+3),fullWork+3)
    ((cells,cells.work+3),innerWork+3)

def backwardRows (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (width : Nat) :=
  MaskedAllStart.FullCost.Table.build fun a : Fin P.A.stateCount=>
    let ⟨cells,innerWork⟩:=MaskedAllStart.FullCost.Table.build fun g : Fin P.G.stateCount=>
      let ⟨out,fullWork⟩:=MaskedAllStart.FullCost.Rows.backward (front P a g) P.C P.D w fallback width
      ((out,out.work+3),fullWork+3)
    ((cells,cells.work+3),innerWork+3)

theorem forwardRows_value (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (width : Nat) :
    (forwardRows P w fallback width).1=ResidualActual.P2.forwardRows P w fallback width := by
  simp only [forwardRows,ResidualActual.P2.forwardRows,MaskedAllStart.FullCost.Table.build_value,
    MaskedAllStart.FullCost.Rows.forward_value]

theorem backwardRows_value (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (width : Nat) :
    (backwardRows P w fallback width).1=ResidualActual.P2.backwardRows P w fallback width := by
  simp only [backwardRows,ResidualActual.P2.backwardRows,MaskedAllStart.FullCost.Table.build_value,
    MaskedAllStart.FullCost.Rows.backward_value]

def inputs (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) : ResidualActual.P2.Rows P w.length width×Nat :=
  let ⟨forward,forwardWork⟩:=forwardRows P w fallback width
  let ⟨backward,backwardWork⟩:=backwardRows P w fallback width
  let forwardBits:=project forward fun _ cells=>project cells fun _ row=>row.bits
  let backwardBits:=project backward fun _ cells=>project cells fun _ row=>row.bits
  let builds:=(List.ofFn fun q=>(List.ofFn fun c=>(Table.get (Table.get forward q) c).fixedPatternBuilds).sum).sum+
    (List.ofFn fun a=>(List.ofFn fun g=>(Table.get (Table.get backward a) g).fixedPatternBuilds).sum).sum
  let entries:=P.G.stateCount*TableColor.count P.H+P.A.stateCount*P.G.stateCount
  let overhead:=P.G.stateCount*(4*TableColor.count P.H+1)+P.A.stateCount*(4*P.G.stateCount+1)+12*entries+7
  (⟨⟨forwardBits,backwardBits⟩,forwardBits.work+backwardBits.work+overhead,builds⟩,
    forwardWork+4*P.G.stateCount+1+(backwardWork+4*P.A.stateCount+1)+overhead)

theorem inputs_value (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (width : Nat) :
    (inputs P w fallback width).1=ResidualActual.P2.inputs P w fallback width := by
  simp only [inputs,ResidualActual.P2.inputs,forwardRows_value,backwardRows_value,Nat.add_assoc]

theorem inputs_ready (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) : ResidualCached.P2.Ready P w width (inputs P w fallback width).1.bits := by
  rw [inputs_value]
  exact ResidualActual.P2.inputs_ready P w fallback width

theorem inputs_work (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) :
    (inputs P w fallback width).2=
      (forwardRows P w fallback width).2+4*P.G.stateCount+1+
      ((backwardRows P w fallback width).2+4*P.A.stateCount+1)+
      (P.G.stateCount*(4*TableColor.count P.H+1)+P.A.stateCount*(4*P.G.stateCount+1)+
      12*(P.G.stateCount*TableColor.count P.H+P.A.stateCount*P.G.stateCount)+7) := rfl

theorem forwardRows_work (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) :
    (forwardRows P w fallback width).2=
      (List.ofFn fun q : Fin P.G.stateCount=>
        (List.ofFn fun c : TableColor.Key P.H=>
          (MaskedAllStart.FullCost.Rows.forward P.C P.D (suffix P q c) w fallback width).2+6).sum+
          1+10*TableColor.count P.H+5+6).sum+1+10*P.G.stateCount+5 := by
  simp only [forwardRows,MaskedAllStart.FullCost.Table.build_work,Nat.add_assoc,Nat.reduceAdd]

theorem backwardRows_work (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) :
    (backwardRows P w fallback width).2=
      (List.ofFn fun a : Fin P.A.stateCount=>
        (List.ofFn fun g : Fin P.G.stateCount=>
          (MaskedAllStart.FullCost.Rows.backward (front P a g) P.C P.D w fallback width).2+6).sum+
          1+10*P.G.stateCount+5+6).sum+1+10*P.A.stateCount+5 := by
  simp only [backwardRows,MaskedAllStart.FullCost.Table.build_work,Nat.add_assoc,Nat.reduceAdd]

theorem inputs_builds (P : SevenDFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) :
    (inputs P w fallback width).1.fixedPatternBuilds=
      (List.ofFn fun q : Fin P.G.stateCount=>(List.ofFn fun c : TableColor.Key P.H=>
        (MaskedAllStart.FullCost.Rows.forward P.C P.D (suffix P q c) w fallback width).1.fixedPatternBuilds).sum).sum+
      (List.ofFn fun a : Fin P.A.stateCount=>(List.ofFn fun g : Fin P.G.stateCount=>
        (MaskedAllStart.FullCost.Rows.backward (front P a g) P.C P.D w fallback width).1.fixedPatternBuilds).sum).sum := by
  simp only [inputs,forwardRows,backwardRows,MaskedAllStart.FullCost.Table.get_build]

end P2
end REWB.ResidualActual.FullCost
