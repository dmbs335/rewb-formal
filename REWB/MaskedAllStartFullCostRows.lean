import REWB.MaskedAllStartFullCost
import REWB.MaskedAllStartFullCostTable
import REWB.MaskedAllStartRowsCorrect

/-! Actual finite row factories using the construction-counted solver.
Each solver and nested factory is executed once. The first projection
retains the complete old payload and ledger, so every cached Ready
contract transfers by equality; the second projection records full work.
The measured table restores old cells only from materialized results. -/
namespace REWB.MaskedAllStart.FullCost.Rows
open REWB.BoundaryRange REWB.BoundaryApplication REWB.OneUseRange
open REWB.MaskedAllStart.Rows
variable {σ : Nat}

def row (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) : Row×Nat :=
  let ⟨out,work⟩:=FullCost.solve B C E text fallback source target
  (⟨out.bits,out.accountedWork+4,out.fixedPatternBuilds⟩,work+4)

theorem row_value (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) :
    (row B C E text fallback source target).1=MaskedAllStart.Rows.row B C E text fallback source target := by
  simp only [row,MaskedAllStart.Rows.row,FullCost.solve_value]

theorem row_correct (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) (p : Nat) :
    FarAggregate.bit (row B C E text fallback source target).1.bits p=true ↔
      MaskedProgression.readMask source p=true ∧
        Spec.maskedStart B C E text.toList (MaskedProgression.readMask target) p := by
  rw [row_value]
  exact MaskedAllStart.Rows.row_correct B C E text fallback source target p

theorem row_size (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) :
    (row B C E text fallback source target).1.bits.size=text.size+1 := by
  rw [row_value]
  exact MaskedAllStart.Rows.row_size B C E text fallback source target

def prefixRows (B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (grid : Nat) : Prefix E×Nat :=
  let text:=(w.take grid).toArray
  let marks:=full text.size
  let ⟨rows,work⟩:=FullCost.Table.build fun c : TableColor.Key E=>
    let ⟨out,fullWork⟩:=row B C (FarSelection.variant E c) text fallback marks marks
    ((out,out.work),fullWork)
  let bits:=Vector.ofFn fun c=>(BoundaryRange.Table.get rows c).bits
  let builds:=(List.ofFn fun c=>(BoundaryRange.Table.get rows c).fixedPatternBuilds).sum
  (⟨bits,rows.work+20*TableColor.count E+4*(grid+1)+9,builds⟩,
    work+20*TableColor.count E+4*(grid+1)+9)

theorem prefix_value (B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (grid : Nat) :
    (prefixRows B C E w fallback grid).1=MaskedAllStart.Rows.prefixRows B C E w fallback grid := by
  simp only [prefixRows,MaskedAllStart.Rows.prefixRows,FullCost.Table.build_value,row_value]

theorem prefix_ready (B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (grid : Nat) :
    FarBank.Ready B C E w grid (prefixRows B C E w fallback grid).1.bits := by
  rw [prefix_value]
  exact MaskedAllStart.Rows.prefix_ready B C E w fallback grid

def far (A B C K D : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (grid : Nat) : Far K×Nat :=
  let requests:=FarRight.prepare K w grid
  let text:=w.reverse.toArray
  let source:=full w.length
  let reverseB:=Automata.reverse B
  let reverseA:=Automata.reverse A
  let ⟨rows,work⟩:=FullCost.Table.build fun q : Fin K.stateCount=>
    let ⟨cells,innerWork⟩:=FullCost.Table.build fun k : Fin K.stateCount=>
      let target:=(BoundaryRange.Table.get (BoundaryRange.Table.get requests.masks q) k).bits.toArray
      let gap:=Automata.reverse (Automata.gap C K D C.initial k)
      let ⟨out,fullWork⟩:=row reverseB gap reverseA text fallback source target
      ((out,out.work+6),fullWork+6)
    ((cells,cells.work+3),innerWork+3)
  let bits:=Vector.ofFn fun q=>Vector.ofFn fun k=>(BoundaryRange.Table.get (BoundaryRange.Table.get rows q) k).bits
  let builds:=(List.ofFn fun q=>(List.ofFn fun k=>
    (BoundaryRange.Table.get (BoundaryRange.Table.get rows q) k).fixedPatternBuilds).sum).sum
  (⟨bits,requests.work+rows.work+20*K.stateCount*(K.stateCount+1)+6*(w.length+1)+12,builds⟩,
    requests.work+work+20*K.stateCount*(K.stateCount+1)+6*(w.length+1)+12)

theorem far_value (A B C K D : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (grid : Nat) :
    (far A B C K D w fallback grid).1=MaskedAllStart.Rows.far A B C K D w fallback grid := by
  simp only [far,MaskedAllStart.Rows.far,FullCost.Table.build_value,row_value]

theorem far_ready (A B C K D : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (grid : Nat) :
    FarRight.Ready A B C K D w grid (far A B C K D w fallback grid).1.bits := by
  rw [far_value]
  exact MaskedAllStart.Rows.far_ready A B C K D w fallback grid

def forward (B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (width : Nat) :
    Forward E w.length width×Nat :=
  let ⟨rows,work⟩:=FullCost.Table.build fun slot : Fin (Grid.count w.length width)=>
    let ⟨out,fullWork⟩:=prefixRows B C E w fallback (Grid.position w.length width slot.val)
    ((out,out.work+3),fullWork+3)
  let bits:=Vector.ofFn fun slot=>(BoundaryRange.Table.get rows slot).bits
  let builds:=(List.ofFn fun slot=>(BoundaryRange.Table.get rows slot).fixedPatternBuilds).sum
  (⟨bits,rows.work+12*Grid.count w.length width+5,builds⟩,
    work+12*Grid.count w.length width+5)

theorem forward_value (B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (width : Nat) :
    (forward B C E w fallback width).1=MaskedAllStart.Rows.forward B C E w fallback width := by
  simp only [forward,MaskedAllStart.Rows.forward,FullCost.Table.build_value,prefix_value]

def backward (A B C : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (width : Nat) :
    Forward (Automata.reverse A) w.length width×Nat :=
  let reversed:=w.reverse
  let a:=Automata.reverse A
  let b:=Automata.reverse B
  let c:=Automata.reverse C
  let ⟨rows,work⟩:=FullCost.Table.build fun slot : Fin (Grid.count w.length width)=>
    let ⟨out,fullWork⟩:=prefixRows b c a reversed fallback (Grid.backward w.length width slot.val)
    ((out,out.work+3),fullWork+3)
  let bits:=Vector.ofFn fun slot=>(BoundaryRange.Table.get rows slot).bits
  let builds:=(List.ofFn fun slot=>(BoundaryRange.Table.get rows slot).fixedPatternBuilds).sum
  (⟨bits,rows.work+12*Grid.count w.length width+2*w.length+8,builds⟩,
    work+12*Grid.count w.length width+2*w.length+8)

theorem backward_value (A B C : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (width : Nat) :
    (backward A B C w fallback width).1=MaskedAllStart.Rows.backward A B C w fallback width := by
  simp only [backward,MaskedAllStart.Rows.backward,FullCost.Table.build_value,prefix_value]

theorem forward_ready (B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (width : Nat) :
    ∀slot,FarBank.Ready B C E w (Grid.position w.length width slot.val)
      ((forward B C E w fallback width).1.bits.get slot) := by
  rw [forward_value]
  exact MaskedAllStart.Rows.forward_ready B C E w fallback width

theorem backward_ready (A B C : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (width : Nat) :
    ∀slot,FarBank.Ready (Automata.reverse B) (Automata.reverse C) (Automata.reverse A)
      w.reverse (Grid.backward w.length width slot.val)
      ((backward A B C w fallback width).1.bits.get slot) := by
  rw [backward_value]
  exact MaskedAllStart.Rows.backward_ready A B C w fallback width

theorem oneUse_ready (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (width : Nat) :
    OneUseRange.Cache.Ready A B C E w width
      (forward B C E w fallback width).1.bits (backward A B C w fallback width).1.bits :=
  ⟨forward_ready B C E w fallback width,backward_ready A B C w fallback width⟩

def boundary (A B C K D : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (width : Nat) :
    Boundary K w.length width×Nat :=
  let ⟨rows,work⟩:=FullCost.Table.build fun slot : Fin (CacheGrid.count w.length width)=>
    let ⟨out,fullWork⟩:=far A B C K D w fallback (CacheGrid.upper w.length width slot.val)
    ((out,out.work+3),fullWork+3)
  let bits:=Vector.ofFn fun slot=>(BoundaryRange.Table.get rows slot).bits
  let builds:=(List.ofFn fun slot=>(BoundaryRange.Table.get rows slot).fixedPatternBuilds).sum
  (⟨bits,rows.work+12*CacheGrid.count w.length width+5,builds⟩,
    work+12*CacheGrid.count w.length width+5)

theorem boundary_value (A B C K D : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (width : Nat) :
    (boundary A B C K D w fallback width).1=MaskedAllStart.Rows.boundary A B C K D w fallback width := by
  simp only [boundary,MaskedAllStart.Rows.boundary,FullCost.Table.build_value,far_value]

theorem boundary_ready (A B C K D : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (width : Nat) :
    BoundaryRange.Cache.Ready A B C K D w width (boundary A B C K D w fallback width).1.bits := by
  rw [boundary_value]
  exact MaskedAllStart.Rows.boundary_ready A B C K D w fallback width

end REWB.MaskedAllStart.FullCost.Rows
