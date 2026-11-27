import REWB.MaskedAllStart
import REWB.OneUseRangeCache
import REWB.BoundaryRangeCache

/-! Concrete producers for the finite all-start rows consumed by the
boundary and one-use caches. Every cell invokes the actual all-start
executor once and retains only its output bitmap and counters. Neither
the source store nor an answer callback is retained by the row table.
Correctness of these producers is connected after whole-plan correctness;
these definitions do not introduce a supplied Ready predicate.
-/
namespace REWB.MaskedAllStart.Rows
open REWB.BoundaryRange REWB.BoundaryApplication REWB.OneUseRange
variable {σ : Nat}

structure Row where
  bits : Array Bool
  work : Nat
  fixedPatternBuilds : Nat

def row (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) : Row :=
  let out:=MaskedAllStart.solve B C E text fallback source target
  ⟨out.bits,out.accountedWork+4,out.fixedPatternBuilds⟩

def full (n : Nat) : Array Bool := Array.replicate (n+1) true

theorem full_read (n p : Nat) (hp : p≤n) : MaskedProgression.readMask (full n) p=true := by
  simp only [full,MaskedProgression.readMask,Array.getElem?_replicate]
  rw [if_pos (by omega)]
  rfl

structure Prefix (E : DFA (Fin σ)) where
  bits : FarBank.Input E
  work : Nat
  fixedPatternBuilds : Nat

def prefixRows (B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (grid : Nat) : Prefix E :=
  let text:=(w.take grid).toArray
  let marks:=full text.size
  let rows:=Table.build fun c : TableColor.Key E=>
    let out:=row B C (FarSelection.variant E c) text fallback marks marks
    (out,out.work)
  let bits:=Vector.ofFn fun c=> (Table.get rows c).bits
  let fixedBuilds:=(List.ofFn fun c=>(Table.get rows c).fixedPatternBuilds).sum
  ⟨bits,rows.work+20*TableColor.count E+4*(grid+1)+9,fixedBuilds⟩

theorem prefix_get (B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (grid : Nat)
    (c : TableColor.Key E) :
    (prefixRows B C E w fallback grid).bits.get c=
      (row B C (FarSelection.variant E c) (w.take grid).toArray fallback
        (full (w.take grid).length) (full (w.take grid).length)).bits := by
  simp only [prefixRows,Table.vector_get_ofFn,Table.get_build,List.size_toArray]

theorem prefix_work (B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (grid : Nat) :
    (prefixRows B C E w fallback grid).work=
      (List.ofFn fun c : TableColor.Key E=>
        (row B C (FarSelection.variant E c) (w.take grid).toArray fallback
          (full (w.take grid).length) (full (w.take grid).length)).work+3).sum+1+
        20*TableColor.count E+4*(grid+1)+9 := by
  simp only [prefixRows,Table.build_work,List.size_toArray]

structure Far (K : DFA (Fin σ)) where
  bits : FarRight.Input K
  work : Nat
  fixedPatternBuilds : Nat

def far (A B C K D : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (grid : Nat) : Far K :=
  let requests:=FarRight.prepare K w grid
  let text:=w.reverse.toArray
  let source:=full w.length
  let reverseB:=Automata.reverse B
  let reverseA:=Automata.reverse A
  let rows:=Table.build fun q : Fin K.stateCount=>
    let cells:=Table.build fun k : Fin K.stateCount=>
      let target:=(Table.get (Table.get requests.masks q) k).bits.toArray
      let gap:=Automata.reverse (Automata.gap C K D C.initial k)
      let out:=row reverseB gap reverseA text fallback source target
      (out,out.work+6)
    (cells,cells.work+3)
  let bits:=Vector.ofFn fun q=>Vector.ofFn fun k=>(Table.get (Table.get rows q) k).bits
  let fixedBuilds:=(List.ofFn fun q=>(List.ofFn fun k=>(Table.get (Table.get rows q) k).fixedPatternBuilds).sum).sum
  ⟨bits,requests.work+rows.work+20*K.stateCount*(K.stateCount+1)+6*(w.length+1)+12,fixedBuilds⟩

theorem far_get (A B C K D : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (grid : Nat)
    (q k : Fin K.stateCount) :
    ((far A B C K D w fallback grid).bits.get q).get k=
      (row (Automata.reverse B) (Automata.reverse (Automata.gap C K D C.initial k)) (Automata.reverse A)
        w.reverse.toArray fallback (full w.length)
        (Table.get (Table.get (FarRight.prepare K w grid).masks q) k).bits.toArray).bits := by
  simp only [far,Table.vector_get_ofFn,Table.get_build]

structure Forward (E : DFA (Fin σ)) (n width : Nat) where
  bits : OneUseRange.Cache.Inputs E n width
  work : Nat
  fixedPatternBuilds : Nat

def forward (B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (width : Nat) : Forward E w.length width :=
  let rows:=Table.build fun slot : Fin (Grid.count w.length width)=>
    let out:=prefixRows B C E w fallback (Grid.position w.length width slot.val)
    (out,out.work+3)
  let bits:=Vector.ofFn fun slot=>(Table.get rows slot).bits
  let fixedBuilds:=(List.ofFn fun slot=>(Table.get rows slot).fixedPatternBuilds).sum
  ⟨bits,rows.work+12*Grid.count w.length width+5,fixedBuilds⟩

def backward (A B C : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (width : Nat) :
    Forward (Automata.reverse A) w.length width :=
  let reversed:=w.reverse
  let a:=Automata.reverse A
  let b:=Automata.reverse B
  let c:=Automata.reverse C
  let rows:=Table.build fun slot : Fin (Grid.count w.length width)=>
    let out:=prefixRows b c a reversed fallback (Grid.backward w.length width slot.val)
    (out,out.work+3)
  let bits:=Vector.ofFn fun slot=>(Table.get rows slot).bits
  let fixedBuilds:=(List.ofFn fun slot=>(Table.get rows slot).fixedPatternBuilds).sum
  ⟨bits,rows.work+12*Grid.count w.length width+2*w.length+8,fixedBuilds⟩

theorem forward_get (B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (width : Nat)
    (slot : Fin (Grid.count w.length width)) :
    (forward B C E w fallback width).bits.get slot=
      (prefixRows B C E w fallback (Grid.position w.length width slot.val)).bits := by
  simp only [forward,Table.vector_get_ofFn,Table.get_build]

theorem backward_get (A B C : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (width : Nat)
    (slot : Fin (Grid.count w.length width)) :
    (backward A B C w fallback width).bits.get slot=
      (prefixRows (Automata.reverse B) (Automata.reverse C) (Automata.reverse A) w.reverse fallback
        (Grid.backward w.length width slot.val)).bits := by
  simp only [backward,Table.vector_get_ofFn,Table.get_build]

structure Boundary (K : DFA (Fin σ)) (n width : Nat) where
  bits : BoundaryRange.Cache.Inputs K n width
  work : Nat
  fixedPatternBuilds : Nat

def boundary (A B C K D : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (width : Nat) : Boundary K w.length width :=
  let rows:=Table.build fun slot : Fin (CacheGrid.count w.length width)=>
    let out:=far A B C K D w fallback (CacheGrid.upper w.length width slot.val)
    (out,out.work+3)
  let bits:=Vector.ofFn fun slot=>(Table.get rows slot).bits
  let fixedBuilds:=(List.ofFn fun slot=>(Table.get rows slot).fixedPatternBuilds).sum
  ⟨bits,rows.work+12*CacheGrid.count w.length width+5,fixedBuilds⟩

theorem boundary_get (A B C K D : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) (width : Nat)
    (slot : Fin (CacheGrid.count w.length width)) :
    (boundary A B C K D w fallback width).bits.get slot=
      (far A B C K D w fallback (CacheGrid.upper w.length width slot.val)).bits := by
  simp only [boundary,Table.vector_get_ofFn,Table.get_build]

end REWB.MaskedAllStart.Rows
