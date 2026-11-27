import REWB.BoundaryRangeNearIndexScanCost
import REWB.BoundaryRangeGaps
import REWB.BoundaryBorderRegularRows

/-! The same-block border index. One text-level suffix-class index and
shared A/B/C/K/E range indexes serve every boundary pair. Each finite
C/K state pair stores its compiled gap automaton and its range index.
Queries enumerate the two local endpoints and use one gap query to
choose the common split p. Capture lengths are represented by dyadic
AP choices; the empty capture has a separate two-range test. -/
namespace REWB.BoundaryRange.NearIndex.Border
open REWB.BoundaryApplication
variable {σ : Nat}

structure GapCell (C K D : DFA (Fin σ)) (c : Fin C.stateCount) (k : Fin K.stateCount) where
  machine : DFA (Fin σ)
  machine_eq : machine=Automata.gap C K D c k
  ranges : Range.Index machine
  work : Nat

def buildGap (C K D : DFA (Fin σ)) (w : Word (Fin σ))
    (c : Fin C.stateCount) (k : Fin K.stateCount) : GapCell C K D c k :=
  let machine:=Automata.gap C K D c k
  let ranges:=Range.build machine w
  ⟨machine,rfl,ranges,StartIndex.rangeBuildWork machine ranges+machine.stateCount+3⟩

structure Index (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ)) where
  size : Nat
  height : Nat
  size_eq : size=w.toArray.size
  height_eq : height=MaskedSuffixClass.height size
  classes : BoundaryBorder.WindowIndex.Index size height
  aranges : Range.Index A
  branges : Range.Index B
  cranges : Range.Index C
  kranges : Range.Index K
  eranges : Range.Index E
  gaps : Table.Index fun c : Fin C.stateCount=>Table.Index fun k : Fin K.stateCount=>GapCell C K D c k
  length : Nat
  length_eq : length=w.length
  work : Nat

def build (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) :
    Index A B C K D E w :=
  let classes:=BoundaryBorder.WindowIndex.prepare w.toArray fallback
  let aranges:=Range.build A w
  let branges:=Range.build B w
  let cranges:=Range.build C w
  let kranges:=Range.build K w
  let eranges:=Range.build E w
  let gaps:=Table.build fun c : Fin C.stateCount=>
    let row:=Table.build fun k : Fin K.stateCount=>
      let cell:=buildGap C K D w c k
      (cell,cell.work)
    (row,row.work)
  ⟨w.toArray.size,classes.scales,rfl,rfl,classes,aranges,branges,cranges,kranges,eranges,gaps,w.length,rfl,
    classes.work+StartIndex.rangeBuildWork A aranges+StartIndex.rangeBuildWork B branges+
      StartIndex.rangeBuildWork C cranges+StartIndex.rangeBuildWork K kranges+
      StartIndex.rangeBuildWork E eranges+gaps.work+2*w.length+14⟩

@[simp] theorem build_gap (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (c : Fin C.stateCount) (k : Fin K.stateCount) :
    Table.get (Table.get (build A B C K D E w fallback).gaps c) k=buildGap C K D w c k := by
  simp only [build,Table.get_build]

def GapCell.query {C K D : DFA (Fin σ)} {c : Fin C.stateCount} {k : Fin K.stateCount}
    (cell : GapCell C K D c k) (lo hi : Nat) : Bool×Nat :=
  NearIndex.regular cell.machine cell.ranges lo hi

def gap {A B C K D E : DFA (Fin σ)} {w : Word (Fin σ)}
    (idx : Index A B C K D E w) (left a j : Nat) : Bool×Nat :=
  let middle:=max a left
  let c:=Range.query C idx.cranges a middle
  let k:=Range.query K idx.kranges left middle
  let cell:=Table.get (Table.get idx.gaps (c.map.get C.initial)) (k.map.get K.initial)
  let found:=cell.query middle j
  (found.1,c.work+k.work+found.2+6)

def copy {A B C K D E : DFA (Fin σ)} {w : Word (Fin σ)}
    (idx : Index A B C K D E w) (a : Nat) (j : Fin (w.toArray.size+1)) (right : Nat) : Bool×Nat :=
  let target : Fin (idx.size+1):=⟨j.val,by rw [idx.size_eq]; exact j.isLt⟩
  let positive:=BoundaryBorder.Regular.dyadic A B E idx.classes idx.aranges idx.branges idx.eranges a target right
  let before:=NearIndex.regular A idx.aranges 0 a
  let suffix:=NearIndex.regular E idx.eranges j.val right
  (positive.1 || (before.1 && B.final B.initial && suffix.1),positive.2+before.2+suffix.2+4)

def queryAt {A B C K D E : DFA (Fin σ)} {w : Word (Fin σ)}
    (idx : Index A B C K D E w) (left right a j : Nat) : Bool×Nat :=
  if h : j≤idx.length then
    let target : Fin (w.toArray.size+1):=⟨j,by rw [List.size_toArray,←idx.length_eq]; omega⟩
    let matching:=copy idx a target right
    let split:=gap idx left a j
    (matching.1 && split.1,matching.2+split.2+3)
  else (false,1)

def row {A B C K D E : DFA (Fin σ)} {w : Word (Fin σ)}
    (idx : Index A B C K D E w) (left right g a : Nat) : Bool×Nat :=
  let first:=max a left
  NearIndex.scan (queryAt idx left right a) first (min g (right+1)-first)

def query {A B C K D E : DFA (Fin σ)} {w : Word (Fin σ)}
    (idx : Index A B C K D E w) (left right g0 g : Nat) : Bool×Nat :=
  NearIndex.scan (row idx left right g) (g0+1) (g-(g0+1))

end REWB.BoundaryRange.NearIndex.Border
