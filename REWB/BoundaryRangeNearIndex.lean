import REWB.BoundaryRangeTableColor
import REWB.BoundaryRangePrimitives

/-! Eager finite variants at one boundary pair. The separated, fixed-end,
and fixed-start indexes are built for every C-final subset and D-initial
state. Queries read these cached indexes; they never call a text-index
builder. The C/K/D range indexes and numerical boundaries are shared. -/
namespace REWB.BoundaryRange.NearIndex
open REWB.BoundaryApplication
open REWB.BoundaryIndex
variable {σ : Nat}

def cVariant (C : DFA (Fin σ)) (c : TableColor.Key C) : DFA (Fin σ) :=
  Automata.finish C (Colors.decode C c)

def dVariant (D : DFA (Fin σ)) (d : Fin D.stateCount) : DFA (Fin σ) :=
  Automata.start D d

structure Index (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ)) (g0 g : Nat) where
  colors : TableColor.Index C
  separated : Table.Index fun _ : TableColor.Key C=>
    Table.Index fun _ : Fin D.stateCount=>Separated.Index E w
  ends : Table.Index fun d : Fin D.stateCount=>HeavyIndex.Index A B (dVariant D d) E w
  starts : Table.Index fun c : TableColor.Key C=>StartIndex.Index A B (cVariant C c) E w
  cranges : Range.Index C
  kranges : Range.Index K
  dranges : Range.Index D
  lower : Nat
  upper : Nat
  length : Nat
  height : Nat
  lower_eq : lower=g0
  upper_eq : upper=g
  length_eq : length=w.length
  work : Nat

def build (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g0 g : Nat) (h0g : g0≤g) (hg : g≤w.length) : Index A B C K D E w g0 g :=
  let colors:=TableColor.build C
  let separated:=Table.build fun c : TableColor.Key C=>
    let row:=Table.build fun d : Fin D.stateCount=>
      let idx:=Separated.build A B (cVariant C c) (dVariant D d) E w fallback g0 g hg
      (idx,idx.work)
    (row,row.work)
  let ends:=Table.build fun d : Fin D.stateCount=>
    let idx:=HeavyIndex.build A B (dVariant D d) E w fallback g hg
    (idx,idx.work)
  let starts:=Table.build fun c : TableColor.Key C=>
    let idx:=StartIndex.build A B (cVariant C c) E w fallback g0 (by omega)
    (idx,idx.work)
  let cranges:=Range.build C w
  let kranges:=Range.build K w
  let dranges:=Range.build D w
  ⟨colors,separated,ends,starts,cranges,kranges,dranges,g0,g,w.length,w.length.log2+2,
    rfl,rfl,rfl,colors.work+separated.work+ends.work+starts.work+
      StartIndex.rangeBuildWork C cranges+StartIndex.rangeBuildWork K kranges+
      StartIndex.rangeBuildWork D dranges+2*w.length+12⟩

@[simp] theorem build_separated (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ))
    (fallback : Fin σ) (g0 g : Nat) (h0g : g0≤g) (hg : g≤w.length)
    (c : TableColor.Key C) (d : Fin D.stateCount) :
    Table.get (Table.get (build A B C K D E w fallback g0 g h0g hg).separated c) d=
      Separated.build A B (cVariant C c) (dVariant D d) E w fallback g0 g hg := by
  simp only [build,Table.get_build]

@[simp] theorem build_end (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ))
    (fallback : Fin σ) (g0 g : Nat) (h0g : g0≤g) (hg : g≤w.length) (d : Fin D.stateCount) :
    Table.get (build A B C K D E w fallback g0 g h0g hg).ends d=
      HeavyIndex.build A B (dVariant D d) E w fallback g hg := by
  simp only [build,Table.get_build]

@[simp] theorem build_start (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ))
    (fallback : Fin σ) (g0 g : Nat) (h0g : g0≤g) (hg : g≤w.length) (c : TableColor.Key C) :
    Table.get (build A B C K D E w fallback g0 g h0g hg).starts c=
      StartIndex.build A B (cVariant C c) E w fallback g0 (by omega) := by
  simp only [build,Table.get_build]

def cKey {A B C K D E : DFA (Fin σ)} {w : Word (Fin σ)} {g0 g : Nat}
    (idx : Index A B C K D E w g0 g) (p : Nat) : TableColor.Key C×Nat :=
  let pre:=Range.query C idx.cranges idx.lower p
  let selected:=TableColor.choose C idx.colors (fun q=>C.final (pre.map.get q))
  (selected.1,pre.work+selected.2+2)

def dKey {A B C K D E : DFA (Fin σ)} {w : Word (Fin σ)} {g0 g : Nat}
    (idx : Index A B C K D E w g0 g) (p : Nat) : Fin D.stateCount×Nat :=
  let pre:=Range.query D idx.dranges p idx.upper
  (pre.map.get D.initial,pre.work+2)

def separated {A B C K D E : DFA (Fin σ)} {w : Word (Fin σ)} {g0 g : Nat}
    (idx : Index A B C K D E w g0 g) (p right : Nat) : Bool×Nat :=
  let c:=cKey idx p
  let d:=dKey idx p
  let cell:=Table.get (Table.get idx.separated c.1) d.1
  let out:=Separated.query E cell right
  (out.1,c.2+d.2+out.2+3)

def fixedEnd {A B C K D E : DFA (Fin σ)} {w : Word (Fin σ)} {g0 g : Nat}
    (idx : Index A B C K D E w g0 g) (p : Nat) (a : Fin (w.length+1)) (right : Nat) : Bool×Nat :=
  let d:=dKey idx p
  let cell:=Table.get idx.ends d.1
  let out:=HeavyIndex.query A B (dVariant D d.1) E w cell a right
  (out.value,d.2+out.work+2)

def fixedStart {A B C K D E : DFA (Fin σ)} {w : Word (Fin σ)} {g0 g : Nat}
    (idx : Index A B C K D E w g0 g) (p : Nat) (j : Fin (w.length+1)) (right : Nat) : Bool×Nat :=
  let c:=cKey idx p
  let cell:=Table.get idx.starts c.1
  let out:=StartIndex.query B (cVariant C c.1) E cell j right
  (out.value,c.2+out.work+2)

end REWB.BoundaryRange.NearIndex
