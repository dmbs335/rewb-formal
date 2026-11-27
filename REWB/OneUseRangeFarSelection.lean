import REWB.OneUseRangeReverse
import REWB.BoundaryRangeTableColor

/-! A shared E range index and eager finite final-subset keys. Selecting
the row at right endpoint r reads E[g:r] once and compares materialized
finite rows. It does not rebuild an all-start array or a text index. -/
namespace REWB.OneUseRange.FarSelection
open REWB.BoundaryApplication REWB.BoundaryRange REWB.BoundaryIndex
variable {σ : Nat}

def variant (E : DFA (Fin σ)) (c : TableColor.Key E) : DFA (Fin σ) := Automata.finish E (Colors.decode E c)

structure Index (E : DFA (Fin σ)) (w : Word (Fin σ)) where
  ranges : Range.Index E
  colors : TableColor.Index E
  length : Nat
  length_eq : length=w.length
  work : Nat

def build (E : DFA (Fin σ)) (w : Word (Fin σ)) : Index E w :=
  let ranges:=Range.build E w
  let colors:=TableColor.build E
  ⟨ranges,colors,w.length,rfl,StartIndex.rangeBuildWork E ranges+colors.work+w.length+4⟩

def keyCore (E : DFA (Fin σ)) (ranges : Range.Index E) (colors : TableColor.Index E)
    (grid right : Nat) : TableColor.Key E×Nat :=
  let suffix:=Range.query E ranges grid right
  let chosen:=TableColor.choose E colors (fun q=>E.final (suffix.map.get q))
  (chosen.1,suffix.work+chosen.2+2)

def key {E : DFA (Fin σ)} {w : Word (Fin σ)} (idx : Index E w) (grid right : Nat) : TableColor.Key E×Nat :=
  keyCore E idx.ranges idx.colors grid right

theorem key_variant (E : DFA (Fin σ)) (w : Word (Fin σ)) (grid right : Nat) :
    variant E (key (build E w) grid right).1=
      Automata.tail E (Range.query E (Range.build E w) grid right).map := by
  change Automata.finish E (Colors.decode E (TableColor.choose E (TableColor.build E)
    (fun q=>E.final ((Range.query E (Range.build E w) grid right).map.get q))).1)=_
  rw [TableColor.choose_correct]
  rfl

def keyBudget (E : DFA (Fin σ)) (n : Nat) : Nat :=
  E.stateCount+8*(n.log2+2)+TableColor.budget E+3

theorem key_work (E : DFA (Fin σ)) (w : Word (Fin σ)) (grid right : Nat)
    (hgr : grid≤right) (hr : right≤w.length) :
    (key (build E w) grid right).2≤keyBudget E w.length := by
  have hs:=Range.query_work E w grid right hgr hr
  have hc:=TableColor.choose_work E (fun q=>E.final ((Range.query E (Range.build E w) grid right).map.get q))
  simp only [key,keyCore,build,keyBudget]
  omega

def buildBudget (E : DFA (Fin σ)) (n : Nat) : Nat :=
  StartIndex.rangeBound E n+(TableColor.build E).work+n+4

theorem build_work (E : DFA (Fin σ)) (w : Word (Fin σ)) : (build E w).work=buildBudget E w.length := by
  simp only [build,buildBudget,StartIndex.rangeBuildWork_build]

end REWB.OneUseRange.FarSelection
