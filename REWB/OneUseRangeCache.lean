import REWB.OneUseRangeFarBank
import REWB.OneUseRangeGrid

/-! Concrete eager forward/reverse prefix banks and the actual near
index. The input is two finite arrays of bit rows, not an endpoint
oracle. Their all-start provenance remains an explicit unresolved
construction obligation, expressed by `Ready`. Reverse-DFA compilation
is fixed-pattern preprocessing; the counters below track text/table
construction and query operations. -/
namespace REWB.OneUseRange.Cache
open REWB.BoundaryRange REWB.Spec
variable {σ : Nat}

abbrev Inputs (E : DFA (Fin σ)) (n width : Nat) := Vector (FarBank.Input E) (Grid.count n width)

def Ready (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (width : Nat)
    (forward : Inputs E w.length width) (backward : Inputs (Automata.reverse A) w.length width) : Prop :=
  (∀slot,FarBank.Ready B C E w (Grid.position w.length width slot.val) (forward.get slot)) ∧
  (∀slot,FarBank.Ready (Automata.reverse B) (Automata.reverse C) (Automata.reverse A) w.reverse
    (Grid.backward w.length width slot.val) (backward.get slot))

structure Backward (A : DFA (Fin σ)) (w : Word (Fin σ)) (slots : Nat) where
  machine : DFA (Fin σ)
  machine_eq : machine=Automata.reverse A
  selection : FarSelection.Index machine w.reverse
  banks : Table.Index (fun _ : Fin slots=>FarBank.Index machine)
  work : Nat

def Backward.query {A : DFA (Fin σ)} {w : Word (Fin σ)} {slots : Nat}
    (idx : Backward A w slots) (slot : Fin slots) (left right : Nat) : Bool×Nat :=
  FarBank.queryCore idx.machine (Table.get idx.banks slot) idx.selection.ranges idx.selection.colors
    idx.selection.length left right

structure Index (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) where
  length : Nat
  length_eq : length=w.length
  width : Nat
  positive : 0<width
  slots : Nat
  slots_eq : slots=Grid.count length width
  selection : FarSelection.Index E w
  forward : Table.Index (fun _ : Fin slots=>FarBank.Index E)
  backward : Backward A w slots
  near : Border.Index A B C E w
  work : Nat

def build (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) (hw : 0<width) (forward : Inputs E w.length width)
    (backward : Inputs (Automata.reverse A) w.length width) : Index A B C E w :=
  let n:=w.length
  let slots:=Grid.count n width
  let selection:=FarSelection.build E w
  let front:=Table.build fun slot : Fin slots=>
    let bank:=FarBank.build A E w (Grid.position n width slot.val) (forward.get slot)
    (bank,bank.work+4)
  let reversed:=w.reverse
  let reverseA:=Automata.reverse A
  let reverseE:=Automata.reverse E
  let reverseSelection:=FarSelection.build reverseA reversed
  let back:=Table.build fun slot : Fin slots=>
    let bank:=FarBank.build reverseE reverseA reversed (Grid.backward n width slot.val) (backward.get slot)
    (bank,bank.work+5)
  let near:=Border.build A B C E w fallback
  ⟨n,rfl,width,hw,slots,rfl,selection,front,
    ⟨reverseA,rfl,reverseSelection,back,reverseSelection.work+back.work+1⟩,near,
    selection.work+front.work+reverseSelection.work+back.work+near.work+2*n+20⟩

@[simp] theorem build_forward (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) (hw : 0<width) (forward : Inputs E w.length width)
    (backward : Inputs (Automata.reverse A) w.length width) (slot : Fin (Grid.count w.length width)) :
    Table.get (build A B C E w fallback width hw forward backward).forward slot=
      FarBank.build A E w (Grid.position w.length width slot.val) (forward.get slot) := by
  simp only [build,Table.get_build]

@[simp] theorem build_backward_query (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (width : Nat) (hw : 0<width) (forward : Inputs E w.length width)
    (backward : Inputs (Automata.reverse A) w.length width) (slot : Fin (Grid.count w.length width))
    (left right : Nat) :
    ((build A B C E w fallback width hw forward backward).backward.query slot left right)=
      FarBank.query
        (FarBank.build (Automata.reverse E) (Automata.reverse A) w.reverse
          (Grid.backward w.length width slot.val) (backward.get slot))
        (FarSelection.build (Automata.reverse A) w.reverse) left right := by
  simp only [build,Backward.query,Table.get_build,FarBank.query]

def queryValid {A B C E : DFA (Fin σ)} {w : Word (Fin σ)} (idx : Index A B C E w)
    (left right : Nat) (hlr : left≤right) (hr : right≤idx.length) : Bool×Nat :=
  let chosen:=Grid.choose idx.length idx.width idx.positive left right hlr hr
  let leftSlot : Fin idx.slots:=⟨chosen.leftSlot.val,by rw [idx.slots_eq]; exact chosen.leftSlot.isLt⟩
  let rightSlot : Fin idx.slots:=⟨chosen.rightSlot.val,by rw [idx.slots_eq]; exact chosen.rightSlot.isLt⟩
  let forward:=FarBank.query (Table.get idx.forward rightSlot) idx.selection left right
  let backward:=idx.backward.query leftSlot (idx.length-right) (idx.length-left)
  let near:=Border.query idx.near left right chosen.leftGrid chosen.rightGrid
  (forward.1 || backward.1 || near.1,forward.2+backward.2+near.2+chosen.work+9)

def query {A B C E : DFA (Fin σ)} {w : Word (Fin σ)} (idx : Index A B C E w)
    (left right : Nat) : Bool×Nat :=
  if h : left≤right ∧ right≤idx.length then queryValid idx left right h.1 h.2 else (false,3)

end REWB.OneUseRange.Cache
