import REWB.ShortOuterKeys
import REWB.ShortOuterSweep
import REWB.ShortOuterSuffix

/-! Actual construction of every short outer-copy feasibility bit.  At
each time x, eligible second copies are inserted before first-copy end
queries, so empty words and zero-length gaps are included.  Both loops
have only `width` iterations; no displacement or endpoint-pair loop is
hidden in a DFA test. -/
namespace REWB.ShortOuter.Band
open REWB.BoundaryApplication
variable {σ : Nat}

structure State (k : Nat) where
  cells : Array (Sweep.Cell k)
  bits : Array Bool
  touches : Nat
  work : Nat

def insertOne (G : DFA (Fin σ)) (range : Range.Index G) (keys : Keys.Index σ)
    (suffix : OneUseRange.FarAggregate.Index) (x len : Nat) : State G.stateCount→State G.stateCount
  | ⟨cells,bits,touches,work⟩ =>
    if x+len≤keys.length ∧ Suffix.get suffix (x+len)=true then
      let one:=Sweep.update G range x (Keys.get keys x len) true cells
      ⟨one.cells,bits,touches+1,work+one.work+8⟩
    else ⟨cells,bits,touches,work+8⟩

def inserts (G : DFA (Fin σ)) (range : Range.Index G) (keys : Keys.Index σ)
    (suffix : OneUseRange.FarAggregate.Index) (x : Nat) : Nat→State G.stateCount→State G.stateCount
  | 0,st => st
  | count+1,st => inserts G range keys suffix x count (insertOne G range keys suffix x count st)

def probeOne (G : DFA (Fin σ)) (range : Range.Index G) (keys : Keys.Index σ)
    (x len : Nat) : State G.stateCount→State G.stateCount
  | ⟨cells,bits,touches,work⟩ =>
    if len≤x then
      let p:=x-len
      let one:=Sweep.update G range x (Keys.get keys p len) false cells
      ⟨one.cells,bits.setIfInBounds (p*keys.width+len) one.value,touches+1,work+one.work+9⟩
    else ⟨cells,bits,touches,work+9⟩

def probes (G : DFA (Fin σ)) (range : Range.Index G) (keys : Keys.Index σ)
    (x : Nat) : Nat→State G.stateCount→State G.stateCount
  | 0,st => st
  | count+1,st => probes G range keys x count (probeOne G range keys x count st)

def charge (cost : Nat) : State k→State k
  | ⟨cells,bits,touches,work⟩ => ⟨cells,bits,touches,work+cost⟩

@[simp] theorem charge_cells (cost : Nat) (st : State k) : (charge cost st).cells=st.cells := by cases st; rfl
@[simp] theorem charge_bits (cost : Nat) (st : State k) : (charge cost st).bits=st.bits := by cases st; rfl
@[simp] theorem charge_touches (cost : Nat) (st : State k) : (charge cost st).touches=st.touches := by cases st; rfl
@[simp] theorem charge_work (cost : Nat) (st : State k) : (charge cost st).work=st.work+cost := by cases st; rfl

def run (G : DFA (Fin σ)) (range : Range.Index G) (keys : Keys.Index σ)
    (suffix : OneUseRange.FarAggregate.Index) : Nat→State G.stateCount→State G.stateCount
  | 0,st => st
  | x+1,st =>
    let inserted:=inserts G range keys suffix x keys.width st
    let queried:=probes G range keys x keys.width inserted
    run G range keys suffix x (charge 4 queried)

def initial (G : DFA (Fin σ)) (keys : Keys.Index σ) : State G.stateCount :=
  let cells:=Sweep.initial G.stateCount keys.length keys.registry.next
  let bits:=Array.replicate ((keys.length+1)*keys.width) false
  ⟨cells,bits,0,keys.registry.next+bits.size+G.stateCount+3⟩

structure Index (σ : Nat) where
  keys : Keys.Index σ
  bits : Array Bool
  touches : Nat
  work : Nat

def build (G H : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) (limit : Nat) : Index σ :=
  let n:=text.size
  let keys:=Keys.build text fallback limit
  let word:=text.toList
  let range:=Range.build G word
  let suffix:=Suffix.build H text
  let out:=run G range keys suffix.1 (n+1) (initial G keys)
  ⟨keys,out.bits,out.touches,
    keys.work+suffix.2+(G.stateCount+8)*range.products+range.letterCells+
      8*(n+1)+out.work+n+5⟩

def get (idx : Index σ) (p len : Nat) : Bool :=
  if len<idx.keys.width ∧ p+len≤idx.keys.length then
    idx.bits[p*idx.keys.width+len]?.getD false
  else false

def query (idx : Index σ) (p len : Nat) : Bool×Nat := (get idx p len,8)

@[simp] theorem query_value (idx : Index σ) (p len : Nat) : (query idx p len).1=get idx p len := rfl
@[simp] theorem query_work (idx : Index σ) (p len : Nat) : (query idx p len).2=8 := rfl

@[simp] theorem insertOne_cells_size (G : DFA (Fin σ)) (range : Range.Index G) (keys : Keys.Index σ)
    (suffix : OneUseRange.FarAggregate.Index) (x len : Nat) (st : State G.stateCount) :
    (insertOne G range keys suffix x len st).cells.size=st.cells.size := by
  cases st
  simp only [insertOne]
  split <;> simp

@[simp] theorem insertOne_bits (G : DFA (Fin σ)) (range : Range.Index G) (keys : Keys.Index σ)
    (suffix : OneUseRange.FarAggregate.Index) (x len : Nat) (st : State G.stateCount) :
    (insertOne G range keys suffix x len st).bits=st.bits := by
  cases st
  simp only [insertOne]
  split <;> rfl

@[simp] theorem inserts_cells_size (G : DFA (Fin σ)) (range : Range.Index G) (keys : Keys.Index σ)
    (suffix : OneUseRange.FarAggregate.Index) (x count : Nat) (st : State G.stateCount) :
    (inserts G range keys suffix x count st).cells.size=st.cells.size := by
  induction count generalizing st with
  | zero => rfl
  | succ count ih => simp only [inserts,ih,insertOne_cells_size]

@[simp] theorem inserts_bits (G : DFA (Fin σ)) (range : Range.Index G) (keys : Keys.Index σ)
    (suffix : OneUseRange.FarAggregate.Index) (x count : Nat) (st : State G.stateCount) :
    (inserts G range keys suffix x count st).bits=st.bits := by
  induction count generalizing st with
  | zero => rfl
  | succ count ih => simp only [inserts,ih,insertOne_bits]

@[simp] theorem probeOne_cells_size (G : DFA (Fin σ)) (range : Range.Index G) (keys : Keys.Index σ)
    (x len : Nat) (st : State G.stateCount) :
    (probeOne G range keys x len st).cells.size=st.cells.size := by
  cases st
  simp only [probeOne]
  split <;> simp

@[simp] theorem probeOne_bits_size (G : DFA (Fin σ)) (range : Range.Index G) (keys : Keys.Index σ)
    (x len : Nat) (st : State G.stateCount) :
    (probeOne G range keys x len st).bits.size=st.bits.size := by
  cases st
  simp only [probeOne]
  split <;> simp

@[simp] theorem probes_cells_size (G : DFA (Fin σ)) (range : Range.Index G) (keys : Keys.Index σ)
    (x count : Nat) (st : State G.stateCount) :
    (probes G range keys x count st).cells.size=st.cells.size := by
  induction count generalizing st with
  | zero => rfl
  | succ count ih => simp only [probes,ih,probeOne_cells_size]

@[simp] theorem probes_bits_size (G : DFA (Fin σ)) (range : Range.Index G) (keys : Keys.Index σ)
    (x count : Nat) (st : State G.stateCount) :
    (probes G range keys x count st).bits.size=st.bits.size := by
  induction count generalizing st with
  | zero => rfl
  | succ count ih => simp only [probes,ih,probeOne_bits_size]

@[simp] theorem run_cells_size (G : DFA (Fin σ)) (range : Range.Index G) (keys : Keys.Index σ)
    (suffix : OneUseRange.FarAggregate.Index) (count : Nat) (st : State G.stateCount) :
    (run G range keys suffix count st).cells.size=st.cells.size := by
  induction count generalizing st with
  | zero => rfl
  | succ count ih => simp only [run,ih,charge_cells,probes_cells_size,inserts_cells_size]

@[simp] theorem run_bits_size (G : DFA (Fin σ)) (range : Range.Index G) (keys : Keys.Index σ)
    (suffix : OneUseRange.FarAggregate.Index) (count : Nat) (st : State G.stateCount) :
    (run G range keys suffix count st).bits.size=st.bits.size := by
  induction count generalizing st with
  | zero => rfl
  | succ count ih => simp only [run,ih,charge_bits,probes_bits_size,inserts_bits]

end REWB.ShortOuter.Band
