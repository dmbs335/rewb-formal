import REWB.ShortOuterBandCost

/-! Direct DFA acceptance for every bounded factor.  Each start performs
one counted prefix pass over at most `width` letters, and every later
factor test is two array reads and one final-state test.  Padded entries
beyond the text are never used by the bounded-factor correctness theorem. -/
namespace REWB.ShortOuter.Regular
open REWB.Periodic
variable {α : Type} {σ : Nat}

theorem prefix_length (A : DFA α) (w : Word α) (q : Fin A.stateCount) :
    (MaskScan.prefixStates A q w).length=w.length+1 := by
  induction w generalizing q with
  | nil => rfl
  | cons c w ih => simp only [MaskScan.prefixStates,List.length_cons,ih]

def row (A : DFA α) (f : Nat→α) (p width : Nat) : Array (Fin A.stateCount)×Nat :=
  let word:=segment f p width
  let states:=IntervalDFA.countedPrefix A A.initial word
  let out:=states.1.toArray
  (out,3*states.2+2*width+out.size+5)

theorem row_size (A : DFA α) (f : Nat→α) (p width : Nat) : (row A f p width).1.size=width+1 := by
  simp only [row,IntervalDFA.countedPrefix_spec,List.size_toArray,prefix_length,segment_length]

theorem row_work (A : DFA α) (f : Nat→α) (p width : Nat) : (row A f p width).2=6*width+6 := by
  simp only [row,IntervalDFA.countedPrefix_spec,List.size_toArray,prefix_length,segment_length]
  omega

theorem row_get (A : DFA α) (f : Nat→α) (p width len : Nat) (hl : len≤width) :
    (row A f p width).1[len]?=some (A.run A.initial (segment f p len)) := by
  simp only [row,IntervalDFA.countedPrefix_spec,List.getElem?_toArray]
  rw [MaskScan.prefixStates_get A _ len (by rwa [segment_length]),
    SmallPeriodP2.segment_take f p width len hl]

structure Index (A : DFA α) where
  length : Nat
  width : Nat
  rows : Array (Array (Fin A.stateCount))
  work : Nat

def build (A : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) (width : Nat) : Index A :=
  let ps:=CountedProjection.range (text.size+1)
  let rs:=CountedProjection.map (fun p=>row A (ArrayText.read text fallback) p width) ps.1
  let rows:=rs.1.toArray
  ⟨text.size,width,rows,ps.2+rs.2+rows.size+2⟩

def state (A : DFA α) (idx : Index A) (p len : Nat) : Fin A.stateCount :=
  ((idx.rows[p]?.getD #[])[len]?).getD A.initial

def accepts (A : DFA α) (idx : Index A) (p len : Nat) : Bool := A.final (state A idx p len)

theorem build_rows (A : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (width p : Nat) (hp : p≤text.size) :
    (build A text fallback width).rows[p]?=
      some (row A (ArrayText.read text fallback) p width).1 := by
  simp only [build,List.getElem?_toArray,CountedProjection.map_value,CountedProjection.range_value,
    List.getElem?_map,List.getElem?_range,show p<text.size+1 by omega,if_true,Option.map_some']

theorem state_correct (A : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (width p len : Nat) (hp : p≤text.size) (hl : len≤width) :
    state A (build A text fallback width) p len=A.run A.initial (segment (ArrayText.read text fallback) p len) := by
  rw [state,build_rows A text fallback width p hp,Option.getD_some,row_get A _ p width len hl,Option.getD_some]

theorem accepts_correct (A : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (width p len : Nat) (hp : p+len≤text.size) (hl : len≤width) :
    accepts A (build A text fallback width) p len=true ↔
      A.accepts (Spec.slice text.toList p (p+len)) := by
  rw [accepts,state_correct A text fallback width p len (by omega) hl,
    ArrayText.segment_read text fallback p len hp]
  simp only [DFA.accepts,Spec.slice,Nat.add_sub_cancel_left]

theorem build_work (A : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ) (width : Nat) :
    (build A text fallback width).work=(text.size+1)*(6*width+10)+4 := by
  have hm:=CountedProjection.map_steps_constant
    (fun p=>row A (ArrayText.read text fallback) p width) (CountedProjection.range (text.size+1)).1
    (6*width+6) (by intro p _; exact row_work A _ p width)
  simp only [build]
  rw [hm]
  simp only [CountedProjection.range,CountedProjection.rangeFrom_steps,
    CountedProjection.map_value,CountedProjection.rangeFrom_value,List.size_toArray,List.length_map,List.length_range']
  simp only [Nat.mul_add,Nat.mul_one]
  omega

end REWB.ShortOuter.Regular
