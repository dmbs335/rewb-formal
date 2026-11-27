import REWB.SmallPeriodP2

/-! A finite-word entry point for the small-period P2 branch. The input
    is materialized once as an array, and every character probe uses an
    array lookup with an explicit fallback. In particular, probes beyond
    the input made by rejected primitive-square candidates are defined.

    `inputCells` counts the cells in that materialization. The inherited
    counters retain their existing meanings; this module does not turn
    them into a machine-level running-time claim. -/
namespace REWB.ArrayText
open REWB.Periodic REWB.RunGeometry
variable {α : Type}

/-- Safe direct-addressed character access. The array is an argument
    already materialized by the caller, not rebuilt inside this function. -/
def read (text : Array α) (fallback : α) (i : Nat) : α :=
  text[i]?.getD fallback

theorem read_word (w : Word α) (fallback : α) (i : Nat) :
    read w.toArray fallback i=w[i]?.getD fallback := by
  simp only [read,List.getElem?_toArray]

theorem read_in_bounds (w : Word α) (fallback : α) (i : Nat) (hi : i<w.length) :
    read w.toArray fallback i=w[i] := by
  rw [read_word,List.getElem?_eq_getElem hi]
  rfl

theorem read_out_of_bounds (text : Array α) (fallback : α) (i : Nat)
    (hi : text.size≤i) : read text fallback i=fallback := by
  rw [read,Array.getElem?_eq_none hi]
  rfl

theorem segment_get (f : Nat→α) (a L i : Nat) (hi : i<L) :
    (segment f a L)[i]?=some (f (a+i)) := by
  induction L generalizing a i with
  | zero => omega
  | succ L ih =>
    cases i with
    | zero => simp only [segment,List.getElem?_cons_zero,Nat.add_zero]
    | succ i =>
      change (segment f (a+1) L)[i]?=some (f (a+(i+1)))
      rw [ih (a+1) i (by omega),show a+1+i=a+(i+1) by omega]

/-- Every bounded segment of the accessor is the corresponding finite
    array slice. Its value is independent of the fallback. -/
theorem segment_read (text : Array α) (fallback : α) (a L : Nat)
    (h : a+L≤text.size) :
    segment (read text fallback) a L=(text.toList.drop a).take L := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i<L
  · rw [segment_get _ _ _ _ hi,List.getElem?_take,if_pos hi,
      List.getElem?_drop,Array.getElem?_toList]
    have hai : a+i<text.size := by omega
    simp only [read,Array.getElem?_eq_getElem hai,Option.getD_some]
  · rw [List.getElem?_eq_none (by rw [segment_length]; omega),
      List.getElem?_take,if_neg hi]

theorem segment_word (w : Word α) (fallback : α) (a L : Nat)
    (h : a+L≤w.length) :
    segment (read w.toArray fallback) a L=(w.drop a).take L := by
  have hh := segment_read w.toArray fallback a L (by simpa only [List.size_toArray] using h)
  simpa only [List.toList_toArray] using hh

theorem segment_full (w : Word α) (fallback : α) :
    segment (read w.toArray fallback) 0 w.length=w := by
  rw [segment_word w fallback 0 w.length (by omega)]
  simp only [List.drop_zero,List.take_length]

theorem factor_word (w : Word α) (fallback : α) (a b : Nat)
    (hab : a≤b) (hb : b≤w.length) :
    P2Periodic.factor (read w.toArray fallback) a b=Spec.slice w a b := by
  exact segment_word w fallback a (b-a) (by omega)

/-- Shifting the total accessor agrees even past the end with the
    accessor of the dropped word, using the same fallback. -/
theorem shift_word (w : Word α) (fallback : α) (a : Nat) :
    shift (read w.toArray fallback) a=read (w.drop a).toArray fallback := by
  funext i
  simp only [shift,read,List.getElem?_toArray,List.getElem?_drop]

theorem shifted_segment (w : Word α) (fallback : α) (lo a L : Nat)
    (h : lo+a+L≤w.length) :
    segment (shift (read w.toArray fallback) lo) a L=(w.drop (lo+a)).take L := by
  rw [LongSourceCoverage.segment_shift,segment_word w fallback (lo+a) L h]

theorem shifted_factor (w : Word α) (fallback : α) (lo a b : Nat)
    (hab : a≤b) (hb : lo+b≤w.length) :
    P2Periodic.factor (shift (read w.toArray fallback) lo) a b=
      Spec.slice w (lo+a) (lo+b) := by
  unfold P2Periodic.factor Spec.slice
  rw [shifted_segment w fallback lo a (b-a) (by omega),
    show lo+b-(lo+a)=b-a by omega]

theorem segment_fallback (text : Array α) (fallback other : α) (a L : Nat)
    (h : a+L≤text.size) :
    segment (read text fallback) a L=segment (read text other) a L := by
  rw [segment_read text fallback a L h,segment_read text other a L h]

structure Result extends SmallPeriodP2.Result where
  inputCells : Nat
  deriving Repr

/-- Materialize exactly once, before constructing the accessor closure.
    The solver obtains its input length from the materialized array. -/
def solveWord [DecidableEq α] (P : SevenDFA α) (w : Word α) (fallback : α)
    (Q : Nat) : Result :=
  let text := w.toArray
  ⟨SmallPeriodP2.solve P (read text fallback) text.size Q,text.size⟩

theorem solveWord_eq [DecidableEq α] (P : SevenDFA α) (w : Word α)
    (fallback : α) (Q : Nat) :
    (solveWord P w fallback Q).toResult=
      SmallPeriodP2.solve P (read w.toArray fallback) w.length Q := by
  simp only [solveWord,List.size_toArray]

theorem solveWord_inputCells [DecidableEq α] (P : SevenDFA α) (w : Word α)
    (fallback : α) (Q : Nat) : (solveWord P w fallback Q).inputCells=w.length := by
  simp only [solveWord,List.size_toArray]

theorem solveWord_sound [DecidableEq α] (P : SevenDFA α) (w : Word α)
    (fallback : α) (Q : Nat) (hs : (solveWord P w fallback Q).accepted=true) :
    MatchesWithin P.nested2 w 2 := by
  have hh := SmallPeriodP2.solve_sound P (read w.toArray fallback) w.length Q
    (by simpa only [solveWord,List.size_toArray] using hs)
  rwa [segment_full] at hh

/-- The finite-word entry point has the same exact cubic-run, long-outer
    completeness class as the underlying small-period solver. -/
theorem solveWord_complete [DecidableEq α] (P : SevenDFA α) (w : Word α)
    (fallback : α) (Q : Nat) (R : Bounds)
    (hR : R.Valid (read w.toArray fallback) w.length) (hq : R.period≤Q)
    (hc : 3*R.period≤R.hi-R.lo) (x : P2Periodic.Layout Nat)
    (hw : P2Periodic.Witness P (shift (read w.toArray fallback) R.lo) (R.hi-R.lo)
      (w.take R.lo) (w.drop R.hi) x)
    (hlong : R.period≤x.e-x.p) : (solveWord P w fallback Q).accepted=true := by
  have hh := SmallPeriodP2.solve_complete P (read w.toArray fallback) w.length Q R hR hq hc x
    (by simpa only [segment_full] using hw) hlong
  simpa only [solveWord,List.size_toArray] using hh

theorem solveWord_counts [DecidableEq α] (P : SevenDFA α) (w : Word α)
    (fallback : α) (Q : Nat) :
    (solveWord P w fallback Q).inputCells=w.length ∧
    (solveWord P w fallback Q).runComparisons≤
      Q*(w.length+(w.length+1)*(2*Q*(Q+1)+1)) ∧
    (solveWord P w fallback Q).contextEntries=(w.length+1)*(1+P.H.stateCount) ∧
    (solveWord P w fallback Q).cacheWork≤
      (FullyCachedP2.stateSum P*Q+Q^2)*(2*w.length*DyadicIndex.heightFor w.length) ∧
    (solveWord P w fallback Q).phaseCalls≤Q^4*(2*w.length*DyadicIndex.heightFor w.length) ∧
    (solveWord P w fallback Q).equalityReads≤6*(Q^4*(2*w.length*DyadicIndex.heightFor w.length)) := by
  refine ⟨solveWord_inputCells P w fallback Q,?_⟩
  simpa only [solveWord,List.size_toArray] using
    SmallPeriodP2.solve_counts P (read w.toArray fallback) w.length Q

theorem solveWord_projection_steps [DecidableEq α] (P : SevenDFA α) (w : Word α)
    (fallback : α) (Q : Nat) :
    (solveWord P w fallback Q).projectionSteps≤
      CountedProjection.p2Steps P*Q^4*(2*w.length*DyadicIndex.heightFor w.length) := by
  simpa only [solveWord,List.size_toArray] using
    SmallPeriodP2.solve_projection_steps P (read w.toArray fallback) w.length Q

end REWB.ArrayText
