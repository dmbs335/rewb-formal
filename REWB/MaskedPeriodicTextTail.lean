import REWB.MaskedPeriodicTextQuery

/-! Actual full-input suffix contexts for the periodic query. The common
    tail is obtained once per run from the same range index; it is not
    copied or scanned at each phase. `query_full_correct` spells out the
    real text factors and the unchanged target-mask read.
-/
namespace REWB.MaskedPeriodic.Text
open REWB.Periodic REWB.Spec
open REWB.MaskedFiniteAction.Maps REWB.MaskedCut REWB.MaskedCut.DFAIndex
variable {α : Type}

structure TailContext (m : Nat) where
  map : Map m
  products : Nat
  visits : Nat

def prepareTail (b c e : DFA α) (idx : Index.Tree (jointEnum b c e)) (R n : Nat) :
    TailContext e.stateCount :=
  let result := DyadicIndex.query (ops (jointOps b c e) (jointEnum b c e)) idx R n
  ⟨(result.answer.map (fun summary=>summary.total.2.2)).getD (identity e.stateCount),
    result.products,result.visits⟩

theorem suffix_slice (w : Word α) (R : Nat) : slice w R w.length=w.drop R := by
  unfold slice
  rw [←List.length_drop,List.take_length]

theorem prepareTail_value (b c e : DFA α) (w : Word α) (R : Nat) (hr : R≤w.length) :
    (prepareTail b c e (DFAIndex.build b c e w).1 R w.length).map=wordMap e (w.drop R) := by
  simp only [prepareTail,DFAIndex.build]
  rw [Index.range_value (jointOps b c e) (jointEnum b c e) (letters b c e w)
    R w.length hr (by simpa only [letters_length] using Nat.le_refl w.length)]
  simp only [Option.map,Option.getD_some,trace_total,letters_slice,letters_product,jointWord,suffix_slice]

theorem prepareTail_bounds (b c e : DFA α) (w : Word α) (R : Nat) (hr : R≤w.length) :
    (prepareTail b c e (DFAIndex.build b c e w).1 R w.length).products≤1 ∧
    (prepareTail b c e (DFAIndex.build b c e w).1 R w.length).visits≤Nat.log2 w.length+2 := by
  have hb := Index.range_bounds (jointOps b c e) (jointEnum b c e) (letters b c e w)
    R w.length hr (by simpa only [letters_length] using Nat.le_refl w.length)
  simpa only [prepareTail,DFAIndex.build,letters_length] using hb

theorem slice_append_drop (w : Word α) (a R : Nat) (ha : a≤R) :
    slice w a R++w.drop R=w.drop a := by
  have hh := List.take_append_drop (R-a) (w.drop a)
  simpa only [slice,List.drop_drop,Nat.add_sub_of_le ha] using hh

/-- Complete-input suffix semantics; unlike `Witness`, no external tail
    word appears. All four compared/recognized words are actual slices
    or suffixes of `w`. -/
def FullWitness (b c e : DFA α) (w : Word α) (s R q : Nat)
    (mask : Array Bool) (base len : Nat) : Prop :=
  ∃ L k,2*q≤L ∧ s+L≤s+k*q ∧ s+k*q+L≤R ∧
    slice w s (s+L)=slice w (s+k*q) (s+k*q+L) ∧
    b.accepts (slice w s (s+L)) ∧ c.accepts (slice w (s+L) (s+k*q)) ∧
    e.accepts (w.drop (s+k*q+L)) ∧ Marked mask base len q s k

theorem tail_witness_iff (b c e : DFA α) (w : Word α) (s R q : Nat)
    (mask : Array Bool) (base len : Nat) :
    Witness b c e w (w.drop R) s R q mask base len ↔
      FullWitness b c e w s R q mask base len := by
  constructor
  · rintro ⟨L,k,hl,hd,hb,he,hB,hC,hE,hm⟩
    rw [slice_append_drop w (s+k*q+L) R hb] at hE
    exact ⟨L,k,hl,hd,hb,he,hB,hC,hE,hm⟩
  · rintro ⟨L,k,hl,hd,hb,he,hB,hC,hE,hm⟩
    exact ⟨L,k,hl,hd,hb,he,hB,hC,by rwa [slice_append_drop w (s+k*q+L) R hb],hm⟩

theorem query_full_correct (b c e : DFA α)
    (prepared : PreparedPattern b.stateCount c.stateCount e.stateCount)
    (w : Word α) (fallback : α) (s R q : Nat) (mask : Array Bool) (base len : Nat)
    (hq : 0<q) (hn : R≤w.length)
    (hp : RunGeometry.OnPeriod (ArrayText.read w.toArray fallback) s R q) :
    (query b c e prepared (DFAIndex.build b c e w).1
      (prepareTail b c e (DFAIndex.build b c e w).1 R w.length).map s R q
      (MaskedProgression.build mask base len (prepared.K*q)).counts base).result.answer=true ↔
        FullWitness b c e w s R q mask base len := by
  rw [prepareTail_value b c e w R hn,
    query_correct b c e prepared w (w.drop R) fallback s R q mask base len hq hn hp,
    tail_witness_iff]

theorem query_full_run_correct (b c e : DFA α)
    (prepared : PreparedPattern b.stateCount c.stateCount e.stateCount)
    (w : Word α) (fallback : α) (l R q s : Nat) (mask : Array Bool) (base len : Nat)
    (hr : Run (ArrayText.read w.toArray fallback) w.length l R q) (hs : l≤s) :
    (query b c e prepared (DFAIndex.build b c e w).1
      (prepareTail b c e (DFAIndex.build b c e w).1 R w.length).map s R q
      (MaskedProgression.build mask base len (prepared.K*q)).counts base).result.answer=true ↔
        FullWitness b c e w s R q mask base len := by
  rw [prepareTail_value b c e w R hr.2.1,
    query_run_correct b c e prepared w (w.drop R) fallback l R q s mask base len hr hs,
    tail_witness_iff]

end REWB.MaskedPeriodic.Text
