import REWB.SeedBuckets

/-! Construct the previously assumed Outer and Ready masks. Each outer
    endpoint pair (e,f) induces at most one seed; no capture-length loop
    is used. The LCS and ordinary DFA tables are shared across columns. -/
namespace REWB.OuterTables
open REWB.Spec (slice)
open REWB.MaskScan (Bits bit)
variable {α : Type}

def tabulate (n : Nat) (f : Nat → X) : Array X :=
  ((List.range n).map f).toArray

theorem tabulate_get (n : Nat) (f : Nat → X) (i : Nat) (hi : i<n) :
    (tabulate n f)[i]? = some (f i) := by
  simp [tabulate,List.getElem?_map,List.getElem?_range,hi]

structure Prepared (P : SevenDFA α) where
  n : Nat
  lcs : Array (Array Nat)
  g : Array (Array (Fin P.G.stateCount))
  h : Array (Array (Fin P.H.stateCount))
  d : Array (Array (Fin P.D.stateCount))
  a : Array (Fin P.A.stateCount)

def prepare [DecidableEq α] (P : SevenDFA α) (w : Word α) : Prepared P :=
  ⟨w.length,(LCSTable.buildLCS w).1,IntervalDFA.build P.G w,
    IntervalDFA.build P.H w,IntervalDFA.build P.D w,
    (MaskScan.prefixStates P.A P.A.initial w).toArray⟩

def common (P : SevenDFA α) (I : Prepared P) (e f : Nat) : Nat :=
  (LCSTable.commonAt I.lcs I.n e f).getD 0

theorem common_correct [DecidableEq α] (P : SevenDFA α) (w : Word α) (e f : Nat)
    (hef : e≤f) (hf : f≤w.length) :
    common P (prepare P w) e f = OuterColumn.maxCommon w e f e := by
  unfold common prepare
  rw [LCSTable.commonAt_correct w e f hef hf]
  rfl

def gAt (P : SevenDFA α) (I : Prepared P) (l r : Nat) : Fin P.G.stateCount :=
  IntervalDFA.stateAt P.G I.g l r

def dAt (P : SevenDFA α) (I : Prepared P) (l r : Nat) : Fin P.D.stateCount :=
  IntervalDFA.stateAt P.D I.d l r

def hAt (P : SevenDFA α) (I : Prepared P) (f : Nat) : Bool :=
  P.H.final (IntervalDFA.stateAt P.H I.h f I.n)

def aAt (P : SevenDFA α) (I : Prepared P) (i : Nat) : Fin P.A.stateCount :=
  I.a[i]?.getD P.A.initial

theorem gAt_correct [DecidableEq α] (P : SevenDFA α) (w : Word α) (l r : Nat)
    (hl : l≤r) (hr : r≤w.length) :
    gAt P (prepare P w) l r = P.G.run P.G.initial (slice w l r) :=
  IntervalDFA.stateAt_correct P.G w l r hl hr

theorem dAt_correct [DecidableEq α] (P : SevenDFA α) (w : Word α) (l r : Nat)
    (hl : l≤r) (hr : r≤w.length) :
    dAt P (prepare P w) l r = P.D.run P.D.initial (slice w l r) :=
  IntervalDFA.stateAt_correct P.D w l r hl hr

theorem hAt_correct [DecidableEq α] (P : SevenDFA α) (w : Word α) (f : Nat)
    (hf : f≤w.length) :
    hAt P (prepare P w) f=true ↔ P.H.accepts (slice w f w.length) := by
  unfold hAt
  change P.H.final (IntervalDFA.stateAt P.H (IntervalDFA.build P.H w) f w.length)=true ↔ _
  rw [IntervalDFA.stateAt_correct P.H w f w.length hf (Nat.le_refl _)]
  rfl

theorem aAt_correct [DecidableEq α] (P : SevenDFA α) (w : Word α) (i : Nat)
    (hi : i≤w.length) :
    aAt P (prepare P w) i = P.A.run P.A.initial (slice w 0 i) := by
  unfold aAt
  change ((MaskScan.prefixStates P.A P.A.initial w).toArray[i]?).getD P.A.initial=_
  rw [List.getElem?_toArray,MaskScan.prefixStates_get P.A w i hi P.A.initial]
  rfl

def event (P : SevenDFA α) (I : Prepared P) (e f : Nat) :
    Option (Nat × Fin P.G.stateCount) :=
  if e≤f then
    if hAt P I f then
      let d := common P I e f
      some (e-d,gAt P I e (f-d))
    else none
  else none

theorem event_correct [DecidableEq α] (P : SevenDFA α) (w : Word α)
    (e f a : Nat) (q : Fin P.G.stateCount) (hf : f≤w.length) :
    event P (prepare P w) e f=some (a,q) ↔
      e≤f ∧ a=e-OuterColumn.maxCommon w e f e ∧
      q=P.G.run P.G.initial (slice w e (f-OuterColumn.maxCommon w e f e)) ∧
      P.H.accepts (slice w f w.length) := by
  by_cases hef : e≤f
  · have hmax := OuterColumn.maxCommon_isMax w e f
    have hbound : OuterColumn.maxCommon w e f e≤f-e := hmax.1.2.1
    have hg := gAt_correct P w e (f-OuterColumn.maxCommon w e f e) (by omega) (by omega)
    have hh := hAt_correct P w f hf
    unfold event
    rw [if_pos hef]
    cases h : hAt P (prepare P w) f with
    | false =>
      have hn : ¬P.H.accepts (slice w f w.length) := by
        intro ha
        have h1 := hh.mpr ha
        rw [h] at h1
        contradiction
      simp [h,hn]
    | true =>
      have ha := hh.mp h
      simp only [h,if_true,common_correct P w e f hef hf,hg,Option.some.injEq,
        Prod.mk.injEq,hef,true_and,ha,and_true]
      constructor
      · rintro ⟨h1,h2⟩
        exact ⟨h1.symm,h2.symm⟩
      · rintro ⟨h1,h2⟩
        exact ⟨h1.symm,h2.symm⟩
  · simp [event,hef]

def events (P : SevenDFA α) (I : Prepared P) (e : Nat) :
    List (Nat × Fin P.G.stateCount) :=
  (List.range (I.n+1)).filterMap (event P I e)

theorem events_correct [DecidableEq α] (P : SevenDFA α) (w : Word α)
    (e a : Nat) (q : Fin P.G.stateCount) :
    (a,q)∈events P (prepare P w) e ↔ OuterColumn.Seed P.G P.H w e a q := by
  unfold events OuterColumn.Seed
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨f,hf,he⟩
    have hfn : f≤w.length := by
      have h := List.mem_range.mp hf
      change f<w.length+1 at h
      omega
    obtain ⟨hef,ha,hq,hh⟩ := (event_correct P w e f a q hfn).mp he
    exact ⟨f,hef,hfn,ha,hq,hh⟩
  · rintro ⟨f,hef,hfn,ha,hq,hh⟩
    refine ⟨f,List.mem_range.mpr (by change f<w.length+1; omega),?_⟩
    exact (event_correct P w e f a q hfn).mpr ⟨hef,ha,hq,hh⟩

def seeds (P : SevenDFA α) (I : Prepared P) (e : Nat) : Nat→Bits P.G :=
  let arr := SeedBuckets.build P.G I.n (events P I e)
  fun a => SeedBuckets.read P.G arr a

theorem seeds_correct [DecidableEq α] (P : SevenDFA α) (w : Word α)
    (e a : Nat) (ha : a≤w.length) (q : Fin P.G.stateCount) :
    bit P.G (seeds P (prepare P w) e a) q=true ↔ OuterColumn.Seed P.G P.H w e a q := by
  change bit P.G (SeedBuckets.read P.G (SeedBuckets.build P.G w.length
    (events P (prepare P w) e)) a) q=true ↔ _
  rw [SeedBuckets.build_correct P.G _ _ _ ha q,events_correct]

def column (P : SevenDFA α) (w : Word α) (I : Prepared P) (e : Nat) :
    Array (Bits P.G) :=
  MaskScan.forward P.G w (seeds P I e)

def outerBit (P : SevenDFA α) (col : Array (Bits P.G)) (p e : Nat) : Bool :=
  if p≤e then MaskScan.accepted P.G col p else false

theorem column_correct [DecidableEq α] (P : SevenDFA α) (w : Word α)
    (e p : Nat) (he : e≤w.length) (hp : p≤w.length) :
    outerBit P (column P w (prepare P w) e) p e=true ↔ NestedColumns.Outer P w p e := by
  by_cases hpe : p≤e
  · unfold outerBit
    rw [if_pos hpe]
    rw [NestedColumns.Outer,OuterColumn.column_correct P.G P.H w e p hpe]
    simp only [MaskScan.accepted,FiniteRelation.any_true,Bool.and_eq_true,column,
      MaskScan.forward_correct P.G w _ p hp]
    constructor
    · rintro ⟨q,⟨a,q0,ha,hs,hr⟩,hf⟩
      exact ⟨q,⟨a,q0,ha,(seeds_correct P w e a (by omega) q0).mp hs,hr⟩,hf⟩
    · rintro ⟨q,⟨a,q0,ha,hs,hr⟩,hf⟩
      exact ⟨q,⟨a,q0,ha,(seeds_correct P w e a (by omega) q0).mpr hs,hr⟩,hf⟩
  · have hn : ¬NestedColumns.Outer P w p e := by
      rintro ⟨f,hf⟩
      exact hpe hf.1
    simp [outerBit,hpe,hn]

abbrev OuterTable (P : SevenDFA α) := Array (Array (Bits P.G))

def buildOuter (P : SevenDFA α) (w : Word α) (I : Prepared P) : OuterTable P :=
  tabulate (I.n+1) (column P w I)

def outerAt (P : SevenDFA α) (T : OuterTable P) (p e : Nat) : Bool :=
  outerBit P (T[e]?.getD #[]) p e

theorem outerAt_correct [DecidableEq α] (P : SevenDFA α) (w : Word α)
    (p e : Nat) (hp : p≤w.length) (he : e≤w.length) :
    outerAt P (buildOuter P w (prepare P w)) p e=true ↔ NestedColumns.Outer P w p e := by
  unfold outerAt buildOuter
  rw [tabulate_get _ _ e (by change e<w.length+1; omega)]
  exact column_correct P w e p he hp

abbrev ReadyTable (P : SevenDFA α) := Array (Array (Bits P.F))

def buildReady (P : SevenDFA α) (w : Word α) (I : Prepared P) : ReadyTable P :=
  let outer := buildOuter P w I
  tabulate (I.n+1) (fun p => MaskScan.readyRow P w (fun e => outerAt P outer p e))

def readyAt (P : SevenDFA α) (T : ReadyTable P) (p t : Nat) : Bool :=
  MaskScan.rowBit P.F (T[p]?.getD #[]) t P.F.initial

theorem readyAt_correct [DecidableEq α] (P : SevenDFA α) (w : Word α)
    (p t : Nat) (hp : p≤w.length) (ht : t≤w.length) :
    readyAt P (buildReady P w (prepare P w)) p t=true ↔ NestedColumns.Ready P w p t := by
  unfold readyAt buildReady
  rw [tabulate_get _ _ p (by change p<w.length+1; omega)]
  change MaskScan.rowBit P.F (MaskScan.readyRow P w
    (fun e=>outerAt P (buildOuter P w (prepare P w)) p e)) t P.F.initial=true ↔ _
  exact MaskScan.readyRow_correct P w p t _ ht
    (fun e he=>outerAt_correct P w p e hp he) P.F.initial

end REWB.OuterTables
