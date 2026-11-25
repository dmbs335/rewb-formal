import REWB.FullyCachedP2
import REWB.DFACut

/-! Share exterior DFA contexts across all runs of one text. One forward
    A scan and one backward H scan materialize the boundary states.
    Preparing another run reads its two boundary rows; it does not
    consume the exterior prefix or suffix again. -/
namespace REWB.BoundaryContexts
open REWB.Periodic
variable {α : Type}

/-- Each backward step constructs exactly one row of stateCount cells. -/
def suffix (d : DFA α) : Word α→List (DFACut.Row d)×Nat
  | [] => ([DFACut.vector d id],d.stateCount)
  | c::cs =>
    let rest := suffix d cs
    let row := rest.1.headD #[]
    (DFACut.vector d (fun v=>DFACut.read d row (d.step v c))::rest.1,
      d.stateCount+rest.2)

theorem suffix_correct (d : DFA α) (w : Word α) :
    (suffix d w).1=DFACut.suffixRows d w := by
  induction w with
  | nil => rfl
  | cons c cs ih =>
    change DFACut.vector d (fun v=>DFACut.read d ((suffix d cs).1.headD #[]) (d.step v c))::
      (suffix d cs).1=_
    rw [ih]
    rfl

theorem suffix_cost (d : DFA α) (w : Word α) :
    (suffix d w).2=(w.length+1)*d.stateCount := by
  induction w with
  | nil => simp [suffix]
  | cons c cs ih =>
    change d.stateCount+(suffix d cs).2=(cs.length+1+1)*d.stateCount
    rw [ih]
    simp only [Nat.add_mul,Nat.one_mul]
    omega

structure Index (P : SevenDFA α) where
  prefixes : Array (Fin P.A.stateCount)
  suffixes : Array (DFACut.Row P.H)

/-- The count measures state entries written to the two arrays. -/
def build (P : SevenDFA α) (w : Word α) : Index P×Nat :=
  let a := IntervalDFA.countedPrefix P.A P.A.initial w
  let h := suffix P.H w
  (⟨a.1.toArray,h.1.toArray⟩,a.2+1+h.2)

theorem build_cost (P : SevenDFA α) (w : Word α) :
    (build P w).2=(w.length+1)*(1+P.H.stateCount) := by
  simp only [build,IntervalDFA.countedPrefix_spec,suffix_cost,Nat.mul_add,Nat.mul_one]

def prefixAt (P : SevenDFA α) (I : Index P) (lo : Nat) : Fin P.A.stateCount :=
  I.prefixes[lo]?.getD P.A.initial

def suffixAt (P : SevenDFA α) (I : Index P) (hi : Nat) : DFACut.Row P.H :=
  I.suffixes[hi]?.getD #[]

theorem prefixAt_correct (P : SevenDFA α) (w : Word α) (lo : Nat) (hlo : lo≤w.length) :
    prefixAt P (build P w).1 lo=P.A.run P.A.initial (w.take lo) := by
  unfold prefixAt build
  rw [IntervalDFA.countedPrefix_spec]
  dsimp only
  rw [List.getElem?_toArray,MaskScan.prefixStates_get P.A w lo hlo P.A.initial]
  rfl

theorem suffixAt_correct (P : SevenDFA α) (w : Word α) (hi : Nat) (hhi : hi≤w.length)
    (v : Fin P.H.stateCount) :
    DFACut.read P.H (suffixAt P (build P w).1 hi) v=P.H.run v (w.drop hi) := by
  have h := DFACut.suffix_get P.H w hi v hhi
  unfold suffixAt build
  dsimp only
  rw [suffix_correct,List.getElem?_toArray]
  cases he : (DFACut.suffixRows P.H w)[hi]? with
  | none => simp [he] at h
  | some row => simpa only [he,Option.map,Option.getD,Option.some.injEq] using h

def contextA (P : SevenDFA α) (I : Index P) (lo : Nat) : DFA α :=
  ⟨P.A.stateCount,prefixAt P I lo,P.A.step,P.A.final⟩

def contextH (P : SevenDFA α) (I : Index P) (hi : Nat) : DFA α :=
  let row := suffixAt P I hi
  ⟨P.H.stateCount,P.H.initial,P.H.step,fun v=>P.H.final (DFACut.read P.H row v)⟩

theorem contextA_correct (P : SevenDFA α) (w : Word α) (lo : Nat) (hlo : lo≤w.length) :
    contextA P (build P w).1 lo=contextual P.A (w.take lo) [] := by
  unfold contextA contextual
  rw [prefixAt_correct P w lo hlo]
  rfl

theorem contextH_correct (P : SevenDFA α) (w : Word α) (hi : Nat) (hhi : hi≤w.length) :
    contextH P (build P w).1 hi=contextual P.H [] (w.drop hi) := by
  have h : (fun v : Fin P.H.stateCount=>P.H.final (DFACut.read P.H
      (suffixAt P (build P w).1 hi) v))=(fun v=>P.H.final (P.H.run v (w.drop hi))) := by
    funext v
    rw [suffixAt_correct P w hi hhi v]
  unfold contextH contextual
  dsimp only
  rw [h]
  rfl

def prepareAt [DecidableEq α] (P : SevenDFA α) (s : Nat→α) (q : Nat)
    (I : Index P) (lo hi : Nat) : FullyCachedP2.Shared P :=
  let a := contextA P I lo
  let h := contextH P I hi
  ⟨a,h,(PeriodicCache.build a s q).1,
    (PeriodicCache.build P.B s q).1,(PeriodicCache.build P.C s q).1,
    (PeriodicCache.build P.D s q).1,(PeriodicCache.build P.F s q).1,
    (PeriodicCache.build P.G s q).1,(PeriodicCache.build h s q).1,
    (PhaseEqualityCache.build s q).1⟩

theorem prepareAt_correct [DecidableEq α] (P : SevenDFA α) (s : Nat→α) (q : Nat)
    (w : Word α) (lo hi : Nat) (hlo : lo≤w.length) (hhi : hi≤w.length) :
    prepareAt P s q (build P w).1 lo hi=
      FullyCachedP2.prepare P s q (w.take lo) (w.drop hi) := by
  unfold prepareAt FullyCachedP2.prepare
  rw [contextA_correct P w lo hlo,contextH_correct P w hi hhi,
    ContextCache.prepare_correct,ContextCache.prepare_correct]

/-- Counts the periodic DFA transitions and character comparisons, after
    the two exterior contexts have been read from the shared arrays. -/
def countedPrepareAt [DecidableEq α] (P : SevenDFA α) (s : Nat→α) (q : Nat)
    (I : Index P) (lo hi : Nat) : FullyCachedP2.Shared P×Nat :=
  let a := contextA P I lo
  let h := contextH P I hi
  let ta := PeriodicCache.build a s q
  let tb := PeriodicCache.build P.B s q
  let tc := PeriodicCache.build P.C s q
  let td := PeriodicCache.build P.D s q
  let tf := PeriodicCache.build P.F s q
  let tg := PeriodicCache.build P.G s q
  let th := PeriodicCache.build h s q
  let te := PhaseEqualityCache.build s q
  (⟨a,h,ta.1,tb.1,tc.1,td.1,tf.1,tg.1,th.1,te.1⟩,
    ta.2+tb.2+tc.2+td.2+tf.2+tg.2+th.2+te.2)

theorem countedPrepareAt_correct [DecidableEq α] (P : SevenDFA α) (s : Nat→α) (q : Nat)
    (I : Index P) (lo hi : Nat) :
    (countedPrepareAt P s q I lo hi).1=prepareAt P s q I lo hi := rfl

theorem countedPrepareAt_cost [DecidableEq α] (P : SevenDFA α) (s : Nat→α) (q : Nat)
    (I : Index P) (lo hi : Nat) :
    (countedPrepareAt P s q I lo hi).2=q*(FullyCachedP2.stateSum P*q)+q^3 := by
  simp only [countedPrepareAt,PeriodicCache.build_cost,PhaseEqualityCache.build_cost,
    contextA,contextH,FullyCachedP2.stateSum,Nat.add_mul,Nat.mul_add]

end REWB.BoundaryContexts
