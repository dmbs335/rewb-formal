import REWB.PeriodicCoordinates

/-! Exact simultaneous periodic constraints. All atoms retain their
    original endpoint variables, so compression does not independently
    choose inconsistent factor lengths. No Presburger solver, run
    enumeration, or subquadratic running-time theorem is assumed. -/
namespace REWB.Periodic
variable {α : Type}

structure Interval where
  lo : Coord
  hi : Coord

def Interval.Good (I : Interval) (p n : Nat) : Prop :=
  I.lo.phase<p ∧ I.hi.phase<p ∧ I.lo.pos p≤I.hi.pos p ∧ I.hi.pos p≤n

def Interval.len (I : Interval) (p : Nat) : Nat :=
  I.hi.pos p-I.lo.pos p

def Interval.value (I : Interval) (p : Nat) (f : Nat→α) : Word α :=
  segment f (I.lo.pos p) (I.len p)

def Interval.regularCode (I : Interval) (p : Nat) (f : Nat→α) (d : DFA α) : Prop :=
  ∃ D, factorDescriptor d f I.lo.phase p (residual p I.lo I.hi)=some D ∧
    D.test (copies I.lo I.hi)=true

theorem regularCode_iff (I : Interval) (p n : Nat) (f : Nat→α) (d : DFA α)
    (hp : 0<p) (h : Period f n p) (hg : I.Good p n) :
    I.regularCode p f d ↔ d.accepts (I.value p f) := by
  obtain ⟨D,hD,_,_,hc⟩ := coordinate_descriptor d h I.lo I.hi hp
    hg.1 hg.2.1 hg.2.2.1 hg.2.2.2
  unfold Interval.regularCode Interval.value Interval.len
  constructor
  · rintro ⟨E,hE,he⟩
    rw [hD] at hE
    simp only [Option.some.injEq] at hE
    subst E
    exact hc.mp he
  · intro ha
    exact ⟨D,hD,hc.mpr ha⟩

/-- The equality code only checks an affine length equality, phase
    alignment, or one short comparison inside the canonical blocks. -/
def equalityCode (I J : Interval) (p : Nat) (f : Nat→α) : Prop :=
  I.len p=J.len p ∧
    (p∣J.lo.pos p-I.lo.pos p ∨
      (I.len p<p ∧
        segment f ((I.lo.pos p)%p) (I.len p)=
          segment f ((J.lo.pos p)%p) (I.len p)))

theorem equalityCode_iff (I J : Interval) (p n : Nat) (f : Nat→α)
    (h : LeastPeriod f n p) (hi : I.Good p n) (hj : J.Good p n)
    (ho : I.lo.pos p≤J.lo.pos p) :
    equalityCode I J p f ↔ I.value p f=J.value p f := by
  have hb : J.lo.pos p+J.len p≤n := by
    unfold Interval.len
    have h1 := hj.2.2.1
    have h2 := hj.2.2.2
    omega
  unfold equalityCode Interval.value
  constructor
  · rintro ⟨hl,hcode⟩
    rw [hl] at hcode ⊢
    exact (factor_equality h _ _ _ ho hb).mpr hcode
  · intro he
    have hl := congrArg List.length he
    rw [segment_length,segment_length] at hl
    refine ⟨hl,?_⟩
    rw [hl] at he ⊢
    exact (factor_equality h _ _ _ ho hb).mp he

/-- Prefix/suffix context outside the run is absorbed into the starting
    state and accepting set, respectively. -/
def contextual (d : DFA α) (pre post : Word α) : DFA α :=
  ⟨d.stateCount,d.run d.initial pre,d.step,fun q=>d.final (d.run q post)⟩

theorem contextual_run (d : DFA α) (pre post w : Word α) (q : Fin d.stateCount) :
    (contextual d pre post).run q w=d.run q w := by
  induction w generalizing q with
  | nil => rfl
  | cons c cs ih => exact ih (d.step q c)

theorem contextual_accepts (d : DFA α) (pre w post : Word α) :
    (contextual d pre post).accepts w ↔ d.accepts (pre++w++post) := by
  unfold DFA.accepts
  rw [contextual_run d pre post w _]
  change d.final (d.run (d.run (d.run d.initial pre) w) post)=true ↔ _
  rw [DFA.run_append_three]

structure RegularAtom (α : Type) where
  dfa : DFA α
  interval : Interval

structure EqualityAtom where
  first : Interval
  second : Interval

def SystemPlain (p : Nat) (f : Nat→α)
    (regular : List (RegularAtom α)) (equal : List EqualityAtom) : Prop :=
  (∀ a,a∈regular→a.dfa.accepts (a.interval.value p f)) ∧
    (∀ a,a∈equal→a.first.value p f=a.second.value p f)

def SystemCompact (p : Nat) (f : Nat→α)
    (regular : List (RegularAtom α)) (equal : List EqualityAtom) : Prop :=
  (∀ a,a∈regular→a.interval.regularCode p f a.dfa) ∧
    (∀ a,a∈equal→equalityCode a.first a.second p f)

/-- A whole conjunction of regular and equality constraints over shared
    endpoint variables is equivalent to its periodic compression. This
    is the semantic layer before existential integer projection. -/
theorem system_iff (p n : Nat) (f : Nat→α) (h : LeastPeriod f n p)
    (regular : List (RegularAtom α)) (equal : List EqualityAtom)
    (hreg : ∀ a,a∈regular→a.interval.Good p n)
    (heq : ∀ a,a∈equal→a.first.Good p n ∧ a.second.Good p n ∧
      a.first.lo.pos p≤a.second.lo.pos p) :
    SystemCompact p f regular equal ↔ SystemPlain p f regular equal := by
  constructor
  · rintro ⟨hr,he⟩
    constructor
    · intro a ha
      exact (regularCode_iff a.interval p n f a.dfa h.1 h.2.1 (hreg a ha)).mp (hr a ha)
    · intro a ha
      obtain ⟨h1,h2,h3⟩ := heq a ha
      exact (equalityCode_iff a.first a.second p n f h h1 h2 h3).mp (he a ha)
  · rintro ⟨hr,he⟩
    constructor
    · intro a ha
      exact (regularCode_iff a.interval p n f a.dfa h.1 h.2.1 (hreg a ha)).mpr (hr a ha)
    · intro a ha
      obtain ⟨h1,h2,h3⟩ := heq a ha
      exact (equalityCode_iff a.first a.second p n f h h1 h2 h3).mpr (he a ha)

end REWB.Periodic
