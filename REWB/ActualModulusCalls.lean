import REWB.ActualModulus

/-! An exact arithmetic-call description of the installed left-fold modulus
constructors.  These lists are proof observations, not a new runtime pass.
Every listed pair is an actual LCM operand pair of the corresponding fold.
The instruction cost of each pair is supplied by the separately verified
concrete arithmetic program, not by a free cost oracle. -/
namespace REWB.ActualModulus.Calls
open REWB.AffineProjection

abbrev Call := Nat × Nat

structure Observation where
  value : Nat
  calls : List Call

def scan (g : X → Observation) : List X → Nat → Observation
  | [], seed => ⟨seed, []⟩
  | x :: xs, seed =>
    let one := g x
    let tail := scan g xs (Nat.lcm seed one.value)
    ⟨tail.value, one.calls ++ (seed, one.value) :: tail.calls⟩

theorem scan_value (g : X → Observation) (xs : List X) (seed : Nat) :
    (scan g xs seed).value = xs.foldl (fun a x => Nat.lcm a (g x).value) seed := by
  induction xs generalizing seed with
  | nil => rfl
  | cons x xs ih => simpa only [scan, List.foldl_cons] using ih (Nat.lcm seed (g x).value)

theorem scan_length (g : X → Observation) (xs : List X) (seed : Nat) :
    (scan g xs seed).calls.length = (xs.map (fun x => (g x).calls.length + 1)).sum := by
  induction xs generalizing seed with
  | nil => rfl
  | cons x xs ih =>
    simp only [scan, List.length_append, List.length_cons, ih, List.map_cons, List.sum_cons]
    omega

def Divides (M : Nat) (out : Observation) : Prop :=
  out.value ∣ M ∧ ∀ pair, pair ∈ out.calls → pair.1 ∣ M ∧ pair.2 ∣ M

theorem scan_divides (g : X → Observation) (xs : List X) (seed M : Nat)
    (hseed : seed ∣ M) (hg : ∀ x, x ∈ xs → Divides M (g x)) :
    Divides M (scan g xs seed) := by
  induction xs generalizing seed with
  | nil => exact ⟨hseed, by simp [scan]⟩
  | cons x xs ih =>
    have hx := hg x (by simp)
    have ht := ih (Nat.lcm seed (g x).value) (Nat.lcm_dvd hseed hx.1)
      (fun y hy => hg y (by simp [hy]))
    refine ⟨ht.1, ?_⟩
    intro pair hp
    change pair ∈ (g x).calls ++ (seed, (g x).value) :: (scan g xs (Nat.lcm seed (g x).value)).calls at hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hx.2 pair hp
    · rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨hseed, hx.1⟩
      · exact ht.2 pair hp

theorem fastFold_value (g : X → Nat × Nat) (xs : List X) (seed : Nat × Nat) :
    (xs.foldl (fun a x => ActualModulus.combine a (g x)) seed).1 =
      xs.foldl (fun a x => Nat.lcm a (g x).1) seed.1 := by
  induction xs generalizing seed with
  | nil => rfl
  | cons x xs ih => simpa only [List.foldl_cons, ActualModulus.combine] using ih (ActualModulus.combine seed (g x))

def row (C : Conj) : Observation := scan (fun a => ⟨ActualModulus.atom a, []⟩) C 1

theorem row_value (C : Conj) : (row C).value = (ActualModulus.row C).1 := by
  rw [ActualModulus.row_fast]
  simp only [row, scan_value, ActualModulus.rowFast, ActualModulus.fastFold, fastFold_value]

theorem row_length (C : Conj) : (row C).calls.length = C.length := by
  rw [row, scan_length]
  induction C with
  | nil => rfl
  | cons a as ih => simp only [List.map_cons, List.sum_cons, List.length_nil, List.length_cons] at *; omega

theorem row_divides (C : Conj) (M : Nat) (hM : 0 < M)
    (h : ∀ a, a ∈ C → ActualModulus.AtomDivides M a) : Divides M (row C) := by
  apply scan_divides _ C 1 M (Nat.one_dvd M)
  intro a ha
  exact ⟨ActualModulus.atom_dvd a M hM (h a ha), by simp⟩

def formula (F : Formula) : Observation := scan row F 1

theorem formula_value (F : Formula) : (formula F).value = (ActualModulus.formula F).1 := by
  rw [ActualModulus.formula_fast]
  simp only [formula, scan_value, row_value, ActualModulus.formulaFast,
    ActualModulus.fastFold, fastFold_value]

theorem formula_length (F : Formula) : (formula F).calls.length = ActualModulus.cells F := by
  simp only [formula, scan_length, row_length, ActualModulus.cells]

theorem formula_divides (F : Formula) (M : Nat) (hM : 0 < M)
    (h : ExponentIntervals.Compatible M F) : Divides M (formula F) := by
  apply scan_divides _ F 1 M (Nat.one_dvd M)
  intro C hC
  exact row_divides C M hM (fun a ha => h C hC a ha)

def entries (es : List TimedJoin.TimedEntry) : Observation :=
  scan (fun e => formula e.entry.formula) es 1

theorem entries_value (es : List TimedJoin.TimedEntry) :
    (entries es).value = (ActualModulus.entries es).1 := by
  rw [ActualModulus.entries_fast]
  simp only [entries, scan_value, formula_value, ActualModulus.entriesFast,
    ActualModulus.fastFold, fastFold_value]

theorem entries_length (es : List TimedJoin.TimedEntry) :
    (entries es).calls.length = ActualModulus.eventCells es := by
  simp only [entries, scan_length, formula_length, ActualModulus.eventCells]

theorem entries_divides (es : List TimedJoin.TimedEntry) (M : Nat) (hM : 0 < M)
    (h : TimedJoin.Good M es) : Divides M (entries es) := by
  apply scan_divides _ es 1 M (Nat.one_dvd M)
  intro e he
  exact formula_divides e.entry.formula M hM (h e he)

def build (es fs : List TimedJoin.TimedEntry) : Observation :=
  let a := entries es
  let b := entries fs
  ⟨Nat.lcm a.value b.value, a.calls ++ b.calls ++ [(a.value, b.value)]⟩

theorem build_value (es fs : List TimedJoin.TimedEntry) :
    (build es fs).value = (ActualModulus.build es fs).1 := by
  simp only [build, entries_value, ActualModulus.build]

theorem build_length (es fs : List TimedJoin.TimedEntry) :
    (build es fs).calls.length = ActualModulus.eventCells es + ActualModulus.eventCells fs + 1 := by
  simp only [build, List.length_append, entries_length, List.length_cons, List.length_nil]

theorem build_divides (es fs : List TimedJoin.TimedEntry) (M : Nat) (hM : 0 < M)
    (he : TimedJoin.Good M es) (hf : TimedJoin.Good M fs) : Divides M (build es fs) := by
  have ha := entries_divides es M hM he
  have hb := entries_divides fs M hM hf
  refine ⟨Nat.lcm_dvd ha.1 hb.1, ?_⟩
  intro pair hp
  change pair ∈ (entries es).calls ++ (entries fs).calls ++
    [((entries es).value, (entries fs).value)] at hp
  rcases List.mem_append.mp hp with hp | hp
  · rcases List.mem_append.mp hp with hp | hp
    · exact ha.2 pair hp
    · exact hb.2 pair hp
  · have hp' : pair = ((entries es).value, (entries fs).value) := List.mem_singleton.mp hp
    subst pair
    exact ⟨ha.1, hb.1⟩

theorem row_counter (C : Conj) : (ActualModulus.row C).2 = 2 * (row C).calls.length + 1 := by
  rw [ActualModulus.row_steps, row_length]

theorem formula_counter (F : Formula) :
    (ActualModulus.formula F).2 = 2 * (formula F).calls.length + 1 := by
  rw [ActualModulus.formula_steps, formula_length]

theorem entries_counter (es : List TimedJoin.TimedEntry) :
    (ActualModulus.entries es).2 = 2 * (entries es).calls.length + 1 := by
  rw [ActualModulus.entries_steps, entries_length]

theorem build_counter (es fs : List TimedJoin.TimedEntry) :
    (ActualModulus.build es fs).2 = 2 * (build es fs).calls.length + 1 := by
  rw [ActualModulus.build_steps, build_length]
  omega

theorem operands_le (out : Observation) (M : Nat) (hM : 0 < M)
    (h : Divides M out) (pair : Call) (hp : pair ∈ out.calls) :
    pair.1 ≤ M ∧ pair.2 ≤ M :=
  ⟨Nat.le_of_dvd hM (h.2 pair hp).1, Nat.le_of_dvd hM (h.2 pair hp).2⟩

end REWB.ActualModulus.Calls
