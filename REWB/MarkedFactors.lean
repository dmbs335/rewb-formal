import REWB.ControlShapes

/-! Constructive factor extraction for an ordinary DFA over marked text.

Given a concrete marked DFA and a fixed control word, enumerate the
finite set of states just before its markers. Each enumeration produces
ordinary DFAs for the intervening character factors. The resulting
finite union is exactly the marked DFA language on that control word.

This module takes an actual marked DFA as input. It does not assert that
`LiveCompiler.Reg` has already been converted to one; that construction
belongs to `RegularDFA`.
-/
namespace REWB.MarkedFactors
variable {α : Type}

/-- Literal factors separated by exactly the displayed control markers.
    The empty control word still has one, possibly empty, factor. -/
inductive Interleaves : List Control → List (Word α) → Word (MarkedSymbol α) → Prop where
  | last (w : Word α) : Interleaves [] [w] (w.map Sum.inl)
  | more (c : Control) (w : Word α) {cs : List Control}
      {ws : List (Word α)} {z : Word (MarkedSymbol α)} :
      Interleaves cs ws z →
      Interleaves (c::cs) (w::ws) (w.map Sum.inl++(.inr c::z))

theorem interleaves_length {cs : List Control} {ws : List (Word α)}
    {z : Word (MarkedSymbol α)} (h : Interleaves cs ws z) :
    ws.length=cs.length+1 := by
  induction h with
  | last w => rfl
  | more c w h ih => simpa using congrArg Nat.succ ih

theorem literals_controls (w : Word α) :
    (w.map (Sum.inl : α→MarkedSymbol α)).filterMap controlOf=[] := by
  induction w with
  | nil => rfl
  | cons a w ih => exact ih

theorem interleaves_controls {cs : List Control} {ws : List (Word α)}
    {z : Word (MarkedSymbol α)} (h : Interleaves cs ws z) :
    z.filterMap controlOf=cs := by
  induction h with
  | last w => exact literals_controls w
  | more c w h ih =>
    simp only [List.filterMap_append,literals_controls,List.filterMap_cons,
      controlOf,ih,List.nil_append]

theorem prepend_character {cs : List Control} {ws : List (Word α)}
    {z : Word (MarkedSymbol α)} (h : Interleaves cs ws z) (a : α) :
    ∃ us,Interleaves cs us (.inl a::z) := by
  cases h with
  | last w => exact ⟨[a::w],.last (a::w)⟩
  | more c w h => exact ⟨(a::w)::_,.more c (a::w) h⟩

/-- Every marked word has a character-factor decomposition with exactly
    its actual control word. No possible text is enumerated. -/
theorem exists_interleaves (z : Word (MarkedSymbol α)) :
    ∃ ws,Interleaves (z.filterMap controlOf) ws z := by
  induction z with
  | nil => exact ⟨[[]],.last []⟩
  | cons x z ih =>
    obtain ⟨ws,hw⟩ := ih
    cases x with
    | inl a => exact prepend_character hw a
    | inr c => exact ⟨[]::ws,.more c [] hw⟩

def acceptsFactors : List (DFA α) → List (Word α) → Prop
  | [],[] => True
  | d::ds,w::ws => d.accepts w ∧ acceptsFactors ds ws
  | _,_ => False

/-- Restrict a marked DFA to character transitions and prescribe both
    boundary states. The state space remains the original finite space. -/
def between (d : DFA (MarkedSymbol α)) (q r : Fin d.stateCount) : DFA α :=
  ⟨d.stateCount,q,(fun t a=>d.step t (.inl a)),(fun t=>decide (t=r))⟩

/-- Last factor: retain the original final-state predicate. -/
def ending (d : DFA (MarkedSymbol α)) (q : Fin d.stateCount) : DFA α :=
  ⟨d.stateCount,q,(fun t a=>d.step t (.inl a)),d.final⟩

theorem between_run (d : DFA (MarkedSymbol α)) (q r t : Fin d.stateCount)
    (w : Word α) :
    (between d q r).run t w=d.run t (w.map Sum.inl) := by
  induction w generalizing t with
  | nil => rfl
  | cons a w ih => exact ih (d.step t (.inl a))

theorem ending_run (d : DFA (MarkedSymbol α)) (q t : Fin d.stateCount)
    (w : Word α) :
    (ending d q).run t w=d.run t (w.map Sum.inl) := by
  induction w generalizing t with
  | nil => rfl
  | cons a w ih => exact ih (d.step t (.inl a))

theorem between_accepts (d : DFA (MarkedSymbol α)) (q r : Fin d.stateCount)
    (w : Word α) :
    (between d q r).accepts w ↔ d.run q (w.map Sum.inl)=r := by
  change decide ((between d q r).run q w=r)=true ↔ _
  rw [between_run,decide_eq_true_eq]

theorem ending_accepts (d : DFA (MarkedSymbol α)) (q : Fin d.stateCount)
    (w : Word α) :
    (ending d q).accepts w ↔ d.final (d.run q (w.map Sum.inl))=true := by
  change d.final ((ending d q).run q w)=true ↔ _
  rw [ending_run]

/-- One finite union branch for every sequence of boundary states.
    The transition on each fixed marker determines the next start state. -/
def families (d : DFA (MarkedSymbol α)) :
    Fin d.stateCount → List Control → List (List (DFA α))
  | q,[] => [[ending d q]]
  | q,c::cs =>
    (List.ofFn (fun r : Fin d.stateCount=>r)).flatMap fun r=>
      (families d (d.step r (.inr c)) cs).map (between d q r::·)

theorem families_cons (d : DFA (MarkedSymbol α)) (q : Fin d.stateCount)
    (c : Control) (cs : List Control) (ds : List (DFA α)) :
    ds∈families d q (c::cs) ↔
      ∃ r : Fin d.stateCount,∃ rest,
        rest∈families d (d.step r (.inr c)) cs ∧ ds=between d q r::rest := by
  simp only [families,List.mem_flatMap,List.mem_map]
  constructor
  · rintro ⟨r,_,rest,hr,he⟩
    exact ⟨r,rest,hr,he.symm⟩
  · rintro ⟨r,rest,hr,rfl⟩
    exact ⟨r,by simp,rest,hr,rfl⟩

theorem family_length (d : DFA (MarkedSymbol α)) (q : Fin d.stateCount)
    (cs : List Control) (ds : List (DFA α)) (h : ds∈families d q cs) :
    ds.length=cs.length+1 := by
  induction cs generalizing q ds with
  | nil =>
    have he : ds=[ending d q] := by simpa [families] using h
    subst ds
    rfl
  | cons c cs ih =>
    obtain ⟨r,rest,hr,rfl⟩ := (families_cons d q c cs ds).mp h
    simpa using congrArg Nat.succ (ih (d.step r (.inr c)) rest hr)

private theorem flat_length {X Y : Type} (xs : List X) (f : X→List Y)
    (k : Nat) (h : ∀ x,(f x).length=k) :
    (xs.flatMap f).length=xs.length*k := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons,List.length_append,h,ih,List.length_cons,
      Nat.add_mul,Nat.one_mul]
    omega

/-- Exact, pattern-dependent number of branches. It is independent of
    the length of every factor and of the input text. -/
theorem families_length (d : DFA (MarkedSymbol α)) (q : Fin d.stateCount)
    (cs : List Control) :
    (families d q cs).length=d.stateCount^cs.length := by
  induction cs generalizing q with
  | nil => rfl
  | cons c cs ih =>
    change ((List.ofFn (fun r : Fin d.stateCount=>r)).flatMap _).length=_
    rw [flat_length _ _ (d.stateCount^cs.length)]
    · simp [Nat.pow_succ,Nat.mul_comm]
    · intro r
      rw [List.length_map,ih]

theorem interleaved_acceptance (d : DFA (MarkedSymbol α))
    (q : Fin d.stateCount) {cs : List Control} {ws : List (Word α)}
    {z : Word (MarkedSymbol α)} (h : Interleaves cs ws z) :
    d.final (d.run q z)=true ↔
      ∃ ds∈families d q cs,acceptsFactors ds ws := by
  induction h generalizing q with
  | last w =>
    simp only [families,List.mem_cons,List.mem_nil_iff,or_false]
    constructor
    · intro hw
      exact ⟨[ending d q],rfl,(ending_accepts d q w).mpr hw,True.intro⟩
    · rintro ⟨ds,rfl,hw,_⟩
      exact (ending_accepts d q w).mp hw
  | @more c w cs ws z h ih =>
    rw [DFA.run_append]
    change d.final (d.run (d.step (d.run q (w.map Sum.inl)) (.inr c)) z)=true ↔ _
    rw [ih]
    constructor
    · rintro ⟨rest,hr,hw⟩
      let r := d.run q (w.map Sum.inl)
      refine ⟨between d q r::rest,
        (families_cons d q c cs _).mpr ⟨r,rest,hr,rfl⟩,?_,hw⟩
      exact (between_accepts d q r w).mpr rfl
    · rintro ⟨ds,hds,hws⟩
      obtain ⟨r,rest,hr,rfl⟩ := (families_cons d q c cs ds).mp hds
      have he := (between_accepts d q r w).mp hws.1
      rw [he]
      exact ⟨rest,hr,hws.2⟩

/-- Exact fixed-marker DFA factorization. No language oracle, guessed
    factor predicates, or conditional DFA closure theorem is used. -/
theorem factorization (d : DFA (MarkedSymbol α)) (cs : List Control)
    (z : Word (MarkedSymbol α)) :
    d.accepts z ∧ z.filterMap controlOf=cs ↔
      ∃ ds∈families d d.initial cs,∃ ws,
        Interleaves cs ws z ∧ acceptsFactors ds ws := by
  constructor
  · rintro ⟨ha,hcs⟩
    obtain ⟨ws,hw⟩ := exists_interleaves z
    rw [hcs] at hw
    obtain ⟨ds,hds,hacc⟩ := (interleaved_acceptance d d.initial hw).mp ha
    exact ⟨ds,hds,ws,hw,hacc⟩
  · rintro ⟨ds,hds,ws,hw,hacc⟩
    exact ⟨(interleaved_acceptance d d.initial hw).mpr ⟨ds,hds,hacc⟩,
      interleaves_controls hw⟩

end REWB.MarkedFactors
