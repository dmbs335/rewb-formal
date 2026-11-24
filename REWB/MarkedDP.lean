import REWB.Reference

/-! The marked-suffix dynamic programs underlying the quadratic column
    reduction.  Words carry a mark at each left boundary, with an independent
    mark at the terminal boundary. This avoids losing epsilon matches.
    Functions on finite states specify the DP; a concrete packed implementation
    and its machine cost remain separate obligations. -/
namespace REWB.MarkedDP
variable {α : Type}

abbrev MarkedWord (α : Type) := List (α × Bool)

def text (w : MarkedWord α) : Word α := w.map Prod.fst

def markAtHead (terminal : Bool) : MarkedWord α → Bool
  | [] => terminal
  | (_, m) :: _ => m

/-- Backward absorption of a regular language up to an eligible end. -/
def reachEnd (d : DFA α) (terminal : Bool) :
    MarkedWord α → Fin d.stateCount → Bool
  | [], q => terminal && d.final q
  | (c,m) :: xs, q => (m && d.final q) || reachEnd d terminal xs (d.step q c)

theorem reachEnd_correct (d : DFA α) (terminal : Bool)
    (w : MarkedWord α) (q : Fin d.stateCount) :
    reachEnd d terminal w q = true ↔
      ∃ pre suf, w = pre ++ suf ∧ markAtHead terminal suf = true ∧
        d.final (d.run q (text pre)) = true := by
  induction w generalizing q with
  | nil =>
    simp only [reachEnd, Bool.and_eq_true]
    constructor
    · rintro ⟨hm,hq⟩
      exact ⟨[],[],rfl,hm,hq⟩
    · rintro ⟨pre,suf,he,hm,hq⟩
      cases pre with
      | nil =>
        have hs : ([] : MarkedWord α) = suf := he
        subst suf
        exact ⟨hm,hq⟩
      | cons x xs => cases he
  | cons x xs ih =>
    rcases x with ⟨c,m⟩
    simp only [reachEnd, Bool.or_eq_true, Bool.and_eq_true, ih]
    constructor
    · intro h
      rcases h with ⟨hm,hq⟩ | ⟨pre,suf,he,hm,hq⟩
      · exact ⟨[],(c,m)::xs,rfl,hm,hq⟩
      · exact ⟨(c,m)::pre,suf,congrArg (List.cons (c,m)) he,hm,hq⟩
    · rintro ⟨pre,suf,he,hm,hq⟩
      cases pre with
      | nil =>
        have he' : (c,m)::xs = suf := he
        subst suf
        exact Or.inl ⟨hm,hq⟩
      | cons y ys =>
        have h : (c,m) = y ∧ xs = ys ++ suf := by simpa using he
        rcases h with ⟨rfl,h⟩
        exact Or.inr ⟨ys,suf,h,hm,hq⟩

/-- Statewise table recurrence: B reads the suffix after the single marked
    switch out of D. No independent choice of the two split positions. -/
structure Summary (d b : DFA α) where
  suffixAccept : Fin b.stateCount → Bool
  canSwitch : Fin d.stateCount → Bool

def summarize (d b : DFA α) (terminal : Bool) : MarkedWord α → Summary d b
  | [] => ⟨b.final, fun q => (terminal && d.final q) && b.final b.initial⟩
  | (c,m) :: xs =>
    let tail := summarize d b terminal xs
    let suffixAccept := fun q => tail.suffixAccept (b.step q c)
    ⟨suffixAccept, fun q =>
      ((m && d.final q) && suffixAccept b.initial) ||
        tail.canSwitch (d.step q c)⟩

theorem suffixAccept_correct (d b : DFA α) (terminal : Bool)
    (w : MarkedWord α) (q : Fin b.stateCount) :
    (summarize d b terminal w).suffixAccept q = b.final (b.run q (text w)) := by
  induction w generalizing q with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨c,m⟩
    exact ih (b.step q c)

theorem canSwitch_correct (d b : DFA α) (terminal : Bool)
    (w : MarkedWord α) (q : Fin d.stateCount) :
    (summarize d b terminal w).canSwitch q = true ↔
      ∃ pre suf, w = pre ++ suf ∧ markAtHead terminal suf = true ∧
        d.final (d.run q (text pre)) = true ∧ b.accepts (text suf) := by
  induction w generalizing q with
  | nil =>
    simp only [summarize, Bool.and_eq_true]
    constructor
    · rintro ⟨⟨hm,hq⟩,hb⟩
      exact ⟨[],[],rfl,hm,hq,hb⟩
    · rintro ⟨pre,suf,he,hm,hq,hb⟩
      cases pre with
      | nil =>
        have hs : ([] : MarkedWord α) = suf := he
        subst suf
        exact ⟨⟨hm,hq⟩,hb⟩
      | cons x xs => cases he
  | cons x xs ih =>
    rcases x with ⟨c,m⟩
    simp only [summarize, Bool.or_eq_true, Bool.and_eq_true,
      suffixAccept_correct, ih]
    constructor
    · intro h
      rcases h with ⟨⟨hm,hq⟩,hb⟩ | ⟨pre,suf,he,hm,hq,hb⟩
      · exact ⟨[],(c,m)::xs,rfl,hm,hq,hb⟩
      · exact ⟨(c,m)::pre,suf,congrArg (List.cons (c,m)) he,hm,hq,hb⟩
    · rintro ⟨pre,suf,he,hm,hq,hb⟩
      cases pre with
      | nil =>
        have he' : (c,m)::xs = suf := he
        subst suf
        exact Or.inl ⟨⟨hm,hq⟩,hb⟩
      | cons y ys =>
        have h : (c,m) = y ∧ xs = ys ++ suf := by simpa using he
        rcases h with ⟨rfl,h⟩
        exact Or.inr ⟨ys,suf,h,hm,hq,hb⟩

/-- Shortening two equal, disjoint copies from the left transports the
    same removed prefix into the middle gap. No group inverses needed. -/
theorem shorten_from_left (pre x u gap tail : Word α) :
    pre ++ (x ++ u) ++ gap ++ (x ++ u) ++ tail =
    (pre ++ x) ++ u ++ (gap ++ x) ++ u ++ tail := by
  simp only [List.append_assoc]

theorem shortened_gap_state (d : DFA α) (q : Fin d.stateCount)
    (gap x : Word α) :
    d.run q (gap ++ x) = d.run (d.run q gap) x :=
  d.run_append q gap x

end REWB.MarkedDP
