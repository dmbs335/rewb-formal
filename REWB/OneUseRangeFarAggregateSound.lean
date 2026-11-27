import REWB.OneUseRangeFarAggregate

/-! Exact finite-row semantics of the concrete backwards DFA aggregate.
All word slices and existential endpoint searches in this file are erased
proof specifications.  The public query performs a single array access. -/
namespace REWB.OneUseRange.FarAggregate
open REWB.Spec (slice)
variable {α : Type}

def Reach (A : DFA α) (v : Array α) (bits : Array Bool)
    (l : Nat) (q : Fin A.stateCount) : Prop :=
  ∃ i, l≤i ∧ i≤v.size ∧ bit bits i=true ∧
    A.final (A.run q (slice v.toList l i))=true

theorem slice_head (v : Array α) (l i : Nat) (hl : l<v.size) (hli : l<i) :
    slice v.toList l i = v[l] :: slice v.toList (l+1) i := by
  unfold slice
  rw [List.drop_eq_getElem_cons (i := l) (by simpa using hl)]
  have hs : i-l=(i-(l+1))+1 := by omega
  rw [hs, List.take_succ_cons]
  simp

theorem reach_terminal (A : DFA α) (v : Array α) (bits : Array Bool)
    (q : Fin A.stateCount) :
    Reach A v bits v.size q ↔ bit bits v.size=true ∧ A.final q=true := by
  constructor
  · rintro ⟨i,hgi,hig,hb,hA⟩
    have hi : i=v.size := by omega
    subst i
    simpa [OuterColumn.slice_self, DFA.run] using And.intro hb hA
  · rintro ⟨hb,hA⟩
    exact ⟨v.size, Nat.le_refl _, Nat.le_refl _, hb, by simpa [DFA.run] using hA⟩

theorem reach_step (A : DFA α) (v : Array α) (bits : Array Bool)
    (l : Nat) (hl : l<v.size) (q : Fin A.stateCount) :
    Reach A v bits l q ↔
      (bit bits l=true ∧ A.final q=true) ∨
      Reach A v bits (l+1) (A.step q v[l]) := by
  constructor
  · rintro ⟨i,hli,hig,hb,hA⟩
    by_cases he : i=l
    · subst i
      exact Or.inl ⟨hb, by simpa [DFA.run] using hA⟩
    · exact Or.inr ⟨i, by omega, hig, hb, by
        rw [slice_head v l i hl (by omega)] at hA
        exact hA⟩
  · rintro (⟨hb,hA⟩ | ⟨i,hli,hig,hb,hA⟩)
    · exact ⟨l, Nat.le_refl _, by omega, hb, by simpa [DFA.run] using hA⟩
    · exact ⟨i, by omega, hig, hb, by
        rw [slice_head v l i hl (by omega)]
        exact hA⟩

def RowGood (A : DFA α) (v : Array α) (bits : Array Bool)
    (n : Nat) (row : Vector Bool A.stateCount) : Prop :=
  ∀ q, row.get q=true ↔ Reach A v bits n q

def AnswersGood (A : DFA α) (v : Array α) (bits : Array Bool)
    (n : Nat) (answers : Array Bool) : Prop :=
  answers.size=v.size-n+1 ∧
  ∀ l, n≤l → l≤v.size →
    (answers[v.size-l]?.getD false=true ↔ Reach A v bits l A.initial)

theorem terminal_correct (A : DFA α) (v : Array α) (bits : Array Bool) :
    RowGood A v bits v.size (terminal A (bit bits v.size)).1 := by
  intro q
  rw [terminal_get, Bool.and_eq_true, reach_terminal]

theorem advance_correct (A : DFA α) (v : Array α) (bits : Array Bool)
    (n : Nat) (hn : n<v.size) (row : Vector Bool A.stateCount)
    (hr : RowGood A v bits (n+1) row) :
    RowGood A v bits n (advance A v[n] (bit bits n) row).1 := by
  intro q
  rw [advance_get, Bool.or_eq_true, Bool.and_eq_true, hr, reach_step A v bits n hn]

theorem push_correct (A : DFA α) (v : Array α) (bits : Array Bool)
    (n : Nat) (hn : n<v.size) (row : Vector Bool A.stateCount)
    (answers : Array Bool) (hr : RowGood A v bits n row)
    (ha : AnswersGood A v bits (n+1) answers) :
    AnswersGood A v bits n (answers.push (row.get A.initial)) := by
  obtain ⟨hs, ha⟩ := ha
  have hsz : answers.size=v.size-n := by omega
  constructor
  · simp [hsz]
  · intro l hnl hlg
    rw [Array.getElem?_push]
    by_cases he : l=n
    · subst l
      rw [if_pos (by omega)]
      exact hr A.initial
    · rw [if_neg (by omega)]
      exact ha l (by omega) hlg

theorem initial_correct (A : DFA α) (v : Array α) (bits : Array Bool) :
    RowGood A v bits v.size (initial A bits v.size).row ∧
    AnswersGood A v bits v.size (initial A bits v.size).answers := by
  refine ⟨terminal_correct A v bits, ?_⟩
  constructor
  · simp [initial]
  · intro l hgl hlg
    have hl : l=v.size := by omega
    subst l
    simpa [initial] using terminal_correct A v bits A.initial

theorem sweep_correct (A : DFA α) (v : Array α) (bits : Array Bool)
    (n : Nat) (hn : n≤v.size) (st : State A.stateCount)
    (hr : RowGood A v bits n st.row)
    (ha : AnswersGood A v bits n st.answers) :
    RowGood A v bits 0 (sweep A v bits n hn st).row ∧
    AnswersGood A v bits 0 (sweep A v bits n hn st).answers := by
  induction n generalizing st with
  | zero => exact ⟨hr,ha⟩
  | succ n ih =>
    rw [sweep]
    have hnew := advance_correct A v bits n (by omega) st.row hr
    exact ih (by omega) _ hnew (push_correct A v bits n (by omega) _ _ hnew ha)

theorem build_correct (A : DFA α) (v : Array α) (bits : Array Bool) :
    AnswersGood A v bits 0 (build A v bits).answers := by
  exact (sweep_correct A v bits v.size (Nat.le_refl _) (initial A bits v.size)
    (initial_correct A v bits).1 (initial_correct A v bits).2).2

/-- Exact original-coordinate endpoints, including `i=l` and `i=v.size`.
No condition on the physical mask-array length is required. -/
theorem query_correct (A : DFA α) (v : Array α) (bits : Array Bool) (l : Nat) :
    (query (build A v bits) l).1=true ↔
      ∃ i, l≤i ∧ i≤v.size ∧ bit bits i=true ∧ A.accepts (slice v.toList l i) := by
  by_cases hl : l≤v.size
  · simpa only [query, build_length, if_pos hl, DFA.accepts, Reach] using
      (build_correct A v bits).2 l (Nat.zero_le _) hl
  · simp only [query, build_length, if_neg hl, Bool.false_eq_true, false_iff]
    rintro ⟨i,hli,hig,_,_⟩
    exact hl (Nat.le_trans hli hig)

theorem query_end (A : DFA α) (v : Array α) (bits : Array Bool) :
    (query (build A v bits) v.size).1 = (bit bits v.size && A.final A.initial) := by
  apply Bool.eq_iff_iff.mpr
  rw [query_correct, Bool.and_eq_true]
  exact reach_terminal A v bits A.initial

theorem query_zero (A : DFA α) (v : Array α) (bits : Array Bool) :
    (query (build A v bits) 0).1=true ↔
      ∃ i, i≤v.size ∧ bit bits i=true ∧ A.accepts (v.toList.take i) := by
  simpa [slice] using query_correct A v bits 0

theorem query_empty (A : DFA α) (bits : Array Bool) :
    (query (build A (#[] : Array α) bits) 0).1 =
      (bit bits 0 && A.final A.initial) := query_end A #[] bits

theorem bit_outside (bits : Array Bool) (i : Nat) (hi : bits.size≤i) :
    bit bits i=false := by simp [bit, Array.getElem?_eq_none hi]

/-- Substitution is a theorem about an already materialized input row.  It
does not postulate an endpoint-query implementation or construct that row. -/
theorem query_substitute (A : DFA α) (v : Array α) (bits : Array Bool)
    (P : Nat→Prop) (hp : ∀ i, i≤v.size → (bit bits i=true ↔ P i)) (l : Nat) :
    (query (build A v bits) l).1=true ↔
      ∃ i, l≤i ∧ i≤v.size ∧ P i ∧ A.accepts (slice v.toList l i) := by
  rw [query_correct]
  constructor
  · rintro ⟨i,hli,hig,hb,hA⟩
    exact ⟨i,hli,hig,(hp i hig).mp hb,hA⟩
  · rintro ⟨i,hli,hig,hp',hA⟩
    exact ⟨i,hli,hig,(hp i hig).mpr hp',hA⟩

theorem slice_prefix (w : Word α) (g l i : Nat) (hi : i≤g) :
    slice (w.take g) l i = slice w l i := by
  simp only [slice, List.drop_take, List.take_take]
  congr 1
  omega

/-- The prebuilt word array may be a prefix of a larger text; the reported
interval keeps the original absolute coordinates. -/
theorem query_prefix_correct (A : DFA α) (w : Word α) (g : Nat)
    (hg : g≤w.length) (bits : Array Bool) (l : Nat) :
    (query (build A (w.take g).toArray bits) l).1=true ↔
      ∃ i, l≤i ∧ i≤g ∧ bit bits i=true ∧ A.accepts (slice w l i) := by
  rw [query_correct]
  simp only [List.size_toArray, List.length_take, Nat.min_eq_left hg, List.toList_toArray]
  constructor
  · rintro ⟨i,hli,hig,hb,hA⟩
    exact ⟨i,hli,hig,hb,by simpa only [slice_prefix w g l i hig] using hA⟩
  · rintro ⟨i,hli,hig,hb,hA⟩
    exact ⟨i,hli,hig,hb,by simpa only [slice_prefix w g l i hig] using hA⟩

theorem query_prefix_substitute (A : DFA α) (w : Word α) (g : Nat)
    (hg : g≤w.length) (bits : Array Bool) (P : Nat→Prop)
    (hp : ∀ i, i≤g → (bit bits i=true ↔ P i)) (l : Nat) :
    (query (build A (w.take g).toArray bits) l).1=true ↔
      ∃ i, l≤i ∧ i≤g ∧ P i ∧ A.accepts (slice w l i) := by
  rw [query_prefix_correct A w g hg]
  constructor
  · rintro ⟨i,hli,hig,hb,hA⟩
    exact ⟨i,hli,hig,(hp i hig).mp hb,hA⟩
  · rintro ⟨i,hli,hig,hp',hA⟩
    exact ⟨i,hli,hig,(hp i hig).mpr hp',hA⟩

/-- If a separate concrete all-start computation has supplied a correct
finite row, the very same built index aggregates its answers.  This theorem
makes no claim that `build` itself computes the all-start row. -/
theorem query_maskedStart (A B C E : DFA α) (w : Word α) (g : Nat)
    (hg : g≤w.length) (bits : Array Bool) (mask : Nat→Bool)
    (hb : ∀ i, i≤g → (bit bits i=true ↔ Spec.maskedStart B C E w mask i)) (l : Nat) :
    (query (build A (w.take g).toArray bits) l).1=true ↔
      ∃ i, l≤i ∧ i≤g ∧ Spec.maskedStart B C E w mask i ∧ A.accepts (slice w l i) :=
  query_prefix_substitute A w g hg bits _ hb l

end REWB.OneUseRange.FarAggregate
