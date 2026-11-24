import REWB.DyadicIndex
import REWB.MatrixTable
import REWB.LCSTable

/-! The indexed marked switch used by P2. The correctness theorem explicitly
    requires a mask that represents First2. The construction of that mask by
    the outer-column DP and the full word-RAM cost are separate obligations. -/
namespace REWB.IndexedMarked
open REWB.Spec (slice)
open REWB.MarkedDP (MarkedWord)
open REWB.MarkedTransfer (Phase enum)
variable {α : Type}

abbrev Index (d b : DFA α) :=
  DyadicIndex.Tree (MatrixTable.Matrix (enum d b))

def build (d b : DFA α) (w : MarkedWord α) : Index d b × Nat :=
  DyadicIndex.buildFor (MatrixTable.ops (enum d b)) (MarkedTransfer.matrixLetters d b w)

def query (d b : DFA α) (terminal : Bool) (idx : Index d b)
    (l r : Nat) (q : Phase d b) : DyadicIndex.Result Bool :=
  let res := DyadicIndex.query (MatrixTable.ops (enum d b)) idx l r
  ⟨res.answer.map (fun m => FiniteRelation.pre (enum d b) (MatrixTable.denote m)
    (FiniteRelation.pre (enum d b) (MarkedTransfer.epsilon d b terminal)
      (MarkedTransfer.final d b)) q), res.products, res.visits⟩

theorem query_correct (d b : DFA α) (terminal : Bool)
    (w : MarkedWord α) (l r : Nat) (q : Phase d b)
    (hl : l ≤ r) (hr : r ≤ w.length) :
    (query d b terminal (build d b w).1 l r q).answer =
      some (MarkedTransfer.run d b terminal (slice w l r) q) := by
  have h := (DyadicIndex.queryFor_spec (MatrixTable.ops (enum d b))
    (MarkedTransfer.matrixLetters d b w) l r hl
    (by simpa only [MarkedTransfer.matrixLetters_length] using hr)).1
  unfold query build
  change (DyadicIndex.query (MatrixTable.ops (enum d b))
    (DyadicIndex.buildFor (MatrixTable.ops (enum d b))
      (MarkedTransfer.matrixLetters d b w)).1 l r).answer.map _ = _
  rw [h]
  simp only [Option.map,MarkedTransfer.matrixLetters_slice,MarkedTransfer.matrix_product_correct]
  rfl

theorem query_bounds (d b : DFA α) (terminal : Bool)
    (w : MarkedWord α) (l r : Nat) (q : Phase d b)
    (hl : l ≤ r) (hr : r ≤ w.length) :
    (query d b terminal (build d b w).1 l r q).products ≤ 1 ∧
      (query d b terminal (build d b w).1 l r q).visits ≤ Nat.log2 w.length+2 := by
  have h := (DyadicIndex.queryFor_spec (MatrixTable.ops (enum d b))
    (MarkedTransfer.matrixLetters d b w) l r hl
    (by simpa only [MarkedTransfer.matrixLetters_length] using hr)).2
  simpa only [query,build,MarkedTransfer.matrixLetters_length] using h

theorem build_cost (d b : DFA α) (w : MarkedWord α) :
    (build d b w).2 = (Nat.log2 w.length+1)*w.length := by
  simp only [build,DyadicIndex.buildFor_cost,MarkedTransfer.matrixLetters_length]

def decorate (m : Nat → Bool) : Nat → Word α → MarkedWord α
  | _, [] => []
  | off, c::cs => (c,m off)::decorate m (off+1) cs

theorem decorate_length (m : Nat → Bool) (off : Nat) (w : Word α) :
    (decorate m off w).length = w.length := by
  induction w generalizing off with
  | nil => rfl
  | cons c cs ih =>
    change (decorate m (off+1) cs).length+1=cs.length+1
    rw [ih]

theorem decorate_text (m : Nat → Bool) (off : Nat) (w : Word α) :
    MarkedDP.text (decorate m off w) = w := by
  induction w generalizing off with
  | nil => rfl
  | cons c cs ih =>
    change c :: MarkedDP.text (decorate m (off+1) cs) = c::cs
    rw [ih]

theorem decorate_append (m : Nat → Bool) (off : Nat) (x y : Word α) :
    decorate m off (x++y) = decorate m off x ++ decorate m (off+x.length) y := by
  induction x generalizing off with
  | nil => simp only [List.nil_append,decorate,List.length_nil,Nat.add_zero]
  | cons c cs ih =>
    change (c,m off)::decorate m (off+1) (cs++y) =
      (c,m off)::(decorate m (off+1) cs ++ decorate m (off+(cs.length+1)) y)
    rw [ih,show off+1+cs.length=off+(cs.length+1) by omega]

theorem decorate_take (m : Nat → Bool) (off : Nat) (w : Word α) (k : Nat) :
    (decorate m off w).take k = decorate m off (w.take k) := by
  induction k generalizing off w with
  | zero => rfl
  | succ k ih =>
    cases w with
    | nil => rfl
    | cons c cs =>
      change (c,m off)::(decorate m (off+1) cs).take k =
        (c,m off)::decorate m (off+1) (cs.take k)
      rw [ih]

theorem decorate_drop (m : Nat → Bool) (off : Nat) (w : Word α) (k : Nat) :
    (decorate m off w).drop k = decorate m (off+k) (w.drop k) := by
  induction k generalizing off w with
  | zero => rfl
  | succ k ih =>
    cases w with
    | nil => rfl
    | cons c cs =>
      change (decorate m (off+1) cs).drop k = decorate m (off+(k+1)) (cs.drop k)
      rw [ih,show off+1+k=off+(k+1) by omega]

theorem decorate_slice (m : Nat → Bool) (w : Word α) (l r : Nat) :
    slice (decorate m 0 w) l r = decorate m l (slice w l r) := by
  simp only [slice,decorate_drop,decorate_take,Nat.zero_add]

private theorem take_prefix {X : Type} (x y : List X) :
    (x++y).take x.length = x := by
  induction x with
  | nil => rfl
  | cons c cs ih =>
    change c::(cs++y).take cs.length=c::cs
    rw [ih]

private theorem drop_prefix {X : Type} (x y : List X) :
    (x++y).drop x.length = y := by
  induction x with
  | nil => rfl
  | cons c cs ih => exact ih

theorem mark_after_drop (m : Nat → Bool) (off : Nat) (w : Word α) (k : Nat)
    (hk : k ≤ w.length) :
    MarkedDP.markAtHead (m (off+w.length)) (decorate m (off+k) (w.drop k)) =
      m (off+k) := by
  cases h : w.drop k with
  | nil =>
    have hh := congrArg List.length h
    rw [List.length_drop,List.length_nil] at hh
    have he : k=w.length := by omega
    simp only [decorate,MarkedDP.markAtHead,he]
  | cons c cs => rfl

theorem switch_iff_offset (d b : DFA α) (m : Nat → Bool) (off : Nat)
    (w : Word α) (q : Fin d.stateCount) :
    MarkedTransfer.run d b (m (off+w.length)) (decorate m off w) (.inl q) = true ↔
      ∃ k, k ≤ w.length ∧ m (off+k)=true ∧
        d.final (d.run q (w.take k))=true ∧ b.accepts (w.drop k) := by
  rw [MarkedTransfer.run_correct]
  constructor
  · rintro ⟨pre,suf,he,hm,hd,hb⟩
    let k := pre.length
    have hlen := congrArg List.length he
    rw [decorate_length,List.length_append] at hlen
    have hk : k ≤ w.length := by dsimp [k]; omega
    have hp : decorate m off (w.take k) = pre := by
      rw [← decorate_take,he]
      exact take_prefix pre suf
    have hs : decorate m (off+k) (w.drop k) = suf := by
      rw [← decorate_drop,he]
      exact drop_prefix pre suf
    refine ⟨k,hk,?_,?_,?_⟩
    · rw [← hs,mark_after_drop m off w k hk] at hm
      exact hm
    · rw [← hp,decorate_text] at hd
      exact hd
    · rw [← hs,decorate_text] at hb
      exact hb
  · rintro ⟨k,hk,hm,hd,hb⟩
    let pre := decorate m off (w.take k)
    let suf := decorate m (off+k) (w.drop k)
    have he : decorate m off w = pre++suf := by
      have hlen : (w.take k).length=k := by rw [List.length_take,Nat.min_eq_left hk]
      calc
        decorate m off w = decorate m off (w.take k ++ w.drop k) :=
          congrArg (decorate m off) (List.take_append_drop k w).symm
        _ = _ := by rw [decorate_append,hlen]
    refine ⟨pre,suf,he,?_,?_,?_⟩
    · simpa only [suf,mark_after_drop m off w k hk] using hm
    · simpa only [pre,decorate_text] using hd
    · simpa only [suf,decorate_text] using hb

private theorem take_slice (w : Word α) (l i r : Nat)
    (hl : l ≤ i) (hi : i ≤ r) (hr : r ≤ w.length) :
    (slice w l r).take (i-l) = slice w l i := by
  have hlen := OuterColumn.slice_length w l i hl (by omega)
  rw [OuterColumn.slice_split w l i r hl hi,← hlen]
  exact take_prefix _ _

private theorem drop_slice (w : Word α) (l i r : Nat)
    (hl : l ≤ i) (hi : i ≤ r) (hr : r ≤ w.length) :
    (slice w l r).drop (i-l) = slice w i r := by
  have hlen := OuterColumn.slice_length w l i hl (by omega)
  rw [OuterColumn.slice_split w l i r hl hi,← hlen]
  exact drop_prefix _ _

theorem switch_iff_indices (d b : DFA α) (m : Nat → Bool) (w : Word α)
    (l r : Nat) (q : Fin d.stateCount) (hl : l ≤ r) (hr : r ≤ w.length) :
    MarkedTransfer.run d b (m r) (decorate m l (slice w l r)) (.inl q) = true ↔
      ∃ i, l ≤ i ∧ i ≤ r ∧ m i=true ∧
        d.final (d.run q (slice w l i))=true ∧ b.accepts (slice w i r) := by
  have hlen := OuterColumn.slice_length w l r hl hr
  have hterm : l+(slice w l r).length=r := by omega
  have h := switch_iff_offset d b m l (slice w l r) q
  rw [hterm] at h
  rw [h]
  constructor
  · rintro ⟨k,hk,hm,hd,hb⟩
    let i := l+k
    have hli : l ≤ i := by dsimp [i]; omega
    have hir : i ≤ r := by dsimp [i]; omega
    have he : i-l=k := by dsimp [i]; omega
    refine ⟨i,hli,hir,hm,?_,?_⟩
    · rw [← take_slice w l i r hli hir hr,he]
      exact hd
    · rw [← drop_slice w l i r hli hir hr,he]
      exact hb
  · rintro ⟨i,hli,hir,hm,hd,hb⟩
    refine ⟨i-l,by omega,?_,?_,?_⟩
    · rwa [show l+(i-l)=i by omega]
    · rw [take_slice w l i r hli hir hr]
      exact hd
    · rw [drop_slice w l i r hli hir hr]
      exact hb

/-- End-to-end indexed decision for a fixed P2 pair of inner-copy ends,
    assuming the First2 mask was computed correctly. -/
theorem p2_query (P : SevenDFA α) (w : Word α) (a t d : Nat)
    (m : Nat → Bool) (hat : a ≤ t) (ht : t ≤ w.length)
    (hm : ∀ i, i ≤ w.length → (m i=true ↔ NestedColumns.First2 P w i t)) :
    (query P.D P.C (m a) (build P.D P.C (decorate m 0 w)).1 (a-d) a
      (.inl (P.D.run P.D.initial (slice w a (t-d))))).answer = some true ↔
      NestedColumns.Anchored2 P w a t d := by
  have hlen : a ≤ (decorate m 0 w).length := by rw [decorate_length]; omega
  rw [query_correct P.D P.C (m a) (decorate m 0 w) (a-d) a
    (.inl (P.D.run P.D.initial (slice w a (t-d)))) (by omega) hlen,
    Option.some.injEq,decorate_slice,
    switch_iff_indices P.D P.C m w (a-d) a _ (by omega) (by omega)]
  constructor
  · rintro ⟨i,hlo,hhi,hmark,hd,hc⟩
    exact ⟨i,hlo,hhi,(hm i (by omega)).mp hmark,hd,hc⟩
  · rintro ⟨i,hlo,hhi,hmark,hd,hc⟩
    exact ⟨i,hlo,hhi,(hm i (by omega)).mpr hmark,hd,hc⟩

end REWB.IndexedMarked
