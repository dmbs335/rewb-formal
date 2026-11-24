import REWB.OuterTables

/-! A complete executable matcher for each of the two nested normal forms.
    There are no externally supplied masks or substring-equality oracles.
    Every endpoint column builds its index once, outside its inner loop.
    The present indices have logarithmic routing and quadratic-space tables;
    this is not the strongly subquadratic algorithm. -/
namespace REWB.Integrated
open REWB.Spec (slice)
open REWB.OuterTables
open REWB.IndexedMarked (decorate)
variable {α : Type}

def test1 (P : SevenDFA α) (I : Prepared P) (m : Nat→Bool)
    (idx : P1Index.Indices P) (t a : Nat) : Bool :=
  let d := common P I a t
  (P1Index.query P idx (m t) a (t-d) t (aAt P I (a-d))).getD false

def test2 (P : SevenDFA α) (I : Prepared P) (m : Nat→Bool)
    (idx : IndexedMarked.Index P.D P.C) (t a : Nat) : Bool :=
  let d := common P I a t
  (IndexedMarked.query P.D P.C (m a) idx (a-d) a
    (.inl (dAt P I a (t-d)))).answer.getD false

/-- A Boolean result obtained from an optional query succeeds exactly
    when that query returns some true. -/
theorem option_true (o : Option Bool) :
    o.getD false=true ↔ o=some true := by
  cases o with
  | none => simp
  | some b => cases b <;> simp

theorem test1_correct [DecidableEq α] (P : SevenDFA α) (w : Word α)
    (m : Nat→Bool) (a t : Nat) (hat : a≤t) (ht : t≤w.length)
    (hm : ∀ p, p≤w.length → (m p=true ↔ NestedColumns.Ready P w p t)) :
    test1 P (prepare P w) m (P1Index.build P (decorate m 0 w)) t a=true ↔
      NestedColumns.Anchored1 P w a t (OuterColumn.maxCommon w a t a) := by
  have hd := OuterColumn.maxCommon_isMax w a t
  have hbound : OuterColumn.maxCommon w a t a≤t-a := hd.1.2.1
  unfold test1
  rw [common_correct P w a t hat ht]
  dsimp only
  rw [aAt_correct P w _ (by omega),option_true]
  exact P1Index.p1_query P w a t _ m hat ht hbound hm

theorem test2_correct [DecidableEq α] (P : SevenDFA α) (w : Word α)
    (m : Nat→Bool) (a t : Nat) (hat : a≤t) (ht : t≤w.length)
    (hm : ∀ i, i≤w.length → (m i=true ↔ NestedColumns.First2 P w i t)) :
    test2 P (prepare P w) m (IndexedMarked.build P.D P.C (decorate m 0 w)).1 t a=true ↔
      NestedColumns.Anchored2 P w a t (OuterColumn.maxCommon w a t a) := by
  have hd := OuterColumn.maxCommon_isMax w a t
  have hbound : OuterColumn.maxCommon w a t a≤t-a := hd.1.2.1
  unfold test2
  rw [common_correct P w a t hat ht]
  dsimp only
  rw [dAt_correct P w a _ (by omega) (by omega),option_true]
  exact IndexedMarked.p2_query P w a t _ m hat ht hm

def col1 (P : SevenDFA α) (w : Word α) (I : Prepared P) (R : ReadyTable P)
    (t : Nat) : Bool :=
  let m := fun p => readyAt P R p t
  let idx := P1Index.build P (decorate m 0 w)
  (List.range (t+1)).any (test1 P I m idx t)

def col2 (P : SevenDFA α) (w : Word α) (I : Prepared P) (R : ReadyTable P)
    (t : Nat) : Bool :=
  let r := fun p => readyAt P R p t
  let row := MaskScan.first2Row P w r
  let m := MaskScan.accepted P.B row
  let idx := (IndexedMarked.build P.D P.C (decorate m 0 w)).1
  (List.range (t+1)).any (test2 P I m idx t)

theorem col1_correct [DecidableEq α] (P : SevenDFA α) (w : Word α)
    (t : Nat) (ht : t≤w.length) :
    col1 P w (prepare P w) (buildReady P w (prepare P w)) t=true ↔
      ∃ a, a≤t ∧ NestedColumns.Anchored1 P w a t (OuterColumn.maxCommon w a t a) := by
  unfold col1
  rw [List.any_eq_true]
  constructor
  · rintro ⟨a,ha,h⟩
    have hat : a≤t := by have := List.mem_range.mp ha; omega
    exact ⟨a,hat,(test1_correct P w _ a t hat ht
      (fun p hp=>readyAt_correct P w p t hp ht)).mp h⟩
  · rintro ⟨a,hat,h⟩
    exact ⟨a,List.mem_range.mpr (by omega),(test1_correct P w _ a t hat ht
      (fun p hp=>readyAt_correct P w p t hp ht)).mpr h⟩

theorem col2_correct [DecidableEq α] (P : SevenDFA α) (w : Word α)
    (t : Nat) (ht : t≤w.length) :
    col2 P w (prepare P w) (buildReady P w (prepare P w)) t=true ↔
      ∃ a, a≤t ∧ NestedColumns.Anchored2 P w a t (OuterColumn.maxCommon w a t a) := by
  let r := fun p => readyAt P (buildReady P w (prepare P w)) p t
  let row := MaskScan.first2Row P w r
  let m := MaskScan.accepted P.B row
  have hm : ∀ i, i≤w.length → (m i=true ↔ NestedColumns.First2 P w i t) := by
    intro i hi
    exact MaskScan.first2Row_correct P w t i r hi (fun p hp=>readyAt_correct P w p t hp ht)
  change (List.range (t+1)).any
    (test2 P (prepare P w) m (IndexedMarked.build P.D P.C (decorate m 0 w)).1 t)=true ↔ _
  rw [List.any_eq_true]
  constructor
  · rintro ⟨a,ha,h⟩
    have hat : a≤t := by have := List.mem_range.mp ha; omega
    exact ⟨a,hat,(test2_correct P w m a t hat ht hm).mp h⟩
  · rintro ⟨a,hat,h⟩
    exact ⟨a,List.mem_range.mpr (by omega),(test2_correct P w m a t hat ht hm).mpr h⟩

def match1 [DecidableEq α] (P : SevenDFA α) (w : Word α) : Bool :=
  let I := prepare P w
  let R := buildReady P w I
  (List.range (I.n+1)).any (col1 P w I R)

def match2 [DecidableEq α] (P : SevenDFA α) (w : Word α) : Bool :=
  let I := prepare P w
  let R := buildReady P w I
  (List.range (I.n+1)).any (col2 P w I R)

theorem match1_correct [DecidableEq α] (P : SevenDFA α) (w : Word α) :
    match1 P w=true ↔ MatchesWithin P.nested1 w 2 := by
  rw [NestedColumns.nested1_reduced]
  unfold match1
  rw [List.any_eq_true]
  constructor
  · rintro ⟨t,ht,h⟩
    have htn : t≤w.length := by
      have h := List.mem_range.mp ht
      change t<w.length+1 at h
      omega
    obtain ⟨a,hat,ha⟩ := (col1_correct P w t htn).mp h
    exact ⟨a,t,hat,htn,ha⟩
  · rintro ⟨a,t,hat,ht,ha⟩
    exact ⟨t,List.mem_range.mpr (by change t<w.length+1; omega),
      (col1_correct P w t ht).mpr ⟨a,hat,ha⟩⟩

theorem match2_correct [DecidableEq α] (P : SevenDFA α) (w : Word α) :
    match2 P w=true ↔ MatchesWithin P.nested2 w 2 := by
  rw [NestedColumns.nested2_reduced]
  unfold match2
  rw [List.any_eq_true]
  constructor
  · rintro ⟨t,ht,h⟩
    have htn : t≤w.length := by
      have h := List.mem_range.mp ht
      change t<w.length+1 at h
      omega
    obtain ⟨a,hat,ha⟩ := (col2_correct P w t htn).mp h
    exact ⟨a,t,hat,htn,ha⟩
  · rintro ⟨a,t,hat,ht,ha⟩
    exact ⟨t,List.mem_range.mpr (by change t<w.length+1; omega),
      (col2_correct P w t ht).mpr ⟨a,hat,ha⟩⟩

theorem match1_reference [DecidableEq α] (P : SevenDFA α) (w : Word α) :
    match1 P w=true ↔ Reference.nested1 P w=true :=
  (match1_correct P w).trans (Reference.nested1_correct P w).symm

theorem match2_reference [DecidableEq α] (P : SevenDFA α) (w : Word α) :
    match2 P w=true ↔ Reference.nested2 P w=true :=
  (match2_correct P w).trans (Reference.nested2_correct P w).symm

end REWB.Integrated
