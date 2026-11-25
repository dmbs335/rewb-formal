import REWB.BoundaryApplicationRange

/-! Backwards chronological endpoint rows, keyed by exact word ID.  Each
key caches its last touched time and a materialized DFA-state vector.
An actual shared range-map query transports the row across the skipped
interval.  Arbitrary noninjective transitions are handled by preimage.
The marked endpoint predicate below is erased proof provenance only. -/
namespace REWB.ShortOuter.Sweep
open REWB.Spec (slice)
open REWB.BoundaryApplication
variable {α : Type}

structure Cell (k : Nat) where
  stamp : Nat
  row : Vector Bool k

def emptyCell (k n : Nat) : Cell k := ⟨n,Vector.ofFn (fun _=>false)⟩

def cellAt (k : Nat) (cells : Array (Cell k)) (key : Nat) : Cell k :=
  match cells[key]? with
  | some c => c
  | none => emptyCell k 0

def move (A : DFA α) (idx : Range.Index A) (time : Nat) (seed : Bool)
    (old : Cell A.stateCount) : Cell A.stateCount×Nat :=
  let range:=Range.query A idx time old.stamp
  (⟨time,Vector.ofFn (fun q=>(seed && A.final q) || old.row.get (range.map.get q))⟩,
    range.work+6*A.stateCount+9)

structure Result (k : Nat) where
  cells : Array (Cell k)
  value : Bool
  work : Nat

def update (A : DFA α) (idx : Range.Index A) (time key : Nat) (seed : Bool)
    (cells : Array (Cell A.stateCount)) : Result A.stateCount :=
  let fresh:=move A idx time seed (cellAt A.stateCount cells key)
  ⟨cells.setIfInBounds key fresh.1,fresh.1.row.get A.initial,fresh.2+3⟩

def initial (k n keys : Nat) : Array (Cell k) := Array.replicate keys (emptyCell k n)

structure Cell.Good (A : DFA α) (w : Word α) (marked : Nat→Prop)
    (time : Nat) (c : Cell A.stateCount) : Prop where
  lower : time≤c.stamp
  upper : c.stamp≤w.length
  future : ∀ p, marked p → c.stamp≤p ∧ p≤w.length
  row_ok : ∀ q, c.row.get q=true ↔
    ∃ p, marked p ∧ A.final (A.run q (slice w c.stamp p))=true

def Good (A : DFA α) (w : Word α) (marked : Nat→Nat→Prop)
    (time : Nat) (cells : Array (Cell A.stateCount)) : Prop :=
  ∀ key, key<cells.size → Cell.Good A w (marked key) time (cellAt A.stateCount cells key)

def added (marked : Nat→Nat→Prop) (time key : Nat) (seed : Bool) : Nat→Nat→Prop :=
  fun r p=>marked r p ∨ (seed=true ∧ r=key ∧ p=time)

theorem cellAt_some (k : Nat) (cells : Array (Cell k)) (key : Nat)
    (c : Cell k) (h : cells[key]?=some c) : cellAt k cells key=c := by simp [cellAt,h]

theorem get_cellAt (k : Nat) (cells : Array (Cell k)) (key : Nat) (hk : key<cells.size) :
    cells[key]?=some (cellAt k cells key) := by
  rw [Array.getElem?_eq_getElem hk]
  simp [cellAt,Array.getElem?_eq_getElem hk]

theorem initial_good (A : DFA α) (w : Word α) (keys : Nat) :
    Good A w (fun _ _=>False) w.length (initial A.stateCount w.length keys) := by
  intro key hk
  have hk' : key<keys := by simpa [initial] using hk
  simp only [cellAt,initial,Array.getElem?_replicate,if_pos hk']
  refine ⟨Nat.le_refl _,Nat.le_refl _,by intro p hp; exact False.elim hp,?_⟩
  intro q
  simp [emptyCell,Vector.get,Vector.getElem_ofFn]

theorem Good.weaken {A : DFA α} {w : Word α} {marked : Nat→Nat→Prop}
    {time earlier : Nat} {cells : Array (Cell A.stateCount)}
    (h : Good A w marked time cells) (hle : earlier≤time) : Good A w marked earlier cells := by
  intro key hk
  have hh:=h key hk
  exact ⟨Nat.le_trans hle hh.lower,hh.upper,hh.future,hh.row_ok⟩

theorem Cell.Good.congr {A : DFA α} {w : Word α} {marked other : Nat→Prop}
    {time : Nat} {c : Cell A.stateCount} (h : Cell.Good A w marked time c)
    (he : ∀p,marked p↔other p) : Cell.Good A w other time c := by
  refine ⟨h.lower,h.upper,fun p hp=>h.future p ((he p).mpr hp),?_⟩
  intro q
  rw [h.row_ok]
  exact exists_congr (fun p=>and_congr_left (fun _=>he p))

theorem Good.congr {A : DFA α} {w : Word α} {marked other : Nat→Nat→Prop}
    {time : Nat} {cells : Array (Cell A.stateCount)} (h : Good A w marked time cells)
    (he : ∀r p,marked r p↔other r p) : Good A w other time cells :=
  fun key hk=>(h key hk).congr (he key)

theorem move_correct (A : DFA α) (w : Word α) (marked : Nat→Prop)
    (time : Nat) (seed : Bool) (old : Cell A.stateCount)
    (h : Cell.Good A w marked time old) :
    Cell.Good A w (fun p=>marked p ∨ (seed=true ∧ p=time)) time
      (move A (Range.build A w) time seed old).1 := by
  refine ⟨Nat.le_refl _,Nat.le_trans h.lower h.upper,?_,?_⟩
  · intro p hp
    rcases hp with hp|⟨_,rfl⟩
    · exact ⟨Nat.le_trans h.lower (h.future p hp).1,(h.future p hp).2⟩
    · exact ⟨Nat.le_refl _,Nat.le_trans h.lower h.upper⟩
  · intro q
    simp only [move,BoundaryIndex.Table.get_ofFn]
    change ((seed && A.final q) || old.row.get
      ((Range.query A (Range.build A w) time old.stamp).map.get q))=true ↔ _
    rw [Bool.or_eq_true,Bool.and_eq_true,h.row_ok,
      Range.query_correct A w time old.stamp h.lower h.upper]
    constructor
    · rintro (⟨hs,hA⟩|⟨p,hp,hA⟩)
      · exact ⟨time,Or.inr ⟨hs,rfl⟩,by simpa [DFA.run] using hA⟩
      · refine ⟨p,Or.inl hp,?_⟩
        rw [OuterColumn.slice_split w time old.stamp p h.lower (h.future p hp).1,DFA.run_append]
        exact hA
    · rintro ⟨p,(hp|⟨hs,rfl⟩),hA⟩
      · right
        refine ⟨p,hp,?_⟩
        rw [OuterColumn.slice_split w time old.stamp p h.lower (h.future p hp).1,DFA.run_append] at hA
        exact hA
      · exact Or.inl ⟨hs,by simpa [DFA.run] using hA⟩

@[simp] theorem update_size (A : DFA α) (idx : Range.Index A) (time key : Nat) (seed : Bool)
    (cells : Array (Cell A.stateCount)) : (update A idx time key seed cells).cells.size=cells.size := by
  simp [update]

theorem update_good (A : DFA α) (w : Word α) (marked : Nat→Nat→Prop)
    (time key : Nat) (seed : Bool) (cells : Array (Cell A.stateCount))
    (hk : key<cells.size) (h : Good A w marked time cells) :
    Good A w (added marked time key seed) time
      (update A (Range.build A w) time key seed cells).cells := by
  intro r hr
  rw [update_size] at hr
  by_cases he : key=r
  · subst r
    have hc : cellAt A.stateCount (update A (Range.build A w) time key seed cells).cells key=
        (move A (Range.build A w) time seed (cellAt A.stateCount cells key)).1 := by
      apply cellAt_some
      exact Array.getElem?_setIfInBounds_self_of_lt hk
    rw [hc]
    apply (move_correct A w (marked key) time seed _ (h key hk)).congr
    intro p
    simp only [added,true_and]
  · have hc : cellAt A.stateCount (update A (Range.build A w) time key seed cells).cells r=
        cellAt A.stateCount cells r := by
      apply cellAt_some
      change (cells.setIfInBounds key _)[r]?=_
      rw [Array.getElem?_setIfInBounds_ne he]
      exact get_cellAt _ _ _ hr
    rw [hc]
    apply (h r hr).congr
    intro p
    simp only [added,Ne.symm he,and_false,false_and,or_false]

theorem update_value (A : DFA α) (w : Word α) (marked : Nat→Nat→Prop)
    (time key : Nat) (seed : Bool) (cells : Array (Cell A.stateCount))
    (hk : key<cells.size) (h : Good A w marked time cells) :
    (update A (Range.build A w) time key seed cells).value=true ↔
      ∃p,added marked time key seed key p ∧ A.accepts (slice w time p) := by
  have hh:=(move_correct A w (marked key) time seed _ (h key hk)).row_ok A.initial
  simpa only [update,move,added,true_and,DFA.accepts] using hh

def stepBudget (k n : Nat) : Nat := 7*k+8*(n.log2+2)+13

theorem update_work (A : DFA α) (w : Word α) (marked : Nat→Nat→Prop)
    (time key : Nat) (seed : Bool) (cells : Array (Cell A.stateCount))
    (hk : key<cells.size) (h : Good A w marked time cells) :
    (update A (Range.build A w) time key seed cells).work≤stepBudget A.stateCount w.length := by
  have hh:=Range.query_work A w time (cellAt A.stateCount cells key).stamp
    (h key hk).lower (h key hk).upper
  simp only [update,move,stepBudget]
  omega

end REWB.ShortOuter.Sweep
