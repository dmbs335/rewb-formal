import REWB.IntervalDFA

/-! A seed event (a,q) is scattered into one bounded-state bucket.
    Repeated events are deduplicated by MaskScan.tab, so the size of
    a bucket is bounded by the fixed state enumeration, not by n. -/
namespace REWB.SeedBuckets
open REWB.MaskScan
variable {α : Type}

abbrev Table (d : DFA α) := Array (Bits d)

def read (d : DFA α) (arr : Table d) (i : Nat) : Bits d :=
  arr[i]?.getD []

def insert (d : DFA α) (arr : Table d) (ev : Nat × Fin d.stateCount) : Table d :=
  if h : ev.1 < arr.size then
    arr.set ev.1 (tab d (fun q => bit d (read d arr ev.1) q || decide (q=ev.2))) h
  else arr

theorem insert_size (d : DFA α) (arr : Table d) (ev : Nat × Fin d.stateCount) :
    (insert d arr ev).size=arr.size := by
  unfold insert
  split <;> simp_all

theorem insert_correct (d : DFA α) (arr : Table d) (ev : Nat × Fin d.stateCount)
    (i : Nat) (hi : i<arr.size) (q : Fin d.stateCount) :
    bit d (read d (insert d arr ev) i) q=true ↔
      bit d (read d arr i) q=true ∨ ev=(i,q) := by
  rcases ev with ⟨a,s⟩
  by_cases ha : a<arr.size
  · by_cases he : a=i
    · subst a
      unfold insert read
      simp only [hi,dif_pos]
      rw [Array.getElem?_set]
      simp only [hi,if_true,Option.getD,bit_tab,Bool.or_eq_true,decide_eq_true_eq,Prod.mk.injEq,true_and]
      rw [eq_comm (a:=q) (b:=s)]
    · unfold insert
      simp only [ha,dif_pos]
      unfold read
      rw [Array.getElem?_set]
      simp [he,Ne.symm he]
  · have he : a≠i := by omega
    simp [insert,ha,he]

def fill (d : DFA α) : Table d → List (Nat × Fin d.stateCount) → Table d
  | arr, [] => arr
  | arr, ev::es => fill d (insert d arr ev) es

theorem fill_size (d : DFA α) (arr : Table d) (es : List (Nat × Fin d.stateCount)) :
    (fill d arr es).size=arr.size := by
  induction es generalizing arr with
  | nil => rfl
  | cons ev es ih =>
    change (fill d (insert d arr ev) es).size=arr.size
    rw [ih,insert_size]

theorem fill_correct (d : DFA α) (arr : Table d) (es : List (Nat × Fin d.stateCount))
    (i : Nat) (hi : i<arr.size) (q : Fin d.stateCount) :
    bit d (read d (fill d arr es) i) q=true ↔
      bit d (read d arr i) q=true ∨ (i,q)∈es := by
  induction es generalizing arr with
  | nil => simp [fill]
  | cons ev es ih =>
    change bit d (read d (fill d (insert d arr ev) es) i) q=true ↔ _
    rw [ih _ (by rw [insert_size]; exact hi),insert_correct d arr ev i hi q]
    simp only [List.mem_cons]
    constructor
    · rintro ((h|h)|h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h.symm)
      · exact Or.inr (Or.inr h)
    · rintro (h|(h|h))
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h.symm)
      · exact Or.inr h

def build (d : DFA α) (n : Nat) (es : List (Nat × Fin d.stateCount)) : Table d :=
  fill d (Array.replicate (n+1) []) es

theorem build_correct (d : DFA α) (n : Nat) (es : List (Nat × Fin d.stateCount))
    (i : Nat) (hi : i≤n) (q : Fin d.stateCount) :
    bit d (read d (build d n es) i) q=true ↔ (i,q)∈es := by
  unfold build
  rw [fill_correct d _ es i (by simp; omega) q]
  have hz : read d (Array.replicate (n+1) []) i=[] := by
    unfold read
    simp [Array.getElem?_replicate]
  simp [hz,bit]

end REWB.SeedBuckets
