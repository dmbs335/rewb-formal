import REWB.ExponentIntervals

/-! Batch intersection of bounded residue-class intervals. The sorted
    two-pointer scan visits at most |sources|+|targets| pairs, rather
    than all Cartesian pairs. Sorting uses Lean's mergeSort and its
    checked permutation and order lemmas. -/
namespace REWB.IntervalSweep
open REWB.ExponentIntervals

def Hit (I J : Window) : Prop := ∃ z : Int, I.has z ∧ J.has z

def HasHit (xs ys : List Window) : Prop :=
  ∃ I,I∈xs ∧ ∃ J,J∈ys ∧ Hit I J

def Valid (xs : List Window) : Prop :=
  ∀ I,I∈xs → I.lo≤I.hi

def ordered (I J : Window) : Bool := decide (I.lo≤J.lo)

def Sorted (xs : List Window) : Prop := xs.Pairwise (fun I J=>ordered I J=true)

theorem sorted_tail {a : Window} {as : List Window} (h : Sorted (a::as)) :
    Sorted as := (List.pairwise_cons.mp h).2

theorem sorted_head {a b : Window} {as : List Window} (h : Sorted (a::as))
    (hb : b∈a::as) : a.lo≤b.lo := by
  rcases List.mem_cons.mp hb with he|hm
  · subst b
    exact Int.le_refl _
  · exact of_decide_eq_true ((List.pairwise_cons.mp h).1 b hm)

theorem discard_left (a : Window) (as : List Window) (b : Window) (bs : List Window)
    (hs : Sorted (b::bs)) (h : a.hi<b.lo) :
    HasHit (a::as) (b::bs) ↔ HasHit as (b::bs) := by
  constructor
  · rintro ⟨I,hI,J,hJ,z,hIz,hJz⟩
    rcases List.mem_cons.mp hI with he|hm
    · subst I
      have hh := sorted_head hs hJ
      have h1 := hIz.2
      have h2 := hJz.1
      omega
    · exact ⟨I,hm,J,hJ,z,hIz,hJz⟩
  · rintro ⟨I,hI,J,hJ,h⟩
    exact ⟨I,List.mem_cons.mpr (Or.inr hI),J,hJ,h⟩

theorem hit_symm (xs ys : List Window) : HasHit xs ys ↔ HasHit ys xs := by
  constructor <;> rintro ⟨I,hI,J,hJ,z,hIz,hJz⟩
  · exact ⟨J,hJ,I,hI,z,hJz,hIz⟩
  · exact ⟨J,hJ,I,hI,z,hJz,hIz⟩

theorem discard_right (a : Window) (as : List Window) (b : Window) (bs : List Window)
    (hs : Sorted (a::as)) (h : b.hi<a.lo) :
    HasHit (a::as) (b::bs) ↔ HasHit (a::as) bs :=
  (hit_symm _ _).trans ((discard_left b bs a as hs h).trans (hit_symm _ _))

theorem head_hit (a b : Window) (ha : a.lo≤a.hi) (hb : b.lo≤b.hi)
    (h1 : ¬a.hi<b.lo) (h2 : ¬b.hi<a.lo) : Hit a b := by
  refine ⟨max a.lo b.lo,?_,?_⟩
  · change a.lo≤max a.lo b.lo ∧ max a.lo b.lo≤a.hi
    exact ⟨Int.le_max_left _ _,Int.max_le.mpr ⟨ha,by omega⟩⟩
  · change b.lo≤max a.lo b.lo ∧ max a.lo b.lo≤b.hi
    exact ⟨Int.le_max_right _ _,Int.max_le.mpr ⟨by omega,hb⟩⟩

/-- Fuel is at least the sum of the list lengths. The count records
    examined pairs (each uses at most two endpoint comparisons). -/
def scan : Nat→List Window→List Window→Bool×Nat
  | 0,_,_ => (false,0)
  | _+1,[],_ => (false,0)
  | _+1,_,[] => (false,0)
  | k+1,a::as,b::bs =>
    if a.hi<b.lo then
      let r := scan k as (b::bs)
      (r.1,r.2+1)
    else if b.hi<a.lo then
      let r := scan k (a::as) bs
      (r.1,r.2+1)
    else (true,1)

theorem scan_cost (fuel : Nat) (xs ys : List Window) :
    (scan fuel xs ys).2≤fuel := by
  induction fuel generalizing xs ys with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    cases xs with
    | nil => exact Nat.zero_le _
    | cons a as =>
      cases ys with
      | nil => exact Nat.zero_le _
      | cons b bs =>
        by_cases h : a.hi<b.lo
        · rw [scan,if_pos h]
          have hh := ih as (b::bs)
          omega
        · by_cases h' : b.hi<a.lo
          · rw [scan,if_neg h,if_pos h']
            have hh := ih (a::as) bs
            omega
          · simp [scan,h,h']

theorem scan_correct (fuel : Nat) (xs ys : List Window)
    (hf : xs.length+ys.length≤fuel)
    (hx : Sorted xs) (hy : Sorted ys) (hv : Valid xs) (hw : Valid ys) :
    (scan fuel xs ys).1=true ↔ HasHit xs ys := by
  induction fuel generalizing xs ys with
  | zero =>
    cases xs <;> cases ys <;> simp_all [scan,HasHit]
  | succ k ih =>
    cases xs with
    | nil => simp [scan,HasHit]
    | cons a as =>
      cases ys with
      | nil => simp [scan,HasHit]
      | cons b bs =>
        by_cases h : a.hi<b.lo
        · rw [scan,if_pos h]
          change (scan k as (b::bs)).1=true ↔ _
          rw [ih _ _ (by simp only [List.length_cons] at hf ⊢; omega)
            (sorted_tail hx) hy (fun I hI=>hv I (by simp [hI])) hw]
          exact (discard_left a as b bs hy h).symm
        · by_cases h' : b.hi<a.lo
          · rw [scan,if_neg h,if_pos h']
            change (scan k (a::as) bs).1=true ↔ _
            rw [ih _ _ (by simp only [List.length_cons] at hf ⊢; omega)
              hx (sorted_tail hy) hv (fun I hI=>hw I (by simp [hI]))]
            exact (discard_right a as b bs hx h').symm
          · rw [scan,if_neg h,if_neg h']
            constructor
            · intro _
              exact ⟨a,by simp,b,by simp,head_hit a b (hv a (by simp)) (hw b (by simp)) h h'⟩
            · intro _
              rfl

def prepare (xs : List Window) : List Window :=
  (xs.filter (fun I=>decide (I.lo≤I.hi))).mergeSort ordered

theorem prepare_valid (xs : List Window) : Valid (prepare xs) := by
  intro I hI
  have h := List.mem_filter.mp (List.mem_mergeSort.mp hI)
  exact of_decide_eq_true h.2

theorem prepare_sorted (xs : List Window) : Sorted (prepare xs) := by
  unfold prepare Sorted
  exact List.sorted_mergeSort
    (fun a b c h1 h2=>by
      have h1' : a.lo≤b.lo := of_decide_eq_true h1
      have h2' : b.lo≤c.lo := of_decide_eq_true h2
      exact decide_eq_true (Int.le_trans h1' h2'))
    (fun a b=>by unfold ordered; omega) _

theorem prepare_length (xs : List Window) : (prepare xs).length≤xs.length := by
  unfold prepare
  rw [List.length_mergeSort]
  exact List.length_filter_le _ _

theorem prepare_hit (xs ys : List Window) :
    HasHit (prepare xs) (prepare ys) ↔ HasHit xs ys := by
  constructor
  · rintro ⟨I,hI,J,hJ,h⟩
    exact ⟨I,(List.mem_filter.mp (List.mem_mergeSort.mp hI)).1,
      J,(List.mem_filter.mp (List.mem_mergeSort.mp hJ)).1,h⟩
  · rintro ⟨I,hI,J,hJ,z,hIz,hJz⟩
    have h1 : I.lo≤I.hi := Int.le_trans hIz.1 hIz.2
    have h2 : J.lo≤J.hi := Int.le_trans hJz.1 hJz.2
    exact ⟨I,List.mem_mergeSort.mpr (List.mem_filter.mpr ⟨hI,decide_eq_true h1⟩),
      J,List.mem_mergeSort.mpr (List.mem_filter.mpr ⟨hJ,decide_eq_true h2⟩),z,hIz,hJz⟩

def batch (xs ys : List Window) : Bool×Nat :=
  let a := prepare xs
  let b := prepare ys
  scan (a.length+b.length) a b

theorem batch_correct (xs ys : List Window) :
    (batch xs ys).1=true ↔ HasHit xs ys := by
  unfold batch
  exact (scan_correct _ _ _ (Nat.le_refl _) (prepare_sorted xs) (prepare_sorted ys)
    (prepare_valid xs) (prepare_valid ys)).trans (prepare_hit xs ys)

theorem batch_cost (xs ys : List Window) :
    (batch xs ys).2≤xs.length+ys.length := by
  unfold batch
  exact Nat.le_trans (scan_cost _ _ _) (Nat.add_le_add (prepare_length xs) (prepare_length ys))

end REWB.IntervalSweep
