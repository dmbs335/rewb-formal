import REWB.RunGeometry

/-! Extend a primitive square to its unique maximal run. This is an
    executable local reference extension; no claim of constant-time LCE
    is made. A faster implementation can replace the two scans by an
    LCE/LCS oracle satisfying the same boundary contracts. -/
namespace REWB.RunExtension
open REWB.Periodic REWB.RunGeometry
variable {α : Type} [DecidableEq α]

def left (f : Nat→α) (p : Nat) : Nat→Nat
  | 0 => 0
  | i+1 => if f i=f (i+p) then left f p i else i+1

theorem left_spec (f : Nat→α) (p i : Nat) :
    left f p i≤i ∧
      (∀ j,left f p i≤j→j<i→f j=f (j+p)) ∧
      (left f p i=0 ∨ f (left f p i-1)≠f (left f p i-1+p)) := by
  induction i with
  | zero =>
    refine ⟨Nat.le_refl _,?_,Or.inl rfl⟩
    intro j hj hlt
    omega
  | succ i ih =>
    by_cases he : f i=f (i+p)
    · rw [left,if_pos he]
      refine ⟨by omega,?_,ih.2.2⟩
      intro j hj hlt
      by_cases ht : j<i
      · exact ih.2.1 j hj ht
      · have hj' : j=i := by omega
        simpa only [hj'] using he
    · rw [left,if_neg he]
      refine ⟨Nat.le_refl _,?_,Or.inr ?_⟩
      · intro j hj hlt
        omega
      · simpa only [Nat.add_sub_cancel] using he

/-- The right scan returns the first mismatch (or the length limit).
    Its numeric argument is remaining fuel, so termination is structural. -/
def right (f : Nat→α) (p : Nat) : Nat→Nat→Nat
  | 0,i => i
  | k+1,i => if f i=f (i+p) then right f p k (i+1) else i

theorem right_spec (f : Nat→α) (p k i : Nat) :
    i≤right f p k i ∧ right f p k i≤i+k ∧
      (∀ j,i≤j→j<right f p k i→f j=f (j+p)) ∧
      (right f p k i=i+k ∨ f (right f p k i)≠f (right f p k i+p)) := by
  induction k generalizing i with
  | zero =>
    refine ⟨Nat.le_refl _,by simp [right],?_,Or.inl (by simp [right])⟩
    intro j hj hlt
    change j<i at hlt
    omega
  | succ k ih =>
    by_cases he : f i=f (i+p)
    · rw [right,if_pos he]
      have h := ih (i+1)
      refine ⟨by omega,by omega,?_,?_⟩
      · intro j hj hlt
        by_cases ht : j=i
        · simpa only [ht] using he
        · exact h.2.2.1 j (by omega) hlt
      · rcases h.2.2.2 with h'|h'
        · exact Or.inl (by omega)
        · exact Or.inr h'
    · rw [right,if_neg he]
      refine ⟨Nat.le_refl _,by omega,?_,Or.inr he⟩
      intro j hj hlt
      omega

def extend (f : Nat→α) (n i p : Nat) : Bounds :=
  ⟨left f p i,right f p (n-p-(i+p)) (i+p)+p,p⟩

theorem extend_contains (f : Nat→α) (n i p : Nat) (h : PrimitiveSquare f n i p) :
    (extend f n i p).SquareStart i := by
  have hl := (left_spec f p i).1
  have hr := (right_spec f p (n-p-(i+p)) (i+p)).1
  exact ⟨hl,by change i+2*p≤right f p (n-p-(i+p)) (i+p)+p; omega⟩

theorem extend_valid (f : Nat→α) (n i p : Nat) (h : PrimitiveSquare f n i p) :
    (extend f n i p).Valid f n := by
  let l := left f p i
  let b := right f p (n-p-(i+p)) (i+p)
  have hp := h.2.1
  have hn := h.1
  have hl := left_spec f p i
  have hr := right_spec f p (n-p-(i+p)) (i+p)
  change l≤i ∧ _ at hl
  change i+p≤b ∧ b≤i+p+(n-p-(i+p)) ∧ _ at hr
  have hP : OnPeriod f l (b+p) p := by
    intro j hj hjb
    by_cases hjl : j<i
    · exact hl.2.1 j hj hjl
    · by_cases hjm : j<i+p
      · have hh := (on_iff f i (i+2*p) p).mpr
          (show Period (shift f i) (i+2*p-i) p by
            rw [show i+2*p-i=2*p by omega]
            exact h.2.2.1)
        exact hh j (by omega) (by omega)
      · exact hr.2.2.1 j (by omega) (by omega)
  have hmin : LeastPeriod (shift f l) (b+p-l) p := by
    refine ⟨hp,(on_iff f l (b+p) p).mp hP,?_⟩
    intro q hq hQ
    have hO := (on_iff f l (b+p) q).mpr hQ
    have hh := on_restrict f l (b+p) q i (i+2*p) hO (by omega) (by omega)
    have hSq := (on_iff f i (i+2*p) q).mp hh
    rw [show i+2*p-i=2*p by omega] at hSq
    exact h.2.2.2 q hq hSq
  change Run f n l (b+p) p
  refine ⟨by omega,by omega,by omega,hmin,?_,?_⟩
  · rcases hl.2.2 with hzero|hbad
    · exact Or.inl hzero
    · by_cases hz : l=0
      · exact Or.inl hz
      · refine Or.inr (fun he=>hbad ?_)
        have hh := he 0 (by omega)
        simpa only [shift,Nat.add_zero,Nat.zero_add] using hh
  · rcases hr.2.2.2 with hend|hbad
    · exact Or.inl (by omega)
    · refine Or.inr (fun he=>hbad ?_)
      have hh := he (b-l) (by omega)
      unfold shift at hh
      rw [show l+(b-l)=b by omega,show l+(b-l+p)=b+p by omega] at hh
      exact hh

theorem extend_unique (f : Nat→α) (n i p : Nat) (h : PrimitiveSquare f n i p)
    (R : Bounds) (hR : R.Valid f n) (hp : R.period=p) (hi : R.SquareStart i) :
    R=extend f n i p :=
  square_start_unique f n R _ hR (extend_valid f n i p h) i hp hi
    (extend_contains f n i p h)

/-- A reference implementation of the equality predicate for finite
    intervals; the character function outside the interval is ignored. -/
def periodTest (f : Nat→α) (i L p : Nat) : Bool :=
  (List.range (L-p)).all (fun j=>decide (f (i+j)=f (i+j+p)))

theorem periodTest_correct (f : Nat→α) (i L p : Nat) :
    periodTest f i L p=true ↔ Period (shift f i) L p := by
  unfold periodTest
  rw [List.all_eq_true]
  constructor
  · intro h j hj
    have he := h j (List.mem_range.mpr (by omega))
    have hh := of_decide_eq_true he
    unfold shift
    rw [show i+(j+p)=i+j+p by omega]
    exact hh
  · intro h j hj
    have hh := h j (by have ht := List.mem_range.mp hj; omega)
    unfold shift at hh
    rw [show i+(j+p)=i+j+p by omega] at hh
    exact decide_eq_true hh

def squareTest (f : Nat→α) (n i p : Nat) : Bool :=
  decide (0<p ∧ i+2*p≤n) && periodTest f i (2*p) p &&
    (List.range p).all (fun q=>decide (q=0) || !periodTest f i (2*p) q)

theorem squareTest_correct (f : Nat→α) (n i p : Nat) :
    squareTest f n i p=true ↔ PrimitiveSquare f n i p := by
  unfold squareTest PrimitiveSquare LeastPeriod
  simp only [Bool.and_eq_true,decide_eq_true_eq,periodTest_correct,List.all_eq_true]
  constructor
  · rintro ⟨⟨⟨hp,hn⟩,hP⟩,hall⟩
    refine ⟨hn,hp,hP,?_⟩
    intro q hq hQ
    by_cases hle : p≤q
    · exact hle
    · have hh := hall q (List.mem_range.mpr (by omega))
      have he := (periodTest_correct f i (2*p) q).mpr hQ
      simp [show q≠0 by omega,he] at hh
  · rintro ⟨hn,hp,hP,hmin⟩
    refine ⟨⟨⟨hp,hn⟩,hP⟩,?_⟩
    intro q hq
    by_cases hz : q=0
    · simp [hz]
    · have ht := List.mem_range.mp hq
      have hh : periodTest f i (2*p) q=false := by
        cases he : periodTest f i (2*p) q
        · rfl
        · have hm := hmin q (by omega) ((periodTest_correct f i (2*p) q).mp he)
          omega
      simp [hz,hh]

/-- Explicit exhaustive enumeration used only as a correctness reference.
    It is intentionally not the claimed subquadratic run enumerator. -/
def candidates (f : Nat→α) (n : Nat) : List Bounds :=
  (List.range (n+1)).flatMap fun i =>
    ((List.range (n+1)).filter (squareTest f n i)).map (extend f n i)

def dedup : List Bounds→List Bounds
  | [] => []
  | R::Rs => if R∈Rs then dedup Rs else R::dedup Rs

theorem dedup_mem (Rs : List Bounds) (R : Bounds) :
    R∈dedup Rs ↔ R∈Rs := by
  induction Rs with
  | nil => rfl
  | cons S Ss ih =>
    by_cases h : S∈Ss
    · rw [dedup,if_pos h,ih,List.mem_cons]
      constructor
      · exact Or.inr
      · rintro (he|hm)
        · subst R
          exact h
        · exact hm
    · rw [dedup,if_neg h,List.mem_cons,List.mem_cons,ih]

theorem dedup_nodup (Rs : List Bounds) : (dedup Rs).Nodup := by
  induction Rs with
  | nil => exact List.nodup_nil
  | cons R Rs ih =>
    by_cases h : R∈Rs
    · rwa [dedup,if_pos h]
    · rw [dedup,if_neg h,List.nodup_cons]
      exact ⟨fun hm=>h ((dedup_mem Rs R).mp hm),ih⟩

def enumerate (f : Nat→α) (n : Nat) : List Bounds :=
  dedup (candidates f n)

theorem candidate_iff (f : Nat→α) (n : Nat) (R : Bounds) :
    R∈candidates f n ↔ R.Valid f n := by
  unfold candidates
  constructor
  · intro h
    obtain ⟨i,hi,hh⟩ := List.mem_flatMap.mp h
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hh
    exact extend_valid f n i p ((squareTest_correct f n i p).mp (List.mem_filter.mp hp).2)
  · intro h
    have hs : R.SquareStart R.lo := by
      have hh := h.2.2.1
      have hlo := h.1
      exact ⟨Nat.le_refl _,by omega⟩
    have hsq := square_start_sound f n R h R.lo hs
    have hp := hsq.1
    have he := extend_unique f n R.lo R.period hsq R h rfl hs
    exact List.mem_flatMap.mpr ⟨R.lo,List.mem_range.mpr (by omega),
      List.mem_map.mpr ⟨R.period,List.mem_filter.mpr
        ⟨List.mem_range.mpr (by omega),(squareTest_correct _ _ _ _).mpr hsq⟩,he.symm⟩⟩

theorem enumerate_correct (f : Nat→α) (n : Nat) (R : Bounds) :
    R∈enumerate f n ↔ R.Valid f n := by
  unfold enumerate
  rw [dedup_mem]
  exact candidate_iff f n R

end REWB.RunExtension
