import REWB.OfflineJoin

/-! Geometry of maximal periodic intervals. A square of least period p
    determines a unique maximal p-run. All statements concern character
    positions, not distinct square strings. -/
namespace REWB.RunGeometry
open REWB.Periodic
variable {α : Type}

def OnPeriod (f : Nat→α) (l r p : Nat) : Prop :=
  ∀ i,l≤i → i+p<r → f i=f (i+p)

theorem on_iff (f : Nat→α) (l r p : Nat) :
    OnPeriod f l r p ↔ Period (shift f l) (r-l) p := by
  constructor
  · intro h i hi
    unfold shift
    rw [show l+(i+p)=l+i+p by omega]
    exact h (l+i) (by omega) (by omega)
  · intro h i hi hr
    have hh := h (i-l) (by omega)
    unfold shift at hh
    rw [show l+(i-l)=i by omega,show l+(i-l+p)=i+p by omega] at hh
    exact hh

theorem on_restrict (f : Nat→α) (l r p a b : Nat)
    (h : OnPeriod f l r p) (ha : l≤a) (hb : b≤r) :
    OnPeriod f a b p := by
  intro i hi hr
  exact h i (by omega) (by omega)

theorem on_extend_left (f : Nat→α) (l r p : Nat)
    (h : OnPeriod f l r p) (hl : 0<l)
    (he : f (l-1)=f (l-1+p)) : OnPeriod f (l-1) r p := by
  intro i hi hr
  by_cases hp : l≤i
  · exact h i hp hr
  · have hpos : i=l-1 := by omega
    rw [hpos]
    exact he

theorem on_extend_right (f : Nat→α) (l r p : Nat)
    (h : OnPeriod f l r p) (hp : 0<p) (hl : l+p≤r)
    (he : f (r-p)=f r) : OnPeriod f l (r+1) p := by
  intro i hi hr
  by_cases hlt : i+p<r
  · exact h i hi hlt
  · have h1 : i=r-p := by omega
    have h2 : i+p=r := by omega
    rw [h1,h2]
    exact he

/-- A length >= 2p factor of a least-period-p interval also has
    least period p, regardless of its alignment. -/
theorem least_factor (f : Nat→α) (n p a L : Nat)
    (h : LeastPeriod f n p) (hL : 2*p≤L) (hn : a+L≤n) :
    LeastPeriod (shift f a) L p := by
  refine ⟨h.1,shift_period h.2.1 hn,?_⟩
  intro q hq hQ
  by_cases hle : p≤q
  · exact hle
  · have hlt : q<p := by omega
    have he : ∀ i,i<p → f (a+i)=f (a+q+i) := by
      intro i hi
      have hh := hQ i (by omega)
      unfold shift at hh
      rw [show a+(i+q)=a+q+i by omega] at hh
      exact hh
    have hdiv := equal_long_factor_same_phase h (show a≤a+q by omega)
      (show a+q+p≤n by omega) (Nat.le_refl p) he
    rw [show a+q-a=q by omega] at hdiv
    have hc := Nat.le_of_dvd hq hdiv
    omega

theorem on_least_factor (f : Nat→α) (l r p a b : Nat)
    (h : LeastPeriod (shift f l) (r-l) p)
    (ha : l≤a) (hb : b≤r) (hlen : 2*p≤b-a) :
    LeastPeriod (shift f a) (b-a) p := by
  have hab : a≤b := by
    have hp := h.1
    omega
  have hh := least_factor (shift f l) (r-l) p (a-l) (b-a) h hlen (by omega)
  have he : shift (shift f l) (a-l)=shift f a := by
    funext i
    unfold shift
    rw [show l+(a-l+i)=a+i by omega]
  rwa [he] at hh

/-- Equal-period intervals whose intersection contains p characters
    merge into a single periodic interval. -/
theorem merge_periods (f : Nat→α) (l r a b p : Nat)
    (hl : l≤a) (ho : a+p≤r)
    (h1 : OnPeriod f l r p) (h2 : OnPeriod f a b p) :
    OnPeriod f l (max r b) p := by
  intro i hi hr
  by_cases h : i+p<r
  · exact h1 i hi h
  · have ha : a≤i := by omega
    have hb : i+p<b := by omega
    exact h2 i ha hb

theorem run_on (f : Nat→α) (n l r p : Nat) (h : Run f n l r p) :
    OnPeriod f l r p :=
  (on_iff f l r p).mpr h.2.2.2.1.2.1

/-- Two maximal p-runs overlapping in at least p characters are the
    same run. This yields a collision-free charging of run-local square
    starts to global (start,period) pairs. -/
theorem unique_overlap (f : Nat→α) (n l r a b p : Nat)
    (h1 : Run f n l r p) (h2 : Run f n a b p)
    (hlo : max l a+p≤min r b) : l=a ∧ r=b := by
  have hp := h1.2.2.2.1.1
  have hP := run_on f n l r p h1
  have hQ := run_on f n a b p h2
  have hla : l=a := by
    by_cases h : l<a
    · have he : f (a-1)=f (a-1+p) := hP _ (by omega) (by omega)
      have hx := on_extend_left f a b p hQ (by omega) he
      have hy := (on_iff f (a-1) b p).mp hx
      have hlen : b-(a-1)=b-a+1 := by
        have hh := h2.1
        omega
      rw [hlen] at hy
      rcases h2.2.2.2.2.1 with hz|hz
      · omega
      · exact False.elim (hz hy)
    · by_cases h' : a<l
      · have he : f (l-1)=f (l-1+p) := hQ _ (by omega) (by omega)
        have hx := on_extend_left f l r p hP (by omega) he
        have hy := (on_iff f (l-1) r p).mp hx
        have hlen : r-(l-1)=r-l+1 := by
          have hh := h1.1
          omega
        rw [hlen] at hy
        rcases h1.2.2.2.2.1 with hz|hz
        · omega
        · exact False.elim (hz hy)
      · omega
  subst a
  refine ⟨rfl,?_⟩
  by_cases h : r<b
  · have hl : l+p≤r := by
      have hh := h1.2.2.1
      omega
    have he : f (r-p)=f r := by
      have hh := hQ (r-p) (by omega) (by omega)
      rw [show r-p+p=r by omega] at hh
      exact hh
    have hx := on_extend_right f l r p hP hp hl he
    have hy := (on_iff f l (r+1) p).mp hx
    rw [show r+1-l=r-l+1 by have hh := h1.1; omega] at hy
    rcases h1.2.2.2.2.2 with hz|hz
    · have hh := h2.2.1
      omega
    · exact False.elim (hz hy)
  · by_cases h' : b<r
    · have hl : l+p≤b := by
        have hh := h2.2.2.1
        omega
      have he : f (b-p)=f b := by
        have hh := hP (b-p) (by omega) (by omega)
        rw [show b-p+p=b by omega] at hh
        exact hh
      have hx := on_extend_right f l b p hQ hp hl he
      have hy := (on_iff f l (b+1) p).mp hx
      rw [show b+1-l=b-l+1 by have hh := h2.1; omega] at hy
      rcases h2.2.2.2.2 with hz|hz
      · have hh := h1.2.1
        omega
      · exact False.elim (hz hy)
    · omega

structure Bounds where
  lo : Nat
  hi : Nat
  period : Nat
  deriving Repr, DecidableEq

def Bounds.Valid (f : Nat→α) (n : Nat) (R : Bounds) : Prop :=
  Run f n R.lo R.hi R.period

def Bounds.SquareStart (R : Bounds) (i : Nat) : Prop :=
  R.lo≤i ∧ i+2*R.period≤R.hi

def PrimitiveSquare (f : Nat→α) (n i p : Nat) : Prop :=
  i+2*p≤n ∧ LeastPeriod (shift f i) (2*p) p

theorem square_start_sound (f : Nat→α) (n : Nat) (R : Bounds)
    (h : R.Valid f n) (i : Nat) (hi : R.SquareStart i) :
    PrimitiveSquare f n i R.period := by
  have hn := h.2.1
  refine ⟨by have hh := hi.2; omega,?_⟩
  have hh := on_least_factor f R.lo R.hi R.period i (i+2*R.period)
    h.2.2.2.1 hi.1 hi.2 (by omega)
  rwa [show i+2*R.period-i=2*R.period by omega] at hh

theorem square_start_unique (f : Nat→α) (n : Nat) (R S : Bounds)
    (hR : R.Valid f n) (hS : S.Valid f n) (i : Nat)
    (hp : R.period=S.period) (hr : R.SquareStart i) (hs : S.SquareStart i) : R=S := by
  have hS' : Run f n S.lo S.hi R.period := by rwa [hp]
  have hO : max R.lo S.lo+R.period≤min R.hi S.hi := by
    have h1 := hr.1
    have h2 := hr.2
    have h3 := hs.1
    have h4 := hs.2
    omega
  obtain ⟨hl,hh⟩ := unique_overlap f n R.lo R.hi S.lo S.hi R.period hR hS' hO
  cases R
  cases S
  simp_all

end REWB.RunGeometry
