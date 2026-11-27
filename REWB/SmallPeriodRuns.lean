import REWB.GridCoverage
import REWB.PeriodicBudgets

/-! Enumerate all runs whose least period is at most a supplied bound.
    Each period uses one backward equality scan and direct-addressed
    endpoints. Minimality is checked on the first square only. The
    comparison counters belong to the executable traversals; they do not
    count all RAM operations or assume a suffix/LCE oracle. -/
namespace REWB.SmallPeriodRuns
open REWB.Periodic REWB.RunGeometry REWB.RunExtension
variable {α : Type} [DecidableEq α]

/-- Right endpoints of all equal-shift intervals, including the terminal
    endpoint. The table uses one character comparison per position. -/
def ends (f : Nat→α) (p : Nat) : Nat→Nat→List Nat × Nat
  | a,0 => ([a],0)
  | a,k+1 =>
    let r := ends f p (a+1) k
    ((if f a=f (a+p) then r.1.headD (a+1) else a)::r.1,r.2+1)

theorem ends_cost (f : Nat→α) (p a k : Nat) : (ends f p a k).2=k := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    change (ends f p (a+1) k).2+1=k+1
    rw [ih]

theorem ends_head (f : Nat→α) (p a k fallback : Nat) :
    (ends f p a k).1.headD fallback=right f p k a := by
  induction k generalizing a fallback with
  | zero => rfl
  | succ k ih =>
    change (if f a=f (a+p) then (ends f p (a+1) k).1.headD (a+1) else a)=_
    rw [ih]
    rfl

theorem ends_get (f : Nat→α) (p a k j : Nat) (hj : j≤k) :
    (ends f p a k).1[j]?=some (right f p (k-j) (a+j)) := by
  induction k generalizing a j with
  | zero =>
    have he : j=0 := by omega
    subst j
    rfl
  | succ k ih =>
    cases j with
    | zero =>
      change some (if f a=f (a+p) then (ends f p (a+1) k).1.headD (a+1) else a)=_
      rw [ends_head]
      rfl
    | succ j =>
      change (ends f p (a+1) k).1[j]?=_
      rw [ih (a+1) j (by omega)]
      congr 2 <;> omega

def endAt (T : Array Nat) (i : Nat) : Nat := T[i]?.getD i

theorem endAt_correct (f : Nat→α) (n p i : Nat) (hi : i≤n-p) :
    endAt (ends f p 0 (n-p)).1.toArray i=right f p (n-p-i) i := by
  unfold endAt
  rw [List.getElem?_toArray,ends_get f p 0 (n-p) i hi]
  simp

/-- Count the work of every test, without hiding it in a supplied cost. -/
def allCounted (test : Nat→Bool×Nat) : List Nat→Bool×Nat
  | [] => (true,0)
  | x::xs =>
    let a := test x
    let b := allCounted test xs
    (a.1 && b.1,a.2+b.2)

theorem allCounted_value (test : Nat→Bool×Nat) (xs : List Nat) :
    (allCounted test xs).1=xs.all (fun x=>(test x).1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change ((test x).1 && (allCounted test xs).1)=_
    rw [ih]
    rfl

theorem allCounted_cost_le (test : Nat→Bool×Nat) (xs : List Nat) (c : Nat)
    (h : ∀ x,x∈xs→(test x).2≤c) :
    (allCounted test xs).2≤xs.length*c := by
  induction xs with
  | nil => simp [allCounted]
  | cons x xs ih =>
    change (test x).2+(allCounted test xs).2≤(xs.length+1)*c
    rw [Nat.add_mul,Nat.one_mul]
    have hrest := ih (fun y hy=>h y (by simp [hy]))
    have hx := h x (by simp)
    omega

def period (f : Nat→α) (i L p : Nat) : Bool×Nat :=
  allCounted (fun j=>(decide (f (i+j)=f (i+j+p)),1)) (List.range (L-p))

theorem period_value (f : Nat→α) (i L p : Nat) :
    (period f i L p).1=periodTest f i L p :=
  allCounted_value _ _

theorem period_cost (f : Nat→α) (i L p : Nat) :
    (period f i L p).2≤L := by
  have h := allCounted_cost_le
    (fun j=>(decide (f (i+j)=f (i+j+p)),1)) (List.range (L-p)) 1 (by simp)
  simpa [period,List.length_range,Nat.mul_one] using Nat.le_trans h (by simp)

def square (f : Nat→α) (n i p : Nat) : Bool×Nat :=
  let a := period f i (2*p) p
  let b := allCounted (fun q=>
    if q=0 then (true,0) else
      let t := period f i (2*p) q
      (!t.1,t.2)) (List.range p)
  (decide (0<p ∧ i+2*p≤n) && a.1 && b.1,a.2+b.2)

theorem square_value (f : Nat→α) (n i p : Nat) :
    (square f n i p).1=squareTest f n i p := by
  dsimp only [square]
  unfold squareTest
  rw [period_value,allCounted_value]
  congr 2
  funext q
  by_cases h : q=0
  · simp [h]
  · simp [h,period_value]

theorem square_cost (f : Nat→α) (n i p : Nat) :
    (square f n i p).2≤2*p*(p+1) := by
  have ha := period_cost f i (2*p) p
  have hb := allCounted_cost_le (fun q=>
    if q=0 then (true,0) else
      let t := period f i (2*p) q
      (!t.1,t.2)) (List.range p) (2*p) (by
        intro q _
        dsimp only
        split
        · exact Nat.zero_le _
        · exact period_cost f i (2*p) q)
  rw [List.length_range] at hb
  change (period f i (2*p) p).2+_≤_
  have hh := Nat.add_le_add ha hb
  calc
    _ ≤ 2*p+p*(2*p) := hh
    _ = 2*p*(p+1) := by rw [Nat.mul_succ,Nat.mul_comm p (2*p),Nat.add_comm]

def isLeft (f : Nat→α) (p i : Nat) : Bool :=
  decide (i=0 ∨ f (i-1)≠f (i-1+p))

theorem valid_left (f : Nat→α) (n : Nat) (R : Bounds) (h : R.Valid f n) :
    isLeft f R.period R.lo=true := by
  apply decide_eq_true
  by_cases hz : R.lo=0
  · exact Or.inl hz
  · refine Or.inr ?_
    intro he
    have hh := on_extend_left f R.lo R.hi R.period (run_on f n _ _ _ h) (by omega) he
    have hp := (on_iff f (R.lo-1) R.hi R.period).mp hh
    rw [show R.hi-(R.lo-1)=R.hi-R.lo+1 by have hl := h.1; omega] at hp
    rcases h.2.2.2.2.1 with hzero|hbad
    · exact hz hzero
    · exact hbad hp

def candidate (f : Nat→α) (n p : Nat) (T : Array Nat) (i : Nat) : Option Bounds × Nat :=
  if isLeft f p i then
    let s := square f n i p
    (if s.1 then some ⟨i,endAt T i+p,p⟩ else none,s.2+1)
  else (none,1)

theorem candidate_iff (f : Nat→α) (n p i : Nat) (R : Bounds) :
    (candidate f n p (ends f p 0 (n-p)).1.toArray i).1=some R ↔
      R.Valid f n ∧ R.period=p ∧ R.lo=i := by
  unfold candidate
  constructor
  · intro hc
    split at hc
    next hl =>
      dsimp only at hc
      split at hc
      next hs =>
        have hs' := (squareTest_correct f n i p).mp (by rwa [← square_value])
        have hn := hs'.1
        have hp := hs'.2.1
        have hr := right_spec f p (n-p-i) i
        have hTab := endAt_correct f n p i (by omega)
        have he : (⟨i,endAt (ends f p 0 (n-p)).1.toArray i+p,p⟩ : Bounds)=R :=
          Option.some.inj hc
        rw [← he,hTab]
        refine ⟨?_,rfl,rfl⟩
        let b := right f p (n-p-i) i
        have hsq : i+p≤b := by
          by_cases h : i+p≤b
          · exact h
          · rcases hr.2.2.2 with hlim|hbad
            · change b=i+(n-p-i) at hlim
              omega
            · have hsmall : b-i+p<2*p := by have hlo := hr.1; omega
              have heq := hs'.2.2.1 (b-i) hsmall
              unfold shift at heq
              rw [show i+(b-i)=b by have hlo := hr.1; omega,
                show i+(b-i+p)=b+p by have hlo := hr.1; omega] at heq
              exact False.elim (hbad heq)
        have hOn : OnPeriod f i (b+p) p := by
          intro j hj hjb
          exact hr.2.2.1 j hj (by omega)
        change Run f n i (b+p) p
        refine ⟨by omega,by have hb := hr.2.1; omega,by omega,
          ⟨hp,(on_iff f i (b+p) p).mp hOn,?_⟩,?_,?_⟩
        · intro q hq hQ
          have hres := on_restrict f i (b+p) q i (i+2*p)
            ((on_iff f i (b+p) q).mpr hQ) (Nat.le_refl _) (by omega)
          have hshort := (on_iff f i (i+2*p) q).mp hres
          rw [show i+2*p-i=2*p by omega] at hshort
          exact hs'.2.2.2 q hq hshort
        · rcases of_decide_eq_true hl with hz|hbad
          · exact Or.inl hz
          · refine Or.inr ?_
            intro hext
            have hh := hext 0 (by omega)
            apply hbad
            simpa only [shift,Nat.add_zero,Nat.zero_add] using hh
        · rcases hr.2.2.2 with hlim|hbad
          · exact Or.inl (by change b=i+(n-p-i) at hlim; omega)
          · refine Or.inr ?_
            intro hext
            have hh := hext (b-i) (by omega)
            unfold shift at hh
            rw [show i+(b-i)=b by have hb := hr.1; omega,
              show i+(b-i+p)=b+p by have hb := hr.1; omega] at hh
            exact hbad hh
      next hs => simp at hc
    next hl => simp at hc
  · rintro ⟨hv,hp,hi⟩
    have hleft := valid_left f n R hv
    rw [hp,hi] at hleft
    rw [if_pos hleft]
    dsimp only
    have hSq := square_start_sound f n R hv R.lo
      ⟨Nat.le_refl _,by have hlen := hv.2.2.1; have hlo := hv.1; omega⟩
    rw [hp,hi] at hSq
    have hTest : (square f n i p).1=true := by
      rw [square_value]
      exact (squareTest_correct f n i p).mpr hSq
    rw [if_pos hTest]
    have hn := hSq.1
    rw [endAt_correct f n p i (by omega)]
    have hEnd := (GridCoverage.extend_run_exact f n R hv R.lo (Nat.le_refl _)
      (by have hh := hv.2.2.1; have hp' := hv.2.2.2.1.1; have hl := hv.1; omega)).2
    change right f R.period (n-R.period-R.lo) R.lo+R.period=R.hi at hEnd
    rw [hp,hi] at hEnd
    cases R
    simp_all

def collect (f : Nat→α) (n p : Nat) (T : Array Nat) : List Nat→List Bounds×Nat
  | [] => ([],0)
  | i::is =>
    let a := candidate f n p T i
    let b := collect f n p T is
    (match a.1 with | none=>b.1 | some R=>R::b.1,a.2+b.2)

theorem collect_values (f : Nat→α) (n p : Nat) (T : Array Nat) (xs : List Nat) :
    (collect f n p T xs).1=xs.filterMap (fun i=>(candidate f n p T i).1) := by
  induction xs with
  | nil => rfl
  | cons i is ih =>
    change (match (candidate f n p T i).1 with | none=>_ | some R=>R::_)=_
    rw [ih]
    rw [List.filterMap_cons]
    cases (candidate f n p T i).1 <;> rfl

def forPeriod (f : Nat→α) (n p : Nat) : List Bounds×Nat :=
  let t := ends f p 0 (n-p)
  let r := collect f n p t.1.toArray (List.range (n+1))
  (r.1,t.2+r.2)

theorem forPeriod_mem (f : Nat→α) (n p : Nat) (R : Bounds) :
    R∈(forPeriod f n p).1 ↔ R.Valid f n ∧ R.period=p := by
  change R∈(collect f n p (ends f p 0 (n-p)).1.toArray (List.range (n+1))).1↔_
  rw [collect_values,List.mem_filterMap]
  constructor
  · rintro ⟨i,_,hc⟩
    exact ((candidate_iff f n p i R).mp hc).imp_right And.left
  · rintro ⟨hv,hp⟩
    refine ⟨R.lo,List.mem_range.mpr (by have hlo := hv.1; have hn := hv.2.1; omega),?_⟩
    exact (candidate_iff f n p R.lo R).mpr ⟨hv,hp,rfl⟩

theorem candidate_cost (f : Nat→α) (n p : Nat) (T : Array Nat) (i : Nat) :
    (candidate f n p T i).2≤2*p*(p+1)+1 := by
  unfold candidate
  split
  · exact Nat.add_le_add_right (square_cost f n i p) 1
  · exact Nat.le_add_left 1 _

theorem collect_cost (f : Nat→α) (n p : Nat) (T : Array Nat) (xs : List Nat) :
    (collect f n p T xs).2≤xs.length*(2*p*(p+1)+1) := by
  induction xs with
  | nil => simp [collect]
  | cons i is ih =>
    change (candidate f n p T i).2+(collect f n p T is).2≤
      (is.length+1)*(2*p*(p+1)+1)
    have h := candidate_cost f n p T i
    rw [Nat.add_mul,Nat.one_mul]
    omega

theorem forPeriod_cost (f : Nat→α) (n p : Nat) :
    (forPeriod f n p).2≤n+(n+1)*(2*p*(p+1)+1) := by
  have hc := collect_cost f n p (ends f p 0 (n-p)).1.toArray (List.range (n+1))
  rw [List.length_range] at hc
  change (ends f p 0 (n-p)).2+_≤_
  rw [ends_cost]
  omega

private theorem partial_injective_nodup {X Y : Type} (f : X→Option Y) (g : Y→X)
    (xs : List X) (hd : xs.Nodup) (h : ∀ x y,f x=some y→g y=x) :
    (xs.filterMap f).Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    obtain ⟨hx,hxs⟩ := List.nodup_cons.mp hd
    rw [List.filterMap_cons]
    cases he : f x with
    | none => exact ih hxs
    | some y =>
      apply List.nodup_cons.mpr
      refine ⟨?_,ih hxs⟩
      intro hy
      obtain ⟨z,hz,hfz⟩ := List.mem_filterMap.mp hy
      have heq := (h x y he).symm.trans (h z y hfz)
      exact hx (by rwa [heq])

theorem forPeriod_nodup (f : Nat→α) (n p : Nat) :
    (forPeriod f n p).1.Nodup := by
  change (collect f n p (ends f p 0 (n-p)).1.toArray (List.range (n+1))).1.Nodup
  rw [collect_values]
  apply partial_injective_nodup _ Bounds.lo _ List.nodup_range
  intro i R hc
  exact ((candidate_iff f n p i R).mp hc).2.2

/-- Periods are enumerated once, so the output has no duplicate runs.
    The constructor never performs a character scan over a whole run. -/
def enumerate (f : Nat→α) (n : Nat) : Nat→List Bounds×Nat
  | 0 => ([],0)
  | Q+1 =>
    let a := forPeriod f n (Q+1)
    let b := enumerate f n Q
    (a.1++b.1,a.2+b.2)

theorem enumerate_mem (f : Nat→α) (n Q : Nat) (R : Bounds) :
    R∈(enumerate f n Q).1 ↔ R.Valid f n ∧ R.period≤Q := by
  induction Q with
  | zero =>
    constructor
    · intro h; simp [enumerate] at h
    · rintro ⟨h,hp⟩
      have hh := h.2.2.2.1.1
      omega
  | succ Q ih =>
    change R∈(forPeriod f n (Q+1)).1++(enumerate f n Q).1↔_
    rw [List.mem_append,forPeriod_mem,ih]
    constructor
    · rintro (⟨h,hp⟩|⟨h,hp⟩) <;> exact ⟨h,by omega⟩
    · rintro ⟨h,hp⟩
      by_cases he : R.period=Q+1
      · exact Or.inl ⟨h,he⟩
      · exact Or.inr ⟨h,by omega⟩

private theorem disjoint_append_nodup {X : Type} (xs ys : List X)
    (hx : xs.Nodup) (hy : ys.Nodup) (hd : ∀ x,x∈xs→x∉ys) :
    (xs++ys).Nodup := by
  induction xs with
  | nil => exact hy
  | cons x xs ih =>
    obtain ⟨hx,hxs⟩ := List.nodup_cons.mp hx
    rw [List.cons_append,List.nodup_cons]
    refine ⟨?_,ih hxs (fun y hy'=>hd y (by simp [hy']))⟩
    intro hm
    rcases List.mem_append.mp hm with hm|hm
    · exact hx hm
    · exact hd x (by simp) hm

theorem enumerate_nodup (f : Nat→α) (n Q : Nat) :
    (enumerate f n Q).1.Nodup := by
  induction Q with
  | zero => exact List.nodup_nil
  | succ Q ih =>
    apply disjoint_append_nodup _ _ (forPeriod_nodup f n (Q+1)) ih
    intro R ha hb
    have hp := ((forPeriod_mem f n (Q+1) R).mp ha).2
    have hq := ((enumerate_mem f n Q R).mp hb).2
    omega

private theorem period_budget_mono (n p Q : Nat) (hp : p≤Q) :
    n+(n+1)*(2*p*(p+1)+1)≤n+(n+1)*(2*Q*(Q+1)+1) := by
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_left
  apply Nat.add_le_add_right
  exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 hp) (Nat.add_le_add_right hp 1)

/-- At most Q scans and (n+1) first-square tests per scan. The resulting
    bound is O((n+1)(Q+1)^3), and does not depend on run lengths. -/
theorem enumerate_cost (f : Nat→α) (n Q : Nat) :
    (enumerate f n Q).2≤Q*(n+(n+1)*(2*Q*(Q+1)+1)) := by
  induction Q with
  | zero => simp [enumerate]
  | succ Q ih =>
    change (forPeriod f n (Q+1)).2+(enumerate f n Q).2≤_
    have hleft := forPeriod_cost f n (Q+1)
    have hright := Nat.le_trans ih (Nat.mul_le_mul_left Q (period_budget_mono n Q (Q+1) (by omega)))
    rw [Nat.add_mul,Nat.one_mul]
    omega

theorem enumerate_mass (f : Nat→α) (n Q : Nat) :
    RunBudget.totalMass (enumerate f n Q).1≤2*n*DyadicIndex.heightFor n :=
  RunBudget.totalMass_bound f n _ (enumerate_nodup f n Q)
    (fun R h=>((enumerate_mem f n Q R).mp h).1)

def cubic (f : Nat→α) (n Q : Nat) : List Bounds :=
  (enumerate f n Q).1.filter (fun R=>decide (3*R.period≤R.hi-R.lo))

theorem cubic_mem (f : Nat→α) (n Q : Nat) (R : Bounds) :
    R∈cubic f n Q ↔ R.Valid f n ∧ R.period≤Q ∧ 3*R.period≤R.hi-R.lo := by
  simp only [cubic,List.mem_filter,enumerate_mem,decide_eq_true_eq]
  exact and_assoc

private theorem filter_nodup {X : Type} (p : X→Bool) (xs : List X)
    (h : xs.Nodup) : (xs.filter p).Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    obtain ⟨hx,hxs⟩ := List.nodup_cons.mp h
    cases he : p x
    · simpa only [List.filter_cons,he,Bool.false_eq_true,if_false] using ih hxs
    · simp only [List.filter_cons,he,if_true,List.nodup_cons]
      exact ⟨fun hm=>hx (List.mem_filter.mp hm).1,ih hxs⟩

theorem cubic_nodup (f : Nat→α) (n Q : Nat) : (cubic f n Q).Nodup :=
  filter_nodup _ _ (enumerate_nodup f n Q)

/-- The output of the concrete enumerator satisfies the global phase
    budget; an abstract or externally supplied run list is unnecessary. -/
theorem cubic_phase_bound (f : Nat→α) (n Q k : Nat) :
    RunBudget.phaseWork k (cubic f n Q)≤Q^k*(2*n*DyadicIndex.heightFor n) :=
  RunBudget.cubic_phase_bound f n k Q _ (cubic_nodup f n Q)
    (fun R h=>((cubic_mem f n Q R).mp h).1)
    (fun R h=>((cubic_mem f n Q R).mp h).2)

end REWB.SmallPeriodRuns
