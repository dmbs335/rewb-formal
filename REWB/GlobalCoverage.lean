import REWB.GridCoverage
import REWB.PeriodicBudgets

/-! Global geometry for the outer equality of a nested witness.

The maximal equality strip is built by the existing reference scans.
Its overlap case produces an actual least-period maximal run, without
requiring the caller to provide a minimum period. Long gaps have a grid
cut into a separated equality strip. Low-exponent runs and large-period
cubic runs have concrete candidate schedules with aggregate cardinality
bounds. These are geometry and schedule bounds; fast run construction
and the boundary-query implementation remain separate obligations. -/
namespace REWB.GlobalCoverage
open REWB.Periodic REWB.RunGeometry
variable {α : Type}

/-- A positive nonoverlapping pair of equal outer copies. -/
structure Copy (f : Nat→α) (n p e k : Nat) : Prop where
  positive : p<e
  separated : e≤k
  within : k+(e-p)≤n
  equal : segment f p (e-p)=segment f k (e-p)

/-- The equality strip [lo,hi), compared with its shift by d. -/
def MaximalStrip (f : Nat→α) (n lo hi d : Nat) : Prop :=
  0<d ∧ lo<hi ∧ hi+d≤n ∧
    (∀ j,lo≤j→j<hi→f j=f (j+d)) ∧
    (lo=0 ∨ f (lo-1)≠f (lo-1+d)) ∧
    (hi+d=n ∨ f hi≠f (hi+d))

theorem copy_region (f : Nat→α) (n p e k : Nat) (h : Copy f n p e k) :
    GridCoverage.EqualityRegion f n p (e-p) (k-p) := by
  have hp := h.positive
  have hk := h.separated
  have hn := h.within
  refine ⟨by omega,by omega,?_⟩
  intro j hj hje
  have he := (segment_eq_points f p k (e-p)).mp h.equal (j-p) (by omega)
  rw [show p+(j-p)=j by omega,show k+(j-p)=j+(k-p) by omega] at he
  exact he

def expand [DecidableEq α] (f : Nat→α) (n p k : Nat) : Nat × Nat :=
  (GridCoverage.regionLeft f (k-p) p,GridCoverage.regionEnd f n (k-p) p)

/-- Exact maximal expansion of every positive outer-copy pair. -/
theorem expand_spec [DecidableEq α] (f : Nat→α) (n p e k : Nat) (h : Copy f n p e k) :
    let z := expand f n p k
    z.1≤p ∧ e≤z.2 ∧ MaximalStrip f n z.1 z.2 (k-p) := by
  let d := k-p
  let l := GridCoverage.regionLeft f d p
  let r := GridCoverage.regionEnd f n d p
  have hp := h.positive
  have hk := h.separated
  have hn := h.within
  have hreg := copy_region f n p e k h
  have hcov := GridCoverage.extend_covers f n p (e-p) d p hreg
    (Nat.le_refl _) (by omega)
  change l≤p ∧ p+(e-p)≤r at hcov
  have hl := RunExtension.left_spec f d p
  have hr := RunExtension.right_spec f d (n-d-p) p
  change l≤p ∧ (∀ j,l≤j→j<p→f j=f (j+d)) ∧
    (l=0 ∨ f (l-1)≠f (l-1+d)) at hl
  change p≤r ∧ r≤p+(n-d-p) ∧
    (∀ j,p≤j→j<r→f j=f (j+d)) ∧
    (r=p+(n-d-p) ∨ f r≠f (r+d)) at hr
  have hd : 0<d := by dsimp [d]; omega
  have hpn : p+d≤n := by dsimp [d]; omega
  change l≤p ∧ e≤r ∧ MaximalStrip f n l r d
  refine ⟨hl.1,by omega,hd,by omega,by omega,?_,hl.2.2,?_⟩
  · intro j hj hjr
    by_cases hjp : j<p
    · exact hl.2.1 j hj hjp
    · exact hr.2.2.1 j (by omega) hjr
  · rcases hr.2.2.2 with hend|hbad
    · exact Or.inl (by omega)
    · exact Or.inr hbad

/-- Every positive available period has a least positive period below it.
This is an existence proof, not a claimed constant-time period finder. -/
theorem least_of_period (f : Nat→α) (N d : Nat)
    (hd : 0<d) (hP : Period f N d) :
    ∃ q,q≤d ∧ LeastPeriod f N q := by
  classical
  induction d using Nat.strongRecOn with
  | ind d ih =>
    by_cases hm : ∀ q,0<q→Period f N q→d≤q
    · exact ⟨d,Nat.le_refl _,hd,hP,hm⟩
    · have he : ∃ q,0<q ∧ Period f N q ∧ q<d := by
        apply Classical.byContradiction
        intro hnone
        apply hm
        intro q hq hQ
        by_cases hqd : q<d
        · exact False.elim (hnone ⟨q,hq,hQ,hqd⟩)
        · omega
      obtain ⟨q,hq,hQ,hqd⟩ := he
      obtain ⟨r,hr,hR⟩ := ih q hqd hq hQ
      exact ⟨r,Nat.le_trans hr (Nat.le_of_lt hqd),hR⟩

/-- If maximal equal strips overlap, their union is a maximal run of
its actual least period, and the displacement is a multiple of it. -/
theorem overlapping_run (f : Nat→α) (n l r d : Nat)
    (h : MaximalStrip f n l r d) (hoverlap : d≤r-l) :
    ∃ R : Bounds,R.Valid f n ∧ R.lo=l ∧ R.hi=r+d ∧
      R.period∣d ∧ R.period≤d := by
  obtain ⟨hd,hlr,hn,he,hl,hr⟩ := h
  have hcopy : ∀ i,i<r-l→shift f l i=shift f l (i+d) := by
    intro i hi
    have hh := he (l+i) (by omega) (by omega)
    simpa only [shift,Nat.add_assoc] using hh
  have hP := overlap_period (shift f l) (r-l) d hcopy
  obtain ⟨q,hqd,hmin⟩ := least_of_period (shift f l) (r-l+d) d hd hP
  have hex := maximal_equality_run f n l (r-l) d q hd hoverlap (by omega)
    (fun i hi=>by simpa only [shift,Nat.add_assoc] using hcopy i hi)
    hl (by simpa only [show l+(r-l)=r by omega] using hr) hmin
  refine ⟨⟨l,r+d,q⟩,?_,rfl,rfl,hex.1,hqd⟩
  change Run f n l (r+d) q
  simpa only [show l+(r-l)=r by omega] using hex.2

/-- A long outer copy has an actual grid seed in its maximal strip. -/
theorem long_copy_seed (f : Nat→α) (n s p e k : Nat)
    (h : Copy f n p e k) (hs : 0<s) (hL : s≤e-p) :
    ∃ i,(i,i+(k-p))∈GridCoverage.probes n s ∧
      p≤i ∧ i<e ∧ f i=f (i+(k-p)) := by
  obtain ⟨i,hi,hp,he,heq⟩ := GridCoverage.equality_grid f n s p (e-p) (k-p)
    hs hL (copy_region f n p e k h)
  exact ⟨i,hi,hp,by have hh := h.positive; omega,heq⟩

/-- Cutting through the gap gives a separated strip containing both
copy boundaries. This statement includes all natural subtraction edges. -/
theorem cut_separates (l r p e d c : Nat)
    (hlp : l≤p) (_hpe : p<e) (her : e≤r)
    (hec : e≤c) (hck : c≤p+d) :
    max l (c-d)≤p ∧ e≤min r c ∧ min r c≤max l (c-d)+d := by
  omega

theorem long_gap_cut (D l r p e d : Nat)
    (hD : 0<D) (hlp : l≤p) (hpe : p<e) (her : e≤r)
    (hgap : e+D≤p+d) :
    ∃ a,e≤a*D ∧ a*D≤p+d ∧
      max l (a*D-d)≤p ∧ e≤min r (a*D) ∧
      min r (a*D)≤max l (a*D-d)+d := by
  obtain ⟨a,ha,hb⟩ := GridCoverage.grid_hit D e (p+d-e) hD (by omega)
  have hk : a*D≤p+d := by omega
  exact ⟨a,ha,hk,cut_separates l r p e d (a*D) hlp hpe her ha hk⟩

/-- Concrete candidate starts for a low-exponent, short-gap run.
One harmless extra boundary makes the size exactly mass(R)+D. -/
def lowStarts (R : Bounds) (D : Nat) : List Nat :=
  (List.range (RunBudget.mass R+D)).map (fun i=>R.lo+i)

theorem lowStarts_length (R : Bounds) (D : Nat) :
    (lowStarts R D).length=RunBudget.mass R+D := by
  simp only [lowStarts,List.length_map,List.length_range]

/-- The overlap displacement of a low-exponent strip is its minimum
period. A gap shorter than D forces the source start into lowStarts. -/
theorem low_start_coverage (f : Nat→α) (n D p e d : Nat) (R : Bounds)
    (hR : R.Valid f n) (hd : 0<d) (hdiv : R.period∣d)
    (hoverlap : 2*d≤R.hi-R.lo) (hlow : R.hi-R.lo<3*R.period)
    (hlp : R.lo≤p) (hpe : p<e) (heq : e≤p+d)
    (hend : e+d≤R.hi) (hgap : p+d-e<D) :
    d=R.period ∧ p∈lowStarts R D := by
  have hp := hR.2.2.2.1.1
  have hlo := hR.1
  have he : d=R.period := RunBudget.low_exponent_shift R.period d
    (R.hi-R.lo-d) hp hd hdiv (by omega) (by omega)
  refine ⟨he,?_⟩
  apply List.mem_map.mpr
  refine ⟨p-R.lo,List.mem_range.mpr ?_,by omega⟩
  unfold RunBudget.mass
  omega

/-- Enumerate every run-local start boundary and every positive period
multiple at most the run length. Invalid endpoint combinations may be
discarded by the query; they are included in the measured list size. -/
def largePairs (R : Bounds) : List (Nat × Nat) :=
  (List.range ((R.hi-R.lo)/R.period)).flatMap fun j=>
    (List.range (R.hi-R.lo+1)).map fun i=>(R.lo+i,(j+1)*R.period)

theorem largePairs_length (R : Bounds) :
    (largePairs R).length=((R.hi-R.lo)/R.period)*(R.hi-R.lo+1) := by
  have aux : ∀ xs : List Nat,
      (xs.flatMap (fun j=>(List.range (R.hi-R.lo+1)).map
        (fun i=>(R.lo+i,(j+1)*R.period)))).length=
          xs.length*(R.hi-R.lo+1) := by
    intro xs
    induction xs with
    | nil => simp
    | cons j js ih =>
      rw [List.flatMap_cons,List.length_append,List.length_map,
        List.length_range,ih,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
  exact (aux _).trans (by rw [List.length_range])

theorem largePairs_coverage (R : Bounds) (p d : Nat)
    (hq : 0<R.period) (hlp : R.lo≤p) (hpr : p≤R.hi)
    (hd : 0<d) (hdn : d≤R.hi-R.lo) (hdiv : R.period∣d) :
    (p,d)∈largePairs R := by
  obtain ⟨m,hm⟩ := hdiv
  have hmpos : 0<m := by
    by_cases hz : m=0
    · simp only [hz,Nat.mul_zero] at hm
      omega
    · omega
  have hmle : m≤(R.hi-R.lo)/R.period := by
    apply (Nat.le_div_iff_mul_le hq).mpr
    rw [Nat.mul_comm,← hm]
    exact hdn
  unfold largePairs
  apply List.mem_flatMap.mpr
  refine ⟨m-1,List.mem_range.mpr (by omega),?_⟩
  apply List.mem_map.mpr
  refine ⟨p-R.lo,List.mem_range.mpr (by omega),?_⟩
  apply Prod.ext
  · omega
  · change (m-1+1)*R.period=d
    rw [show m-1+1=m by omega,Nat.mul_comm,← hm]

theorem largePairs_bound (n Q : Nat) (R : Bounds)
    (hn : R.hi≤n) (hQ : Q≤R.period) :
    Q*(largePairs R).length≤n*(R.hi-R.lo+1) := by
  have hd : Q*((R.hi-R.lo)/R.period)≤n := by
    have h1 := Nat.mul_le_mul_right ((R.hi-R.lo)/R.period) hQ
    have h2 := Nat.div_mul_le_self (R.hi-R.lo) R.period
    rw [Nat.mul_comm] at h2
    have h3 : R.hi-R.lo≤n := by omega
    exact Nat.le_trans (Nat.le_trans h1 h2) h3
  rw [largePairs_length,← Nat.mul_assoc]
  exact Nat.mul_le_mul_right _ hd

def lowSchedule (D : Nat) : List Bounds→List (Bounds × Nat)
  | [] => []
  | R::Rs => (lowStarts R D).map (fun p=>(R,p))++lowSchedule D Rs

def largeSchedule : List Bounds→List (Bounds × (Nat × Nat))
  | [] => []
  | R::Rs => (largePairs R).map (fun p=>(R,p))++largeSchedule Rs

theorem lowSchedule_mem (D : Nat) (Rs : List Bounds) (R : Bounds) (p : Nat) :
    (R,p)∈lowSchedule D Rs ↔ R∈Rs ∧ p∈lowStarts R D := by
  induction Rs with
  | nil => simp [lowSchedule]
  | cons S Ss ih =>
    simp only [lowSchedule,List.mem_append,List.mem_map,ih,List.mem_cons]
    constructor
    · rintro (⟨v,hv,he⟩|⟨hS,hp⟩)
      · have hSR : S=R := congrArg Prod.fst he
        have hvp : v=p := congrArg Prod.snd he
        subst S
        subst v
        exact ⟨Or.inl rfl,hv⟩
      · exact ⟨Or.inr hS,hp⟩
    · rintro ⟨hR,hp⟩
      rcases hR with he|hm
      · subst S
        exact Or.inl ⟨p,hp,rfl⟩
      · exact Or.inr ⟨hm,hp⟩

theorem largeSchedule_mem (Rs : List Bounds) (R : Bounds) (p d : Nat) :
    (R,(p,d))∈largeSchedule Rs ↔ R∈Rs ∧ (p,d)∈largePairs R := by
  induction Rs with
  | nil => simp [largeSchedule]
  | cons S Ss ih =>
    simp only [largeSchedule,List.mem_append,List.mem_map,ih,List.mem_cons]
    constructor
    · rintro (⟨v,hv,he⟩|⟨hS,hp⟩)
      · have hSR : S=R := congrArg Prod.fst he
        have hvp : v=(p,d) := congrArg Prod.snd he
        subst S
        subst v
        exact ⟨Or.inl rfl,hv⟩
      · exact ⟨Or.inr hS,hp⟩
    · rintro ⟨hR,hp⟩
      rcases hR with he|hm
      · subst S
        exact Or.inl ⟨(p,d),hp,rfl⟩
      · exact Or.inr ⟨hm,hp⟩

theorem lowSchedule_mass (D : Nat) (Rs : List Bounds) :
    (lowSchedule D Rs).length≤(D+1)*RunBudget.totalMass Rs := by
  induction Rs with
  | nil => simp [lowSchedule,RunBudget.totalMass]
  | cons R Rs ih =>
    have hm : 1≤RunBudget.mass R := by unfold RunBudget.mass; omega
    have hD := Nat.mul_le_mul_left D hm
    rw [Nat.mul_one] at hD
    have hlocal : RunBudget.mass R+D≤(D+1)*RunBudget.mass R := by
      rw [Nat.add_mul,Nat.one_mul]
      omega
    rw [lowSchedule,List.length_append,List.length_map,lowStarts_length]
    change _≤(D+1)*(RunBudget.mass R+RunBudget.totalMass Rs)
    rw [Nat.mul_add]
    exact Nat.add_le_add hlocal ih

theorem lowSchedule_bound (f : Nat→α) (n D : Nat) (Rs : List Bounds)
    (hR : ∀ R,R∈Rs→R.Valid f n) (hd : Rs.Nodup) :
    (lowSchedule D Rs).length≤(D+1)*(2*n*DyadicIndex.heightFor n) :=
  Nat.le_trans (lowSchedule_mass D Rs)
    (Nat.mul_le_mul_left _ (RunBudget.totalMass_bound f n Rs hd hR))

theorem cubic_length_mass (R : Bounds) (hc : 3*R.period≤R.hi-R.lo) :
    R.hi-R.lo+1≤3*RunBudget.mass R := by
  unfold RunBudget.mass
  omega

theorem largeSchedule_mass (n Q : Nat) (Rs : List Bounds)
    (h : ∀ R,R∈Rs→R.hi≤n ∧ Q≤R.period ∧ 3*R.period≤R.hi-R.lo) :
    Q*(largeSchedule Rs).length≤3*n*RunBudget.totalMass Rs := by
  induction Rs with
  | nil => simp [largeSchedule,RunBudget.totalMass]
  | cons R Rs ih =>
    obtain ⟨hn,hQ,hc⟩ := h R (by simp)
    have hlocal := Nat.le_trans (largePairs_bound n Q R hn hQ)
      (Nat.mul_le_mul_left n (cubic_length_mass R hc))
    have hlocal' : Q*(largePairs R).length≤3*n*RunBudget.mass R := by
      have he : n*(3*RunBudget.mass R)=3*n*RunBudget.mass R := by ac_rfl
      rwa [he] at hlocal
    have hrest := ih (fun R hR=>h R (by simp [hR]))
    rw [largeSchedule,List.length_append,List.length_map,Nat.mul_add]
    change _≤3*n*(RunBudget.mass R+RunBudget.totalMass Rs)
    rw [Nat.mul_add]
    exact Nat.add_le_add hlocal' hrest

/-- Actual generated pair-list size for any duplicate-free cubic run
family with periods greater than Q. This is O(n² log n/(Q+1)). -/
theorem largeSchedule_bound (f : Nat→α) (n Q : Nat) (Rs : List Bounds)
    (hR : ∀ R,R∈Rs→R.Valid f n) (hd : Rs.Nodup)
    (h : ∀ R,R∈Rs→Q<R.period ∧ 3*R.period≤R.hi-R.lo) :
    (largeSchedule Rs).length≤
      (3*n*(2*n*DyadicIndex.heightFor n))/(Q+1) := by
  apply (Nat.le_div_iff_mul_le (by omega : 0<Q+1)).mpr
  rw [Nat.mul_comm]
  exact Nat.le_trans (largeSchedule_mass n (Q+1) Rs (fun R hm=>
    ⟨(hR R hm).2.1,by have hh := (h R hm).1; omega,(h R hm).2⟩))
      (Nat.mul_le_mul_left _ (RunBudget.totalMass_bound f n Rs hd hR))

/-- The exhaustive geometric cases of a positive outer-copy pair.
The low and large constructors carry membership in actual schedules.
The small-period constructor carries precisely the outer containment
and length conditions needed by the existing periodic solvers. -/
inductive GeometryCase (f : Nat→α) (n L D Q p e k : Nat) : Prop
  | short (h : e-p<L) : GeometryCase f n L D Q p e k
  | separated (l r : Nat) (h : MaximalStrip f n l r (k-p))
      (left : l≤p) (right : e≤r) (disjoint : r-l≤k-p) :
      GeometryCase f n L D Q p e k
  | longGap (l r a : Nat) (h : MaximalStrip f n l r (k-p))
      (left : l≤p) (right : e≤r)
      (cutLeft : e≤a*D) (cutRight : a*D≤k)
      (containsLeft : max l (a*D-(k-p))≤p)
      (containsRight : e≤min r (a*D))
      (separates : min r (a*D)≤max l (a*D-(k-p))+(k-p)) :
      GeometryCase f n L D Q p e k
  | low (R : Bounds) (valid : R.Valid f n)
      (left : R.lo≤p) (right : e+(k-p)≤R.hi)
      (displacement : R.period=k-p) (exponent : R.hi-R.lo<3*R.period)
      (scheduled : p∈lowStarts R D) : GeometryCase f n L D Q p e k
  | large (R : Bounds) (valid : R.Valid f n)
      (left : R.lo≤p) (right : e+(k-p)≤R.hi)
      (cubic : 3*R.period≤R.hi-R.lo) (largePeriod : Q<R.period)
      (scheduled : (p,k-p)∈largePairs R) : GeometryCase f n L D Q p e k
  | smallPeriod (R : Bounds) (valid : R.Valid f n)
      (left : R.lo≤p) (right : e+(k-p)≤R.hi)
      (cubic : 3*R.period≤R.hi-R.lo) (small : R.period≤Q)
      (longOuter : R.period≤e-p) : GeometryCase f n L D Q p e k

/-- Every positive copy pair enters one of the explicit geometric
branches. The Q≤L ordering removes short-outer exceptions from the
small-period cubic branch. No matching-query oracle is assumed here. -/
theorem cover [DecidableEq α] (f : Nat→α) (n L D Q p e k : Nat)
    (h : Copy f n p e k) (hD : 0<D) (hQL : Q≤L) :
    GeometryCase f n L D Q p e k := by
  by_cases hshort : e-p<L
  · exact .short hshort
  let l := (expand f n p k).1
  let r := (expand f n p k).2
  let d := k-p
  have hz := expand_spec f n p e k h
  change l≤p ∧ e≤r ∧ MaximalStrip f n l r d at hz
  obtain ⟨hlp,her,hstrip⟩ := hz
  have hp := h.positive
  have hk := h.separated
  have hd : 0<d := by dsimp [d]; omega
  have hpk : p+d=k := by dsimp [d]; omega
  by_cases hsep : r-l≤d
  · exact .separated l r hstrip hlp her hsep
  obtain ⟨R,hR,hRl,hRr,hdiv,hqd⟩ := overlapping_run f n l r d hstrip (by omega)
  have hrleft : R.lo≤p := by rw [hRl]; exact hlp
  have hrright : e+d≤R.hi := by rw [hRr]; omega
  by_cases hgap : D≤p+d-e
  · obtain ⟨a,ha,hb,h1,h2,h3⟩ := long_gap_cut D l r p e d hD hlp hp her (by omega)
    exact .longGap l r a hstrip hlp her ha (by rwa [hpk] at hb) h1 h2 h3
  by_cases hlow : R.hi-R.lo<3*R.period
  · have hov : 2*d≤R.hi-R.lo := by rw [hRl,hRr]; omega
    obtain ⟨he,hs⟩ := low_start_coverage f n D p e d R hR hd hdiv hov hlow
      hrleft hp (by omega) hrright (by omega)
    exact .low R hR hrleft hrright he.symm hlow hs
  by_cases hlarge : Q<R.period
  · have hpn : p≤R.hi := by omega
    have hdn : d≤R.hi-R.lo := by rw [hRl,hRr]; omega
    exact .large R hR hrleft hrright (by omega) hlarge
      (largePairs_coverage R p d hR.2.2.2.1.1 hrleft hpn hd hdn hdiv)
  · exact .smallPeriod R hR hrleft hrright (by omega) (by omega) (by omega)

end REWB.GlobalCoverage
