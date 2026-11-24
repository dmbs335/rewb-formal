import REWB.RunExtension

/-! Grid anchors cover every equality interval of sufficient length.
    A seed is a pair of equal text positions, with the first on a
    stride-s grid. Only the probe count and the exact maximal extension
    are proved here; using a linear-time suffix/LCE index is a separate
    implementation and cost obligation. -/
namespace REWB.GridCoverage
open REWB.Periodic REWB.RunGeometry
variable {α : Type}

def probes (n s : Nat) : List (Nat × Nat) :=
  (List.range (n/s+1)).flatMap (fun k=>
    (List.range (n+1)).map (fun j=>(k*s,j)))

theorem probes_length (n s : Nat) :
    (probes n s).length=(n/s+1)*(n+1) := by
  have aux : ∀ xs : List Nat,
      (xs.flatMap (fun k=>(List.range (n+1)).map (fun j=>(k*s,j)))).length=
        xs.length*(n+1) := by
    intro xs
    induction xs with
    | nil => simp
    | cons x xs ih =>
      simp only [List.flatMap_cons,List.length_append,List.length_map,List.length_range,
        ih,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
  unfold probes
  rw [aux,List.length_range]

theorem probe_mem (n s k j : Nat) (hk : k≤n/s) (hj : j≤n) :
    (k*s,j)∈probes n s := by
  unfold probes
  exact List.mem_flatMap.mpr ⟨k,List.mem_range.mpr (by omega),
    List.mem_map.mpr ⟨j,List.mem_range.mpr (by omega),rfl⟩⟩

/-- Every integer interval of s consecutive positions contains an
    aligned grid coordinate. -/
theorem grid_hit (s a L : Nat) (hs : 0<s) (hL : s≤L) :
    ∃ k,a≤k*s ∧ k*s<a+L := by
  have hm := Nat.mod_add_div a s
  have hr := Nat.mod_lt a hs
  rw [Nat.mul_comm s (a/s)] at hm
  by_cases he : a%s=0
  · exact ⟨a/s,by omega,by omega⟩
  · refine ⟨a/s+1,?_,?_⟩ <;> rw [Nat.add_mul,Nat.one_mul] <;> omega

def EqualityRegion (f : Nat→α) (n a L p : Nat) : Prop :=
  0<p ∧ a+L+p≤n ∧ ∀ i,a≤i→i<a+L→f i=f (i+p)

theorem equality_grid (f : Nat→α) (n s a L p : Nat)
    (hs : 0<s) (hL : s≤L) (h : EqualityRegion f n a L p) :
    ∃ i, (i,i+p)∈probes n s ∧ a≤i ∧ i<a+L ∧ f i=f (i+p) := by
  obtain ⟨k,hlo,hhi⟩ := grid_hit s a L hs hL
  have hn := h.2.1
  have hk : k≤n/s := (Nat.le_div_iff_mul_le hs).mpr (by omega)
  exact ⟨k*s,probe_mem n s k (k*s+p) hk (by omega),hlo,hhi,h.2.2 _ hlo hhi⟩

variable [DecidableEq α]

def regionLeft (f : Nat→α) (p i : Nat) : Nat := RunExtension.left f p i
def regionEnd (f : Nat→α) (n p i : Nat) : Nat :=
  RunExtension.right f p (n-p-i) i

/-- The maximal equality region at a grid anchor contains the entire
    original equality interval. -/
theorem extend_covers (f : Nat→α) (n a L p i : Nat)
    (h : EqualityRegion f n a L p) (ha : a≤i) (hi : i<a+L) :
    regionLeft f p i≤a ∧ a+L≤regionEnd f n p i := by
  have hl := RunExtension.left_spec f p i
  have hr := RunExtension.right_spec f p (n-p-i) i
  let l := regionLeft f p i
  let r := regionEnd f n p i
  change l≤i ∧ _ at hl
  change i≤r ∧ r≤i+(n-p-i) ∧ _ at hr
  have hn := h.2.1
  change l≤a ∧ a+L≤r
  constructor
  · by_cases ht : l≤a
    · exact ht
    · rcases hl.2.2 with hz|hb
      · change l=0 at hz
        omega
      · have hb' : f (l-1)≠f (l-1+p) := hb
        exact False.elim (hb' (h.2.2 (l-1) (by omega) (by omega)))
  · by_cases ht : a+L≤r
    · exact ht
    · rcases hr.2.2.2 with hz|hb
      · change r=i+(n-p-i) at hz
        omega
      · have hb' : f r≠f (r+p) := hb
        exact False.elim (hb' (h.2.2 r (by omega) (by omega)))

/-- For a maximal run, the grid extension at its true period cannot
    escape either maximal boundary. -/
theorem extend_run_exact (f : Nat→α) (n : Nat) (R : Bounds)
    (h : R.Valid f n) (i : Nat)
    (hlo : R.lo≤i) (hhi : i+R.period<R.hi) :
    regionLeft f R.period i=R.lo ∧
      regionEnd f n R.period i+R.period=R.hi := by
  let p := R.period
  let a := R.lo
  let b := R.hi
  let l := regionLeft f p i
  let r := regionEnd f n p i
  have hp : 0<p := h.2.2.2.1.1
  have hb : b≤n := h.2.1
  have hlen : 2*p≤b-a := h.2.2.1
  have hP := run_on f n a b p h
  have hreg : EqualityRegion f n a (b-a-p) p := by
    refine ⟨hp,by omega,?_⟩
    intro j hj hj'
    exact hP j hj (by omega)
  have hcov := extend_covers f n a (b-a-p) p i hreg hlo (by omega)
  change l≤a ∧ a+(b-a-p)≤r at hcov
  have hleft := RunExtension.left_spec f p i
  have hright := RunExtension.right_spec f p (n-p-i) i
  change l≤i ∧ _ at hleft
  change i≤r ∧ r≤i+(n-p-i) ∧ _ at hright
  have hLeftEq : ∀ j,l≤j→j<i→f j=f (j+p) := hleft.2.1
  have hRightEq : ∀ j,i≤j→j<r→f j=f (j+p) := hright.2.2.1
  have heL : l=a := by
    by_cases ht : l=a
    · exact ht
    · have he : f (a-1)=f (a-1+p) := hLeftEq _ (by omega) (by omega)
      have hext := on_extend_left f a b p hP (by omega) he
      have hper := (on_iff f (a-1) b p).mp hext
      rw [show b-(a-1)=b-a+1 by omega] at hper
      rcases h.2.2.2.2.1 with hz|hz
      · change a=0 at hz
        omega
      · exact False.elim (hz hper)
  have heR : r+p=b := by
    by_cases ht : r+p=b
    · exact ht
    · have he : f (b-p)=f b := by
        have hh := hRightEq (b-p) (by omega) (by omega)
        rw [show b-p+p=b by omega] at hh
        exact hh
      have hext := on_extend_right f a b p hP hp (by omega) he
      have hper := (on_iff f a (b+1) p).mp hext
      rw [show b+1-a=b-a+1 by omega] at hper
      rcases h.2.2.2.2.2 with hz|hz
      · change b=n at hz
        omega
      · exact False.elim (hz hper)
  exact ⟨heL,heR⟩

/-- A grid of stride s covers every run with at least s equality
    positions, including a run whose exponent is exactly two.
    The period can be the true minimum period, not an arbitrary
    displacement. -/
theorem run_grid (f : Nat→α) (n s : Nat) (R : Bounds)
    (hs : 0<s) (h : R.Valid f n)
    (hL : s≤R.hi-R.lo-R.period) :
    ∃ i,(i,i+R.period)∈probes n s ∧
      regionLeft f R.period i=R.lo ∧
      regionEnd f n R.period i+R.period=R.hi := by
  have hP := run_on f n R.lo R.hi R.period h
  have hp := h.2.2.2.1.1
  have hn := h.2.1
  have hlen := h.2.2.1
  have hreg : EqualityRegion f n R.lo (R.hi-R.lo-R.period) R.period := by
    refine ⟨hp,by omega,?_⟩
    intro j hj hj'
    exact hP j hj (by omega)
  obtain ⟨i,hi,ha,hb,_⟩ := equality_grid f n s R.lo (R.hi-R.lo-R.period)
    R.period hs hL hreg
  exact ⟨i,hi,extend_run_exact f n R h i ha (by omega)⟩

end REWB.GridCoverage
