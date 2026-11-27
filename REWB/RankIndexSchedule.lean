import REWB.RankIndexRuns
import REWB.RunDedup

/-! A concrete duplicate-free sampled run list, with generated low-start
and large-period schedules. Only the residual matching queries, rather
than run discovery, remain external to this construction. -/
namespace REWB.RankIndexSchedule
open REWB.RunGeometry REWB.GlobalCoverage
variable {σ : Nat}

structure Result where
  runs : List Bounds
  preparation : Nat
  divisorWork : Nat
  queryWork : Nat
  periodWork : Nat
  probes : Nat
  dedupWork : Nat

def generate (f : Nat→Fin σ) (n s : Nat) : Result :=
  let r:=RankIndexRuns.generate f n s
  let d:=RunDedup.run n r.runs
  ⟨d.runs,r.preparation,r.divisorWork,r.queryWork,r.periodWork,r.probes,d.work⟩

theorem generate_mem (f : Nat→Fin σ) (n s : Nat) (R : Bounds) :
    R∈(generate f n s).runs ↔ R∈(RankIndexRuns.generate f n s).runs :=
  RunDedup.run_mem n _ (fun R hm=>RunDedup.valid_bounded f n R
    (RankIndexRuns.generate_sound f n s R hm)) R

theorem generate_sound (f : Nat→Fin σ) (n s : Nat) (R : Bounds)
    (h : R∈(generate f n s).runs) : R.Valid f n :=
  RankIndexRuns.generate_sound f n s R ((generate_mem f n s R).mp h)

theorem generate_complete (f : Nat→Fin σ) (n s : Nat) (R : Bounds)
    (hR : R.Valid f n) (hs : 0<s) (hspan : s≤R.hi-R.lo-R.period) :
    R∈(generate f n s).runs :=
  (generate_mem f n s R).mpr (RankIndexRuns.generate_complete f n s R hR hs hspan)

theorem generate_nodup (f : Nat→Fin σ) (n s : Nat) : (generate f n s).runs.Nodup :=
  RunDedup.run_nodup _ _

theorem totalMass_bound (f : Nat→Fin σ) (n s : Nat) :
    RunBudget.totalMass (generate f n s).runs≤2*n*DyadicIndex.heightFor n :=
  RunBudget.totalMass_bound f n _ (generate_nodup f n s) (generate_sound f n s)

theorem length_le_mass (Rs : List Bounds) : Rs.length≤RunBudget.totalMass Rs := by
  induction Rs with
  | nil => exact Nat.le_refl _
  | cons R Rs ih =>
    have hp : 1≤RunBudget.mass R := by unfold RunBudget.mass; omega
    change Rs.length+1≤RunBudget.mass R+RunBudget.totalMass Rs
    omega

theorem generate_length (f : Nat→Fin σ) (n s : Nat) :
    (generate f n s).runs.length≤2*n*DyadicIndex.heightFor n :=
  Nat.le_trans (length_le_mass _) (totalMass_bound f n s)

theorem generate_counts (f : Nat→Fin σ) (n s : Nat) :
    (generate f n s).probes=(n/s+1)*(n+1) ∧
    (generate f n s).queryWork≤(n/s+1)*((26*(n.log2+1)+2)*(n+1)) ∧
    (generate f n s).periodWork≤(n/s+1)*((n*(n.log2+1))*(13*(n.log2+1)+6)) ∧
    (generate f n s).preparation≤2*((n+1)*((n.log2+1)*(16*RankIndex.width σ n+4)+1)) ∧
    (generate f n s).divisorWork≤3*(n*(n.log2+1)) ∧
    (generate f n s).dedupWork≤(26*((n+1).log2+1)+5)*((n/s+1)*(n+1)) := by
  have h:=RankIndexRuns.generate_counts f n s
  exact ⟨h.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2,
    Nat.le_trans (RunDedup.run_work n _) (Nat.mul_le_mul_left _ h.2.1)⟩

def low (f : Nat→Fin σ) (n s D : Nat) : List (Bounds×Nat) :=
  lowSchedule D (generate f n s).runs

def largeRuns (f : Nat→Fin σ) (n s Q : Nat) : List Bounds :=
  (generate f n s).runs.filter (fun R=>decide (Q<R.period ∧ 3*R.period≤R.hi-R.lo))

def large (f : Nat→Fin σ) (n s Q : Nat) : List (Bounds×(Nat×Nat)) :=
  largeSchedule (largeRuns f n s Q)

theorem low_bound (f : Nat→Fin σ) (n s D : Nat) :
    (low f n s D).length≤(D+1)*(2*n*DyadicIndex.heightFor n) :=
  lowSchedule_bound f n D _ (generate_sound f n s) (generate_nodup f n s)

theorem large_bound (f : Nat→Fin σ) (n s Q : Nat) :
    (large f n s Q).length≤(3*n*(2*n*DyadicIndex.heightFor n))/(Q+1) := by
  apply largeSchedule_bound f n Q
  · intro R hm
    exact generate_sound f n s R (List.mem_filter.mp hm).1
  · exact (generate_nodup f n s).filter _
  · intro R hm
    exact of_decide_eq_true (List.mem_filter.mp hm).2

theorem low_complete (f : Nat→Fin σ) (n s D p e d : Nat) (R : Bounds)
    (hR : R.Valid f n) (hs : 0<s) (hlong : s≤e-p)
    (hl : R.lo≤p) (hr : e+d≤R.hi) (hd : R.period=d)
    (hp : p∈lowStarts R D) : (R,p)∈low f n s D := by
  apply (lowSchedule_mem D _ R p).mpr
  exact ⟨generate_complete f n s R hR hs (by omega),hp⟩

theorem large_complete (f : Nat→Fin σ) (n s Q p e d : Nat) (R : Bounds)
    (hR : R.Valid f n) (hs : 0<s) (hlong : s≤e-p)
    (hl : R.lo≤p) (hr : e+d≤R.hi) (hqd : R.period≤d)
    (hc : 3*R.period≤R.hi-R.lo) (hQ : Q<R.period)
    (hp : (p,d)∈largePairs R) : (R,(p,d))∈large f n s Q := by
  apply (largeSchedule_mem _ R p d).mpr
  refine ⟨List.mem_filter.mpr ⟨?_,decide_eq_true ⟨hQ,hc⟩⟩,hp⟩
  exact generate_complete f n s R hR hs (by omega)

end REWB.RankIndexSchedule
