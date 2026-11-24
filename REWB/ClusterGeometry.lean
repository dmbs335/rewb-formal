import REWB.PeriodicFactor

/-! Geometry of neighboring occurrences, independent of any suffix tree.
    These local lemmas justify progression clusters. Global amortization
    and maintenance of arbitrary masks are still separate obligations. -/
namespace REWB.Periodic
variable {α : Type}

/-- The first occurrence is our pattern, and the next one starts delta
    symbols later. No occurrence of that pattern starts strictly between. -/
def Consecutive (f : Nat→α) (L delta : Nat) : Prop :=
  (∀ i,i<L → f i=f (i+delta)) ∧
    ∀ s,0<s → s<delta → ¬(∀ i,i<L → f i=f (i+s))

/-- If the Fine-Wilf threshold holds, an adjacent occurrence gap cannot
    skip any intervening multiple of the minimum period. -/
theorem consecutive_gap_eq {f : Nat→α} {L delta q : Nat}
    (hd : 0<delta) (hsmall : delta≤L)
    (hc : Consecutive f L delta) (hmin : LeastPeriod f L q)
    (hfw : q+delta≤L+Nat.gcd q delta) : delta=q := by
  have hbig := overlap_period f L delta hc.1
  have hD : Period f L delta := restrict hbig (by omega)
  have hle := hmin.2.2 delta hd hD
  have hdiv := least_dvd hmin hd hD hfw
  have hu : Period f (L+delta) q := extend_period hd hsmall hdiv hbig hmin.2.1
  by_contra hn
  have hq : q<delta := by omega
  apply hc.2 q hmin.1 hq
  intro i hi
  exact hu i (by omega)

/-- Dense occurrence clusters: consecutive starts separated by at most
    half the pattern length have gap equal to the minimum period. -/
theorem dense_consecutive_gap {f : Nat→α} {L delta q : Nat}
    (hd : 0<delta) (hsmall : 2*delta≤L)
    (hc : Consecutive f L delta) (hmin : LeastPeriod f L q) : delta=q := by
  have hD : Period f L delta := restrict (overlap_period f L delta hc.1) (by omega)
  have hle := hmin.2.2 delta hd hD
  exact consecutive_gap_eq hd (by omega) hc hmin (by omega)

/-- If the gap between distinct dense clusters is larger than the
    minimum period but still overlaps, even the penultimate occurrence
    of the earlier cluster cannot overlap the next cluster. -/
theorem separated_cluster_gap {f : Nat→α} {L delta q : Nat}
    (hd : 0<delta) (hoverlap : delta≤L) (hq : q<delta)
    (hc : Consecutive f L delta) (hmin : LeastPeriod f L q) :
    L<delta+q := by
  by_contra hn
  have he := consecutive_gap_eq hd hoverlap hc hmin (by omega)
  omega

/-- A representative of every residue occurs in each full period block. -/
theorem phase_rep (p a r : Nat) (hp : 0<p) (hr : r<p) :
    ∃ j,a≤j ∧ j<a+p ∧ j%p=r := by
  let s := a%p
  have hs : s<p := Nat.mod_lt a hp
  by_cases hsr : s≤r
  · let d := r-s
    have hd : d<p := by dsimp [d]; omega
    refine ⟨a+d,by omega,by omega,?_⟩
    rw [Nat.add_mod,Nat.mod_eq_of_lt hd]
    have he : a%p+d=r := by change s+d=r; dsimp [d]; omega
    rw [he,Nat.mod_eq_of_lt hr]
  · let d := p+r-s
    have hd : d<p := by dsimp [d]; omega
    refine ⟨a+d,by omega,by omega,?_⟩
    rw [Nat.add_mod,Nat.mod_eq_of_lt hd]
    have he : a%p+d=r+p := by change s+d=r+p; dsimp [d]; omega
    rw [he,Nat.add_mod,Nat.mod_eq_of_lt hr,Nat.mod_self,Nat.add_zero,Nat.mod_eq_of_lt hr]

/-- Equal complete phase blocks imply that their displacement is also a
    period of the entire run. This works even if the blocks overlap. -/
theorem full_phase_shift_period {f : Nat→α} {n p a b : Nat}
    (hp : 0<p) (h : Period f n p) (hab : a≤b) (hb : b+p≤n)
    (he : ∀ i,i<p → f (a+i)=f (b+i)) :
    Period f n (b-a) := by
  intro i hi
  obtain ⟨j,haj,hjp,hmod⟩ := phase_rep p a (i%p) hp (Nat.mod_lt i hp)
  have hjn : j<n := by omega
  have hjdelta : j+(b-a)<n := by omega
  have hshift : f j=f (j+(b-a)) := by
    have hh := he (j-a) (by omega)
    rw [show a+(j-a)=j by omega,show b+(j-a)=j+(b-a) by omega] at hh
    exact hh
  have hmod2 : (j+(b-a))%p=(i+(b-a))%p := by
    rw [Nat.add_mod,Nat.add_mod i,hmod]
  calc
    f i=f (i%p) := period_residue h i (by omega)
    _=f (j%p) := by rw [hmod]
    _=f j := (period_residue h j hjn).symm
    _=f (j+(b-a)) := hshift
    _=f ((j+(b-a))%p) := period_residue h _ hjdelta
    _=f ((i+(b-a))%p) := by rw [hmod2]
    _=f (i+(b-a)) := (period_residue h _ hi).symm

/-- Equal factors of length at least p in the same least-period-p run
    must start at the same phase. Distinct phases can agree only on
    factors shorter than p. -/
theorem equal_long_factor_same_phase {f : Nat→α} {n p a b L : Nat}
    (hmin : LeastPeriod f n p) (hab : a≤b) (hb : b+L≤n)
    (hL : p≤L) (he : ∀ i,i<L → f (a+i)=f (b+i)) : p∣b-a := by
  by_cases hsame : a=b
  · subst b
    simp
  · have hd : 0<b-a := by omega
    have hP := full_phase_shift_period hmin.1 hmin.2.1 hab (by omega)
      (fun i hi=>he i (by omega))
    exact least_dvd hmin hd hP (by omega)

end REWB.Periodic
