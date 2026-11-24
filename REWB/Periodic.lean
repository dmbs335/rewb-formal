import REWB.BlockMatcher

/-! Periodicity of a finite interval of a total symbol function.
    The function outside [0,n) is irrelevant. No suffix-array or runs
    theorem is assumed. -/
namespace REWB.Periodic
variable {α : Type}

def Period (f : Nat → α) (n p : Nat) : Prop :=
  ∀ i, i+p<n → f i=f (i+p)

theorem restrict {f : Nat → α} {n m p : Nat}
    (h : Period f n p) (hm : m≤n) : Period f m p := by
  intro i hi
  exact h i (by omega)

theorem period_multiple {f : Nat → α} {n p : Nat}
    (h : Period f n p) (i k : Nat) (hi : i+k*p<n) :
    f i=f (i+k*p) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have he : i+(k+1)*p=(i+k*p)+p := by
      rw [Nat.add_mul,Nat.one_mul]
      omega
    rw [he] at hi ⊢
    exact (ih (by omega)).trans (h (i+k*p) hi)

theorem period_residue {f : Nat → α} {n p : Nat}
    (h : Period f n p) (i : Nat) (hi : i<n) :
    f i=f (i%p) := by
  have he : i%p+(i/p)*p=i := by
    rw [Nat.mul_comm (i/p) p]
    exact Nat.mod_add_div i p
  have hh := period_multiple h (i%p) (i/p) (by rwa [he])
  rw [he] at hh
  exact hh.symm

theorem residue_period {f : Nat → α} {n p : Nat}
    (h : ∀ i,i<n → f i=f (i%p)) : Period f n p := by
  intro i hi
  have he : (i+p)%p=i%p := by
    rw [Nat.add_mod,Nat.mod_self,Nat.add_zero,Nat.mod_mod]
  rw [h i (by omega),h (i+p) hi,he]

/-- A smaller period of the prefix extends across the original period
    when the prefix contains a complete p-block and g divides p. -/
theorem extend_period {f : Nat → α} {n m p g : Nat}
    (hp : 0<p) (hm : p≤m) (hd : g∣p)
    (h : Period f n p) (hg : Period f m g) : Period f n g := by
  apply residue_period
  intro i hi
  have hr : i%p<m := Nat.lt_of_lt_of_le (Nat.mod_lt i hp) hm
  calc
    f i = f (i%p) := period_residue h i hi
    _ = f ((i%p)%g) := period_residue hg _ hr
    _ = f (i%g) := by rw [Nat.mod_mod_of_dvd i hd]

/-- Euclidean reduction: on the prefix of length n-p, q-p is a period
    if p and q are periods of the original interval. -/
theorem subtract_period {f : Nat → α} {n p q : Nat}
    (hpq : p≤q) (hp : Period f n p) (hq : Period f n q) :
    Period f (n-p) (q-p) := by
  intro i hi
  have hq' : i+q<n := by omega
  have he : i+(q-p)+p=i+q := by omega
  have h := hp (i+(q-p)) (by rwa [he])
  rw [he] at h
  exact (hq i hq').trans h.symm

theorem gcd_sub_right (p q : Nat) (h : p≤q) :
    Nat.gcd p (q-p)=Nat.gcd p q := by
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd
    · exact Nat.gcd_dvd_left _ _
    · have hh := Nat.dvd_add (Nat.gcd_dvd_left p (q-p)) (Nat.gcd_dvd_right p (q-p))
      rwa [show p+(q-p)=q by omega] at hh
  · exact Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
      (Nat.dvd_sub (Nat.gcd_dvd_right p q) (Nat.gcd_dvd_left p q))

theorem reduce_length (n p q : Nat) (hp : 0<p) (hpq : p<q)
    (hn : p+q≤n+Nat.gcd p q) :
    p≤n-p ∧ p+(q-p)≤(n-p)+Nat.gcd p (q-p) := by
  have hg : Nat.gcd p q≤q-p := by
    rw [← gcd_sub_right p q (by omega)]
    exact Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right _ _)
  rw [gcd_sub_right p q (by omega)]
  omega

/-- Fine-Wilf, including the sharp n >= p+q-gcd(p,q) threshold.
    The proof decreases p+q by a Euclidean subtraction. -/
theorem fineWilf (f : Nat → α) (n p q : Nat)
    (hp : 0<p) (hq : 0<q) (hn : p+q≤n+Nat.gcd p q)
    (hP : Period f n p) (hQ : Period f n q) :
    Period f n (Nat.gcd p q) := by
  by_cases he : p=q
  · subst q
    simpa using hP
  · by_cases hlt : p<q
    · obtain ⟨hpre,hsize⟩ := reduce_length n p q hp hlt hn
      have hsmall := fineWilf f (n-p) p (q-p) hp (by omega) hsize
        (restrict hP (Nat.sub_le _ _)) (subtract_period (by omega) hP hQ)
      rw [gcd_sub_right p q (by omega)] at hsmall
      exact extend_period hp hpre (Nat.gcd_dvd_left _ _) hP hsmall
    · have hlt' : q<p := by omega
      have hn' : q+p≤n+Nat.gcd q p := by rw [Nat.gcd_comm q p]; omega
      obtain ⟨hpre,hsize⟩ := reduce_length n q p hq hlt' hn'
      have hsmall := fineWilf f (n-q) q (p-q) hq (by omega) hsize
        (restrict hQ (Nat.sub_le _ _)) (subtract_period (by omega) hQ hP)
      rw [gcd_sub_right q p (by omega),Nat.gcd_comm q p] at hsmall
      exact extend_period hq hpre (Nat.gcd_dvd_right _ _) hQ hsmall
termination_by p+q
decreasing_by all_goals omega

def LeastPeriod (f : Nat → α) (n p : Nat) : Prop :=
  0<p ∧ Period f n p ∧ ∀ q,0<q → Period f n q → p≤q

/-- A sufficiently long second period is a multiple of the least period. -/
theorem least_dvd {f : Nat → α} {n p q : Nat}
    (h : LeastPeriod f n p) (hq : 0<q) (hQ : Period f n q)
    (hn : p+q≤n+Nat.gcd p q) : p∣q := by
  have hgpos : 0<Nat.gcd p q := Nat.gcd_pos_of_pos_left q h.1
  have hg := fineWilf f n p q h.1 hq hn h.2.1 hQ
  have hmin := h.2.2 _ hgpos hg
  have hle := Nat.le_of_dvd h.1 (Nat.gcd_dvd_left p q)
  have he : Nat.gcd p q=p := Nat.le_antisymm hle hmin
  rw [← he]
  exact Nat.gcd_dvd_right p q

/-- Equal overlapping copies generate a period on their entire union.
    hcopy says that every symbol of the length-L first copy agrees with
    the corresponding symbol of the shifted copy. -/
theorem overlap_period (f : Nat → α) (L delta : Nat)
    (hcopy : ∀ i,i<L → f i=f (i+delta)) :
    Period f (L+delta) delta := by
  intro i hi
  exact hcopy i (by omega)

/-- In an overlapping maximal equality region the shift is a multiple
    of the minimum period. Maximality itself is not needed for this lemma;
    proving that the union is a maximal run is a separate obligation. -/
theorem overlap_shift_multiple (f : Nat → α) (L delta p : Nat)
    (hd : 0<delta) (hoverlap : delta≤L)
    (hcopy : ∀ i,i<L → f i=f (i+delta))
    (hmin : LeastPeriod f (L+delta) p) : p∣delta := by
  have hP := overlap_period f L delta hcopy
  have hle := hmin.2.2 delta hd hP
  exact least_dvd hmin hd hP (by omega)

end REWB.Periodic
