import REWB.Periodic

/-! A periodic interval is encoded by one phase block and a repetition
    count plus a residual suffix. The compression is an exact identity,
    not a heuristic or a restriction to captures aligned to the run start. -/
namespace REWB.Periodic
variable {α : Type}

def shift (f : Nat→α) (l : Nat) : Nat→α := fun i=>f (l+i)

theorem shift_period {f : Nat→α} {n p l m : Nat}
    (h : Period f n p) (hm : l+m≤n) : Period (shift f l) m p := by
  intro i hi
  unfold shift
  have he : l+(i+p)=(l+i)+p := by omega
  rw [he]
  exact h (l+i) (by omega)

/-- A maximal equality region and its minimum period yield a maximal
    periodic run. This is a local structural statement, not a bound on
    the number of runs. -/
def Run (f : Nat→α) (n l r p : Nat) : Prop :=
  l<r ∧ r≤n ∧ 2*p≤r-l ∧ LeastPeriod (shift f l) (r-l) p ∧
    (l=0 ∨ ¬Period (shift f (l-1)) (r-l+1) p) ∧
    (r=n ∨ ¬Period (shift f l) (r-l+1) p)

theorem maximal_equality_run (f : Nat→α) (n l L delta p : Nat)
    (hd : 0<delta) (hoverlap : delta≤L) (hn : l+L+delta≤n)
    (hc : ∀ i,i<L → f (l+i)=f (l+i+delta))
    (hleft : l=0 ∨ f (l-1)≠f (l-1+delta))
    (hright : l+L+delta=n ∨ f (l+L)≠f (l+L+delta))
    (hmin : LeastPeriod (shift f l) (L+delta) p) :
    p∣delta ∧ Run f n l (l+L+delta) p := by
  have hcopy : ∀ i,i<L → shift f l i=shift f l (i+delta) := by
    intro i hi
    unfold shift
    rw [show l+(i+delta)=l+i+delta by omega]
    exact hc i hi
  have hperiod := overlap_period (shift f l) L delta hcopy
  have hpd := hmin.2.2 delta hd hperiod
  have hdiv := overlap_shift_multiple (shift f l) L delta p hd hoverlap hcopy hmin
  obtain ⟨k,hk⟩ := hdiv
  have hk' : k*p=delta := by rw [Nat.mul_comm,← hk]
  have hlen : l+L+delta-l=L+delta := by omega
  refine ⟨hdiv,by omega,hn,by omega,?_,?_,?_⟩
  · rwa [hlen]
  · rcases hleft with h|h
    · exact Or.inl h
    · refine Or.inr (fun hp=>h ?_)
      rw [hlen] at hp
      have hh := period_multiple hp 0 k (by rw [hk']; omega)
      simpa only [shift,Nat.add_zero,Nat.zero_add,hk'] using hh
  · rcases hright with h|h
    · exact Or.inl h
    · refine Or.inr (fun hp=>h ?_)
      rw [hlen] at hp
      have hh := period_multiple hp L k (by rw [hk']; omega)
      simpa only [shift,hk',Nat.add_assoc] using hh

def segment (f : Nat→α) (a : Nat) : Nat→Word α
  | 0 => []
  | k+1 => f a::segment f (a+1) k

theorem segment_length (f : Nat→α) (a k : Nat) :
    (segment f a k).length=k := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    change (segment f (a+1) k).length+1=k+1
    rw [ih]

theorem segment_append (f : Nat→α) (a k m : Nat) :
    segment f a (k+m)=segment f a k++segment f (a+k) m := by
  induction k generalizing a with
  | zero => simp [segment]
  | succ k ih =>
    have he : k+1+m=(k+m)+1 := by omega
    rw [he]
    change f a::segment f (a+1) (k+m)=
      f a::(segment f (a+1) k++segment f (a+(k+1)) m)
    rw [ih,show a+1+k=a+(k+1) by omega]

/-- The same phase in a periodic interval has exactly the same symbols,
    even when the two factors overlap. -/
theorem segment_same_phase {f : Nat→α} {n p : Nat}
    (h : Period f n p) (a k m : Nat) (hm : a+k*p+m≤n) :
    segment f a m=segment f (a+k*p) m := by
  induction m generalizing a with
  | zero => rfl
  | succ m ih =>
    change f a::segment f (a+1) m =
      f (a+k*p)::segment f (a+k*p+1) m
    rw [period_multiple h a k (by omega)]
    have he : a+k*p+1=(a+1)+k*p := by omega
    rw [he,ih (a+1) (by omega)]

def repeatWord (u : Word α) : Nat→Word α
  | 0 => []
  | k+1 => repeatWord u k++u

theorem repeatWord_length (u : Word α) (k : Nat) :
    (repeatWord u k).length=k*u.length := by
  induction k with
  | zero => simp [repeatWord]
  | succ k ih =>
    rw [repeatWord,List.length_append,ih,Nat.add_mul,Nat.one_mul]

theorem segment_repeated {f : Nat→α} {n p : Nat}
    (h : Period f n p) (a k : Nat) (hk : a+k*p≤n) :
    segment f a (k*p)=repeatWord (segment f a p) k := by
  induction k with
  | zero => simp [segment,repeatWord]
  | succ k ih =>
    rw [Nat.add_mul,Nat.one_mul] at hk ⊢
    rw [segment_append,ih (by omega),← segment_same_phase h a k p hk]
    rfl

/-- Every factor of a periodic run is represented by a phase-specific
    period block, a quotient, and a remainder. -/
theorem compress_factor {f : Nat→α} {n p : Nat}
    (h : Period f n p) (a L : Nat) (hL : a+L≤n) :
    segment f a L =
      repeatWord (segment f a p) (L/p)++segment f a (L%p) := by
  have he : (L/p)*p+L%p=L := by
    rw [Nat.mul_comm (L/p) p,Nat.add_comm]
    exact Nat.mod_add_div L p
  have h1 := segment_append f a ((L/p)*p) (L%p)
  rw [he] at h1
  rw [h1,segment_repeated h a (L/p) (by omega),
    ← segment_same_phase h a (L/p) (L%p) (by omega)]

/-- A periodic interval's factors of a fixed length only need the
    starting phase, not the absolute block index. -/
theorem compress_same_phase {f : Nat→α} {n p : Nat}
    (h : Period f n p) (a b L : Nat)
    (ha : a≤b) (hb : b+L≤n) (hd : p∣b-a) :
    segment f a L=segment f b L := by
  obtain ⟨k,hk⟩ := hd
  have he : a+k*p=b := by rw [Nat.mul_comm k p,← hk]; omega
  have hh := segment_same_phase h a k L (by rwa [he])
  rwa [he] at hh

def power {M : Type} (o : RangeProducts.Ops M) (x : M) : Nat→M
  | 0 => o.one
  | k+1 => o.mul (power o x k) x

theorem power_add {M : Type} (o : RangeProducts.Ops M) (x : M) (a b : Nat) :
    power o x (a+b)=o.mul (power o x a) (power o x b) := by
  induction b with
  | zero => simp [power,o.mul_one]
  | succ b ih =>
    change o.mul (power o x (a+b)) x =
      o.mul (power o x a) (o.mul (power o x b) x)
    rw [ih,o.assoc]

theorem product_repeat {M : Type} (o : RangeProducts.Ops M) (u : Word M) (k : Nat) :
    RangeProducts.product o (repeatWord u k)=power o (RangeProducts.product o u) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [repeatWord,power,RangeProducts.product_append,ih]

/-- Exact finite-monoid compression of the entire periodic factor. -/
theorem compressed_product {M : Type} (o : RangeProducts.Ops M)
    {f : Nat→M} {n p : Nat} (h : Period f n p) (a L : Nat) (hL : a+L≤n) :
    RangeProducts.product o (segment f a L) =
      o.mul (power o (RangeProducts.product o (segment f a p)) (L/p))
        (RangeProducts.product o (segment f a (L%p))) := by
  rw [compress_factor h a L hL,RangeProducts.product_append,product_repeat]

theorem segment_map {β : Type} (g : α→β) (f : Nat→α) (a L : Nat) :
    (segment f a L).map g=segment (fun i=>g (f i)) a L := by
  induction L generalizing a with
  | zero => rfl
  | succ L ih =>
    change g (f a)::(segment f (a+1) L).map g=
      g (f a)::segment (fun i=>g (f i)) (a+1) L
    rw [ih]

theorem map_period {β : Type} (g : α→β) {f : Nat→α} {n p : Nat}
    (h : Period f n p) : Period (fun i=>g (f i)) n p := by
  intro i hi
  exact congrArg g (h i hi)

/-- A DFA interval transfer is a power of a phase block transfer followed
    by the residual transfer, preserving the original product order. -/
theorem compressed_dfa (d : DFA α) {f : Nat→α} {n p : Nat}
    (h : Period f n p) (a L : Nat) (hL : a+L≤n) :
    d.transition (segment f a L) =
      (RangeProducts.dfaOps d).mul
        (power (RangeProducts.dfaOps d) (d.transition (segment f a p)) (L/p))
        (d.transition (segment f a (L%p))) := by
  have hmap := map_period (fun c q=>d.step q c) h
  have he := compressed_product (RangeProducts.dfaOps d) hmap a L hL
  rw [← segment_map,← segment_map,← segment_map] at he
  simpa only [RangeProducts.dfa_product] using he

end REWB.Periodic
