import REWB.ThreeSquares

/-! Exact charging of primitive square occurrences. The dyadic sparsity
    theorem bounds the number of position/period pairs, not just the
    number of distinct words. This is the budget required by the
    large-period and cubic-run branches of the proposed matcher. -/
namespace REWB.RunBudget
open REWB.RunGeometry
variable {α : Type}

abbrev Key := Nat × Nat

def starts (a p : Nat) : Nat→List Key
  | 0 => []
  | k+1 => (a,p)::starts (a+1) p k

theorem starts_length (a p k : Nat) : (starts a p k).length=k := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    change (starts (a+1) p k).length+1=k+1
    rw [ih]

theorem starts_mem (a p k : Nat) (x : Key) :
    x∈starts a p k ↔ a≤x.1 ∧ x.1<a+k ∧ x.2=p := by
  induction k generalizing a with
  | zero =>
    constructor
    · intro h; simp [starts] at h
    · intro h; have hh := h.2.1; omega
  | succ k ih =>
    rw [starts,List.mem_cons,ih]
    constructor
    · rintro (h|⟨h1,h2,h3⟩)
      · subst x
        exact ⟨by omega,by omega,rfl⟩
      · exact ⟨by omega,by omega,h3⟩
    · rintro ⟨h1,h2,h3⟩
      by_cases he : x.1=a
      · left
        exact Prod.ext he h3
      · exact Or.inr ⟨by omega,by omega,h3⟩

theorem starts_nodup (a p k : Nat) : (starts a p k).Nodup := by
  induction k generalizing a with
  | zero => exact List.nodup_nil
  | succ k ih =>
    rw [starts,List.nodup_cons]
    refine ⟨?_,ih (a+1)⟩
    intro h
    have hh := (starts_mem (a+1) p k (a,p)).mp h
    omega

def mass (R : Bounds) : Nat := R.hi-R.lo-2*R.period+1

def charge (R : Bounds) : List Key := starts R.lo R.period (mass R)

theorem charge_length (R : Bounds) : (charge R).length=mass R :=
  starts_length _ _ _

theorem charge_mem (f : Nat→α) (n : Nat) (R : Bounds) (h : R.Valid f n)
    (x : Key) :
    x∈charge R ↔ R.SquareStart x.1 ∧ x.2=R.period := by
  have hlen := h.2.2.1
  unfold charge mass Bounds.SquareStart
  rw [starts_mem]
  constructor
  · rintro ⟨h1,h2,h3⟩
    exact ⟨⟨h1,by omega⟩,h3⟩
  · rintro ⟨⟨h1,h2⟩,h3⟩
    exact ⟨h1,by omega,h3⟩

def charges : List Bounds→List Key
  | [] => []
  | R::Rs => charge R++charges Rs

def totalMass : List Bounds→Nat
  | [] => 0
  | R::Rs => mass R+totalMass Rs

theorem charges_length (Rs : List Bounds) :
    (charges Rs).length=totalMass Rs := by
  induction Rs with
  | nil => rfl
  | cons R Rs ih =>
    rw [charges,List.length_append,charge_length,ih,totalMass]

theorem charges_mem (Rs : List Bounds) (x : Key) :
    x∈charges Rs ↔ ∃ R,R∈Rs ∧ x∈charge R := by
  induction Rs with
  | nil => simp [charges]
  | cons R Rs ih =>
    rw [charges,List.mem_append,ih]
    constructor
    · rintro (h|⟨S,hS,h⟩)
      · exact ⟨R,by simp,h⟩
      · exact ⟨S,List.mem_cons.mpr (Or.inr hS),h⟩
    · rintro ⟨S,hS,h⟩
      rcases List.mem_cons.mp hS with he|hm
      · subst S
        exact Or.inl h
      · exact Or.inr ⟨S,hm,h⟩

private theorem append_nodup {X : Type} (xs ys : List X)
    (hx : xs.Nodup) (hy : ys.Nodup) (hd : ∀ x,x∈xs→x∉ys) :
    (xs++ys).Nodup := by
  induction xs with
  | nil => exact hy
  | cons x xs ih =>
    rw [List.cons_append,List.nodup_cons]
    have hh := List.nodup_cons.mp hx
    refine ⟨?_,ih hh.2 (fun v hv=>hd v (List.mem_cons.mpr (Or.inr hv)))⟩
    intro h
    rcases List.mem_append.mp h with h|h
    · exact hh.1 h
    · exact hd x (by simp) h

theorem charges_nodup (f : Nat→α) (n : Nat) (Rs : List Bounds)
    (hR : ∀ R,R∈Rs→R.Valid f n) (hd : Rs.Nodup) :
    (charges Rs).Nodup := by
  induction Rs with
  | nil => exact List.nodup_nil
  | cons R Rs ih =>
    have h := List.nodup_cons.mp hd
    change (charge R++charges Rs).Nodup
    apply append_nodup _ _ (starts_nodup _ _ _)
      (ih (fun S hS=>hR S (by simp [hS])) h.2)
    intro x hx hrest
    obtain ⟨S,hS,hxS⟩ := (charges_mem Rs x).mp hrest
    have hvR := hR R (by simp)
    have hvS := hR S (by simp [hS])
    obtain ⟨hsR,hpR⟩ := (charge_mem f n R hvR x).mp hx
    obtain ⟨hsS,hpS⟩ := (charge_mem f n S hvS x).mp hxS
    have he := square_start_unique f n R S hvR hvS x.1 (hpR.symm.trans hpS) hsR hsS
    exact h.1 (by rwa [he])

theorem charges_primitive (f : Nat→α) (n : Nat) (Rs : List Bounds)
    (hR : ∀ R,R∈Rs→R.Valid f n) :
    ∀ x,x∈charges Rs→PrimitiveSquare f n x.1 x.2 := by
  intro x hx
  obtain ⟨R,hR',hxR⟩ := (charges_mem Rs x).mp hx
  obtain ⟨hi,hp⟩ := (charge_mem f n R (hR R hR') x).mp hxR
  rw [hp]
  exact square_start_sound f n R (hR R hR') x.1 hi

private theorem filter_nodup {X : Type} (p : X→Bool) (xs : List X)
    (h : xs.Nodup) : (xs.filter p).Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    have hh := List.nodup_cons.mp h
    cases hp : p x
    · simp only [List.filter_cons,hp,Bool.false_eq_true,if_false]
      exact ih hh.2
    · simp only [List.filter_cons,hp,if_true,List.nodup_cons]
      exact ⟨fun hx=>hh.1 (List.mem_filter.mp hx).1,ih hh.2⟩

private theorem filter_partition {X : Type} (p : X→Bool) (xs : List X) :
    (xs.filter p).length+(xs.filter (fun x=> !p x)).length=xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases hp : p x <;> simp only [List.filter_cons,hp,Bool.not_false,Bool.not_true,
      Bool.false_eq_true,if_false,if_true,List.length_cons] <;> omega

private theorem three_distinct (f : Nat→α) (n i b p q r : Nat)
    (hp : PrimitiveSquare f n i p) (hq : PrimitiveSquare f n i q)
    (hr : PrimitiveSquare f n i r)
    (h1 : p≠q) (h2 : p≠r) (h3 : q≠r)
    (bp : b≤p ∧ p<2*b) (bq : b≤q ∧ q<2*b) (br : b≤r ∧ r<2*b) : False := by
  have hs : (p<q ∧ q<r) ∨ (p<r ∧ r<q) ∨ (q<p ∧ p<r) ∨
      (q<r ∧ r<p) ∨ (r<p ∧ p<q) ∨ (r<q ∧ q<p) := by omega
  rcases hs with h|h|h|h|h|h
  · exact three_same_scale f n i b p q r hp hq hr h.1 h.2 bp.1 br.2
  · exact three_same_scale f n i b p r q hp hr hq h.1 h.2 bp.1 bq.2
  · exact three_same_scale f n i b q p r hq hp hr h.1 h.2 bq.1 br.2
  · exact three_same_scale f n i b q r p hq hr hp h.1 h.2 bq.1 bp.2
  · exact three_same_scale f n i b r p q hr hp hq h.1 h.2 br.1 bq.2
  · exact three_same_scale f n i b r q p hr hq hp h.1 h.2 br.1 bp.2

theorem one_position_bound (f : Nat→α) (n i b : Nat) (xs : List Key)
    (hd : xs.Nodup)
    (h : ∀ x,x∈xs→x.1=i ∧ b≤x.2 ∧ x.2<2*b ∧ PrimitiveSquare f n x.1 x.2) :
    xs.length≤2 := by
  cases xs with
  | nil => decide
  | cons x xs =>
    cases xs with
    | nil => decide
    | cons y ys =>
      cases ys with
      | nil => decide
      | cons z zs =>
        obtain ⟨hx,hxs⟩ := List.nodup_cons.mp hd
        obtain ⟨hy,hys⟩ := List.nodup_cons.mp hxs
        obtain ⟨hxi,hxb,hxu,hxP⟩ := h x (by simp)
        obtain ⟨hyi,hyb,hyu,hyP⟩ := h y (by simp)
        obtain ⟨hzi,hzb,hzu,hzP⟩ := h z (by simp)
        have hxy : x.2≠y.2 := by
          intro he
          have hh : x=y := Prod.ext (hxi.trans hyi.symm) he
          exact hx (by simp [hh])
        have hxz : x.2≠z.2 := by
          intro he
          have hh : x=z := Prod.ext (hxi.trans hzi.symm) he
          exact hx (by simp [hh])
        have hyz : y.2≠z.2 := by
          intro he
          have hh : y=z := Prod.ext (hyi.trans hzi.symm) he
          exact hy (by simp [hh])
        rw [hxi] at hxP
        rw [hyi] at hyP
        rw [hzi] at hzP
        exact False.elim (three_distinct f n i b x.2 y.2 z.2 hxP hyP hzP
          hxy hxz hyz ⟨hxb,hxu⟩ ⟨hyb,hyu⟩ ⟨hzb,hzu⟩)

theorem scale_bound (f : Nat→α) (n b k : Nat) (xs : List Key)
    (hd : xs.Nodup)
    (h : ∀ x,x∈xs→x.1<k ∧ b≤x.2 ∧ x.2<2*b ∧ PrimitiveSquare f n x.1 x.2) :
    xs.length≤2*k := by
  induction k generalizing xs with
  | zero =>
    cases xs with
    | nil => decide
    | cons x xs =>
      have hh := (h x (by simp)).1
      omega
  | succ k ih =>
    let p := fun x : Key=>decide (x.1=k)
    let ys := xs.filter p
    let zs := xs.filter (fun x=> !p x)
    have hlen : ys.length+zs.length=xs.length := filter_partition p xs
    have hy := one_position_bound f n k b ys (filter_nodup p xs hd)
      (fun x hx=>by
        have hh := List.mem_filter.mp hx
        have hpos : x.1=k := of_decide_eq_true hh.2
        exact ⟨hpos,(h x hh.1).2⟩)
    have hz := ih zs (filter_nodup _ xs hd) (fun x hx=>by
      have hh := List.mem_filter.mp hx
      have hpos : x.1≠k := by
        intro he
        have hq : p x=true := decide_eq_true he
        rw [hq] at hh
        simp at hh
      obtain ⟨h1,h2⟩ := h x hh.1
      exact ⟨by omega,h2⟩)
    omega

/-- Sum over dyadic scales. A positive period below 2^h contributes
    to exactly one of h classes, each containing at most 2n pairs. -/
theorem primitive_budget (f : Nat→α) (n h : Nat) (xs : List Key)
    (hd : xs.Nodup)
    (hs : ∀ x,x∈xs→PrimitiveSquare f n x.1 x.2 ∧ x.2<2^h) :
    xs.length≤2*n*h := by
  induction h generalizing xs with
  | zero =>
    cases xs with
    | nil => simp
    | cons x xs =>
      have hh := hs x (by simp)
      have hp := hh.1.2.1
      simp only [Nat.pow_zero] at hh
      omega
  | succ h ih =>
    let p := fun x : Key=>decide (x.2<2^h)
    let ys := xs.filter p
    let zs := xs.filter (fun x=> !p x)
    have hlen : ys.length+zs.length=xs.length := filter_partition p xs
    have hy := ih ys (filter_nodup p xs hd) (fun x hx=>by
      have hh := List.mem_filter.mp hx
      exact ⟨(hs x hh.1).1,of_decide_eq_true hh.2⟩)
    have hz := scale_bound f n (2^h) n zs (filter_nodup _ xs hd) (fun x hx=>by
      have hh := List.mem_filter.mp hx
      have hlow : 2^h≤x.2 := by
        by_cases ht : x.2<2^h
        · have hq : p x=true := decide_eq_true ht
          rw [hq] at hh
          simp at hh
        · omega
      obtain ⟨hP,hb⟩ := hs x hh.1
      have hp := hP.2.1
      have hn := hP.1
      rw [Nat.pow_succ] at hb
      exact ⟨by omega,hlow,by omega,hP⟩)
    rw [Nat.mul_succ]
    omega

/-- Exact weighted-run bound for any duplicate-free list of valid runs.
    No algorithm for enumerating the list is assumed by this theorem. -/
theorem totalMass_bound (f : Nat→α) (n : Nat) (Rs : List Bounds)
    (hd : Rs.Nodup) (hR : ∀ R,R∈Rs→R.Valid f n) :
    totalMass Rs≤2*n*(DyadicIndex.heightFor n) := by
  have hp : n<2^(DyadicIndex.heightFor n) := by
    unfold DyadicIndex.heightFor
    exact Nat.lt_log2_self (n:=n)
  have h := primitive_budget f n (DyadicIndex.heightFor n) (charges Rs)
    (charges_nodup f n Rs hR hd) (fun x hx=>by
      have hP := charges_primitive f n Rs hR x hx
      have hlen := hP.1
      exact ⟨hP,by omega⟩)
  rwa [charges_length] at h

end REWB.RunBudget
