import REWB.PeriodicSystem

/-! Integer elimination after normalizing all bounds on the eliminated
    variable to unit coefficients. Congruences are represented by a
    predicate invariant under shifts by a positive common period.
    The resulting finite disjunction does not enumerate the magnitudes
    of the numeric lower or upper bounds. -/
namespace REWB.IntegerProjection

def Above (xs : List Int) (x : Int) : Prop := ∀ a,a∈xs→a≤x
def Below (xs : List Int) (x : Int) : Prop := ∀ a,a∈xs→x≤a

theorem maximum (a : Int) (xs : List Int) :
    ∃ m,m∈a::xs ∧ Above (a::xs) m := by
  induction xs generalizing a with
  | nil =>
    refine ⟨a,by simp,?_⟩
    intro v hv
    have he : v=a := by simpa using hv
    subst v
    exact Int.le_refl _
  | cons b bs ih =>
    obtain ⟨m,hm,hmax⟩ := ih b
    by_cases h : a≤m
    · refine ⟨m,by simp [hm],?_⟩
      intro v hv
      rcases List.mem_cons.mp hv with hv|hv
      · simpa [hv] using h
      · exact hmax v hv
    · refine ⟨a,by simp,?_⟩
      intro v hv
      rcases List.mem_cons.mp hv with hv|hv
      · simp [hv]
      · have hh := hmax v hv
        omega

theorem minimum (a : Int) (xs : List Int) :
    ∃ m,m∈a::xs ∧ Below (a::xs) m := by
  induction xs generalizing a with
  | nil =>
    refine ⟨a,by simp,?_⟩
    intro v hv
    have he : v=a := by simpa using hv
    subst v
    exact Int.le_refl _
  | cons b bs ih =>
    obtain ⟨m,hm,hmin⟩ := ih b
    by_cases h : m≤a
    · refine ⟨m,by simp [hm],?_⟩
      intro v hv
      rcases List.mem_cons.mp hv with hv|hv
      · simpa [hv] using h
      · exact hmin v hv
    · refine ⟨a,by simp,?_⟩
      intro v hv
      rcases List.mem_cons.mp hv with hv|hv
      · simp [hv]
      · have hh := hmin v hv
        omega

def ShiftInvariant (K : Int) (P : Int→Prop) : Prop :=
  ∀ x z, P (x+K*z) ↔ P x

/-- A congruence of an arbitrary affine expression is periodic whenever
    the common period is a multiple of its modulus. -/
theorem dvd_guard (K m a b : Int) (h : m∣K) :
    ShiftInvariant K (fun x=>m∣a*x+b) := by
  intro x z
  obtain ⟨t,ht⟩ := h
  have hd : m∣a*(K*z) := by
    refine ⟨a*t*z,?_⟩
    rw [ht]
    simp only [Int.mul_assoc,Int.mul_left_comm,Int.mul_comm]
  have he : a*(x+K*z)+b=(a*x+b)+a*(K*z) := by
    rw [Int.mul_add]
    omega
  change (m∣a*(x+K*z)+b) ↔ m∣a*x+b
  rw [he,Int.dvd_add_left hd]

theorem and_guard (K : Int) (P Q : Int→Prop)
    (hp : ShiftInvariant K P) (hq : ShiftInvariant K Q) :
    ShiftInvariant K (fun x=>P x ∧ Q x) := by
  intro x z
  change (P (x+K*z) ∧ Q (x+K*z)) ↔ P x ∧ Q x
  rw [hp,hq]

theorem emod_range (x : Int) (K : Nat) (hK : 0<K) :
    ∃ r : Nat,r<K ∧ (r:Int)=x%(K:Int) := by
  have hp : 0<(K:Int) := by omega
  have hn := Int.emod_nonneg x (by omega : (K:Int)≠0)
  have ht := Int.emod_lt_of_pos x hp
  let r := (x%(K:Int)).toNat
  have he : (r:Int)=x%(K:Int) := by
    change (((x%(K:Int)).toNat):Int)=_
    rw [Int.ofNat_toNat]
    omega
  exact ⟨r,by omega,he⟩

/-- Eliminate one integer variable with a positive lower bound list.
    A maximum lower bound plus a residue is enough to witness every
    satisfiable conjunction, even when all bounds are negative. -/
theorem eliminate_nonempty (lo hi : List Int) (K : Nat)
    (hK : 0<K) (P : Int→Prop) (hP : ShiftInvariant (K:Int) P)
    (hn : lo≠[]) :
    (∃ x,Above lo x ∧ Below hi x ∧ P x) ↔
      ∃ l,l∈lo ∧ ∃ r : Nat,r<K ∧
        Above lo (l+r) ∧ Below hi (l+r) ∧ P (l+r) := by
  constructor
  · rintro ⟨x,hlo,hhi,hx⟩
    cases lo with
    | nil => contradiction
    | cons a as =>
      obtain ⟨l,hl,hm⟩ := maximum a as
      obtain ⟨r,hr,he⟩ := emod_range (x-l) K hK
      have hb := hlo l hl
      have hq : 0≤(x-l)/(K:Int) :=
        Int.ediv_nonneg (by omega) (by omega)
      have hd := Int.emod_add_ediv (x-l) (K:Int)
      rw [← he] at hd
      have hprod : 0≤(K:Int)*((x-l)/(K:Int)) :=
        Int.mul_nonneg (by omega) hq
      have hs : x=(l+r)+(K:Int)*((x-l)/(K:Int)) := by omega
      refine ⟨l,hl,r,hr,?_,?_,?_⟩
      · intro v hv
        have hh := hm v hv
        omega
      · intro v hv
        have hh := hhi v hv
        omega
      · apply (hP (l+r) ((x-l)/(K:Int))).mp
        rwa [← hs]
  · rintro ⟨l,hl,r,hr,hlo,hhi,h⟩
    exact ⟨l+r,hlo,hhi,h⟩

/-- Without a lower bound, any accepted residue can be shifted down
    far enough to satisfy every upper bound. No upper bound is retained
    in the resulting formula. -/
theorem eliminate_empty (hi : List Int) (K : Nat) (hK : 0<K)
    (P : Int→Prop) (hP : ShiftInvariant (K:Int) P) :
    (∃ x,Below hi x ∧ P x) ↔
      ∃ r : Nat,r<K ∧ P (r:Int) := by
  constructor
  · rintro ⟨x,_,hx⟩
    obtain ⟨r,hr,he⟩ := emod_range x K hK
    have hd := Int.emod_add_ediv x (K:Int)
    rw [← he] at hd
    refine ⟨r,hr,(hP r (x/(K:Int))).mp ?_⟩
    rwa [hd]
  · rintro ⟨r,hr,h⟩
    cases hi with
    | nil => exact ⟨r,by simp [Below],h⟩
    | cons a as =>
      obtain ⟨u,hu,hm⟩ := minimum a as
      let z := (u-(r:Int))/(K:Int)
      have hd := Int.emod_add_ediv (u-(r:Int)) (K:Int)
      have hn := Int.emod_nonneg (u-(r:Int)) (by omega : (K:Int)≠0)
      have hle : (r:Int)+(K:Int)*z≤u := by
        dsimp only [z]
        omega
      refine ⟨(r:Int)+(K:Int)*z,?_,(hP r z).mpr h⟩
      intro v hv
      have hv' := hm v hv
      omega

/-- A finite list of candidate values. The constant-offset list
    depends only on the common congruence period, not on the bounds. -/
def candidates (lo : List Int) (K : Nat) : List Int :=
  if lo.isEmpty then (List.range K).map Int.ofNat
  else lo.flatMap (fun l=>(List.range K).map (fun r : Nat=>l+(r:Int)))

def feasible (lo hi : List Int) (P : Int→Prop) (x : Int) : Prop :=
  Above lo x ∧ Below hi x ∧ P x

theorem finite_elimination (lo hi : List Int) (K : Nat) (hK : 0<K)
    (P : Int→Prop) (hP : ShiftInvariant (K:Int) P) :
    (∃ x,feasible lo hi P x) ↔
      ∃ c,c∈candidates lo K ∧
        (if lo.isEmpty then P c else feasible lo hi P c) := by
  cases lo with
  | nil =>
    have he : (∃ x,feasible [] hi P x) ↔ ∃ x,Below hi x ∧ P x := by
      simp [feasible,Above]
    rw [he,eliminate_empty hi K hK P hP]
    simp only [candidates,List.isEmpty_nil,if_true,List.mem_map,List.mem_range]
    constructor
    · rintro ⟨r,hr,h⟩
      exact ⟨r,⟨r,hr,rfl⟩,h⟩
    · rintro ⟨c,⟨r,hr,rfl⟩,h⟩
      exact ⟨r,hr,h⟩
  | cons l ls =>
    unfold feasible
    rw [eliminate_nonempty (l::ls) hi K hK P hP (by simp)]
    simp only [candidates,List.isEmpty_cons,Bool.false_eq_true,if_false,List.mem_flatMap,List.mem_map,List.mem_range]
    constructor
    · rintro ⟨a,ha,r,hr,h1,h2,h3⟩
      exact ⟨a+r,⟨a,ha,r,hr,rfl⟩,h1,h2,h3⟩
    · rintro ⟨c,⟨a,ha,r,hr,rfl⟩,h1,h2,h3⟩
      exact ⟨a,ha,r,hr,h1,h2,h3⟩

theorem candidates_length (lo : List Int) (K : Nat) :
    (candidates lo K).length=(max 1 lo.length)*K := by
  have aux : ∀ xs : List Int,
      (xs.flatMap (fun l=>(List.range K).map (fun r : Nat=>l+(r:Int)))).length=xs.length*K := by
    intro xs
    induction xs with
    | nil => simp
    | cons x xs ih =>
      simp only [List.flatMap_cons,List.length_append,List.length_map,List.length_range,
        ih,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
  cases lo with
  | nil => simp [candidates]
  | cons l ls =>
    simp only [candidates,List.isEmpty_cons,Bool.false_eq_true,if_false,aux]
    rw [Nat.max_eq_right (by simp)]

end REWB.IntegerProjection
