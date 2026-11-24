import REWB.P2Periodic

/-! Five-phase enumeration for the small-period P2 branch.
    A long outer copy determines both phases of its second occurrence.
    Inner length equality determines the end phase of its second copy.
    Thus the number of phase layouts tested is q^5, not q^8.
    Soundness is unconditional for a least-period run; completeness here
    is for witnesses whose outer copy has length at least q. -/
namespace REWB.P2Periodic
open REWB.Periodic
variable {α : Type}

structure Five where
  p : Nat
  i : Nat
  a : Nat
  j : Nat
  e : Nat
  deriving Repr

def extend (q : Nat) (v : Five) : Layout Nat :=
  ⟨v.p,v.i,v.a,v.j,
    (v.j+residual q ⟨0,v.i⟩ ⟨0,v.a⟩)%q,v.e,v.p,v.e⟩

def choices (q : Nat) : List Five :=
  (List.range q).flatMap fun p =>
    (List.range q).flatMap fun i =>
      (List.range q).flatMap fun a =>
        (List.range q).flatMap fun j =>
          (List.range q).map fun e=>⟨p,i,a,j,e⟩

private theorem flat_length {X Y : Type} (xs : List X) (f : X→List Y)
    (k : Nat) (h : ∀ x,(f x).length=k) :
    (xs.flatMap f).length=xs.length*k := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons,List.length_append,h,ih,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem choices_length (q : Nat) : (choices q).length=q^5 := by
  unfold choices
  rw [flat_length _ _ (q^4)]
  · rw [List.length_range,Nat.mul_comm q (q^4)] <;> rfl
  · intro p
    rw [flat_length _ _ (q^3)]
    · rw [List.length_range,Nat.mul_comm q (q^3)] <;> rfl
    · intro i
      rw [flat_length _ _ (q^2)]
      · rw [List.length_range,Nat.mul_comm q (q^2)] <;> rfl
      · intro a
        rw [flat_length _ _ q]
        · rw [List.length_range]
          simp [Nat.pow_succ]
        · intro j
          simp

theorem choices_mem (q : Nat) (v : Five)
    (hp : v.p<q) (hi : v.i<q) (ha : v.a<q) (hj : v.j<q) (he : v.e<q) :
    v∈choices q := by
  unfold choices
  refine List.mem_flatMap.mpr ⟨v.p,List.mem_range.mpr hp,?_⟩
  refine List.mem_flatMap.mpr ⟨v.i,List.mem_range.mpr hi,?_⟩
  refine List.mem_flatMap.mpr ⟨v.a,List.mem_range.mpr ha,?_⟩
  refine List.mem_flatMap.mpr ⟨v.j,List.mem_range.mpr hj,?_⟩
  exact List.mem_map.mpr ⟨v.e,List.mem_range.mpr he,by cases v; rfl⟩

theorem mod_shift (q a b : Nat) (hab : a≤b) (h : q∣b-a) :
    b%q=a%q := by
  obtain ⟨m,hm⟩ := h
  have he : b=a+q*m := by omega
  rw [he,Nat.add_mod,Nat.mul_mod,Nat.mod_self,Nat.zero_mul,Nat.zero_mod,Nat.add_zero,Nat.mod_mod]

theorem residual_mod (q a b : Nat) (hq : 0<q) (hab : a≤b) :
    residual q ⟨0,a%q⟩ ⟨0,b%q⟩=(b-a)%q := by
  have ho : (coord q a).pos q≤(coord q b).pos q := by
    rw [coord_pos,coord_pos]
    exact hab
  have hlen := coordinate_length q (coord q a) (coord q b) hq
    (coord_phase q a hq) (coord_phase q b hq) ho
  rw [coord_pos,coord_pos] at hlen
  have he := hlen.2.2
  change residual q (coord q a) (coord q b)=(b-a)%q
  rw [he,Nat.add_mod,Nat.mul_mod,Nat.mod_self,Nat.mul_zero,Nat.zero_mod,Nat.zero_add,
    Nat.mod_eq_of_lt hlen.2.1]
  exact (Nat.mod_eq_of_lt hlen.2.1).symm

theorem phase_family (P : SevenDFA α) (s : Nat→α) (q n : Nat)
    (h : LeastPeriod s n q) (pre post : Word α) (x : Layout Nat)
    (hw : Witness P s n pre post x) (hlong : q≤x.e-x.p) :
    ∃ v,v∈choices q ∧ extend q v=phaseOf q x := by
  rcases hw with ⟨hpi,hia,haj,hjt,hte,hek,hkf,hfn,_,_,_,_,_,_,_,hu,hv⟩
  have hul := congrArg List.length hu
  have hvl := congrArg List.length hv
  simp only [factor,segment_length] at hul hvl
  have hpe : x.p≤x.e := by omega
  have hpk : x.p≤x.k := by omega
  have heq : segment s x.p (x.f-x.k)=segment s x.k (x.f-x.k) := by
    unfold factor at hv
    rwa [hvl] at hv
  have hdiv := equal_long_factor_same_phase h hpk (show x.k+(x.f-x.k)≤n by omega)
    (show q≤x.f-x.k by omega) ((segment_eq_points _ _ _ _).mp heq)
  have hkp := mod_shift q x.p x.k hpk hdiv
  have hshift : x.f-x.e=x.k-x.p := by omega
  have hfe : x.f%q=x.e%q := mod_shift q x.e x.f (by omega) (by rwa [hshift])
  have ht : x.t%q=(x.j%q+residual q ⟨0,x.i%q⟩ ⟨0,x.a%q⟩)%q := by
    rw [residual_mod q x.i x.a h.1 hia]
    have hh : x.t=x.j+(x.a-x.i) := by omega
    rw [hh,Nat.add_mod]
  let v : Five := ⟨x.p%q,x.i%q,x.a%q,x.j%q,x.e%q⟩
  refine ⟨v,choices_mem q v (Nat.mod_lt _ h.1) (Nat.mod_lt _ h.1)
    (Nat.mod_lt _ h.1) (Nat.mod_lt _ h.1) (Nat.mod_lt _ h.1),?_⟩
  cases x
  simp only [v,extend,phaseOf,Layout.map]
  rw [← ht,hkp,hfe]

def solveFamily [DecidableEq α] (P : SevenDFA α) (s : Nat→α) (n q : Nat)
    (pre post : Word α) : Bool :=
  (choices q).any (fun v=>solveAt P s n q pre post (extend q v))

theorem solveFamily_sound [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (n q : Nat) (h : LeastPeriod s n q) (pre post : Word α)
    (hs : solveFamily P s n q pre post=true) :
    MatchesWithin P.nested2 (pre++segment s 0 n++post) 2 := by
  obtain ⟨v,_,hv⟩ := List.any_eq_true.mp hs
  exact solveAt_sound P s n q h pre post _ hv

theorem solveFamily_complete_long [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (n q : Nat) (h : LeastPeriod s n q) (pre post : Word α) (x : Layout Nat)
    (hw : Witness P s n pre post x) (hlong : q≤x.e-x.p) :
    solveFamily P s n q pre post=true := by
  obtain ⟨v,hv,he⟩ := phase_family P s q n h pre post x hw hlong
  apply List.any_eq_true.mpr
  refine ⟨v,hv,?_⟩
  rw [he]
  exact solveAt_complete P s n q h pre post x hw

end REWB.P2Periodic
