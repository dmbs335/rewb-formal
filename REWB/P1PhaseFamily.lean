import REWB.UniformJoin
import REWB.SmallPeriodRuns

/-! Three phases suffice for every anchored P1 target whose outer copy
    is at least one period long. This constructs and counts the actual
    target phase schedule, and proves completeness of its projected
    exponent formulas. Enumeration of source events is a separate step. -/
namespace REWB.P1PhaseFamily
open REWB.Periodic REWB.PhaseSolver REWB.AffineProjection REWB.P1Target
variable {α : Type}

structure Three where
  j : Nat
  e : Nat
  rho : Nat
  deriving Repr

def extend (q p : Nat) (v : Three) : Layout Nat :=
  ⟨v.j,(v.j+v.rho)%q,v.e,p%q,v.e⟩

def choices (q : Nat) : List Three :=
  (List.range q).flatMap fun j=>
    (List.range q).flatMap fun e=>
      (List.range q).map fun rho=>⟨j,e,rho⟩

private theorem flat_length {X Y : Type} (xs : List X) (f : X→List Y)
    (k : Nat) (h : ∀ x,(f x).length=k) :
    (xs.flatMap f).length=xs.length*k := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons,List.length_append,h,ih,List.length_cons,
      Nat.add_mul,Nat.one_mul]
    omega

theorem choices_length (q : Nat) : (choices q).length=q^3 := by
  unfold choices
  rw [flat_length _ _ (q*q)]
  · simp only [List.length_range,Nat.pow_succ,Nat.pow_zero,Nat.one_mul]
    ac_rfl
  · intro j
    rw [flat_length _ _ q]
    · rw [List.length_range]
    · intro e
      simp

theorem choices_mem (q : Nat) (v : Three)
    (hj : v.j<q) (he : v.e<q) (hr : v.rho<q) : v∈choices q := by
  refine List.mem_flatMap.mpr ⟨v.j,List.mem_range.mpr hj,?_⟩
  refine List.mem_flatMap.mpr ⟨v.e,List.mem_range.mpr he,?_⟩
  exact List.mem_map.mpr ⟨v.rho,List.mem_range.mpr hr,by cases v; rfl⟩

def phaseOf (q : Nat) (x : Layout Nat) : Layout Nat := x.map (fun z=>z%q)

def envOf (q : Nat) (x : Layout Nat) : List Int :=
  [Int.ofNat (x.j/q),Int.ofNat (x.t/q),Int.ofNat (x.e/q),Int.ofNat (x.k/q),Int.ofNat (x.f/q)]

theorem canonical_absolute (q : Nat) (x : Layout Nat) (m : Int) :
    absolute q (endpoints (phaseOf q x)) (envOf q x++[m])=x := by
  have aux : ∀ z : Nat,(z/q)*q+z%q=z := fun z=>coord_pos q z
  cases x
  simp [absolute,endpoints,phaseOf,Layout.map,Endpoint.pos,Endpoint.coordinate,
    Endpoint.number,Endpoint.phase,envOf,Aff.eval,Coord.pos,aux]

theorem canonical_valid (q n : Nat) (x : Layout Nat) (m : Int) (hq : 0<q)
    (hn : x.j≤n ∧ x.t≤n ∧ x.e≤n ∧ x.k≤n ∧ x.f≤n) :
    Valid (endpoints (phaseOf q x)) q n (envOf q x++[m]) := by
  have aux : ∀ z : Nat,(z/q)*q+z%q=z := fun z=>coord_pos q z
  have hm : ∀ z : Nat,z%q<q := fun z=>Nat.mod_lt z hq
  simpa [Valid,endpoints,phaseOf,Layout.map,Endpoint.pos,Endpoint.coordinate,
    Endpoint.number,Endpoint.phase,Endpoint.valid,envOf,Aff.eval,Coord.pos,aux,hm] using hn

theorem copies_div (q a b : Nat) (hq : 0<q) (hab : a≤b) :
    copies (coord q a) (coord q b)=(b-a)/q := by
  have h := coordinate_length q (coord q a) (coord q b) hq
    (coord_phase q a hq) (coord_phase q b hq) (by simpa only [coord_pos] using hab)
  rw [coord_pos,coord_pos] at h
  rw [h.2.2,Nat.add_comm,Nat.add_mul_div_right _ _ hq,Nat.div_eq_of_lt h.2.1]
  simp

theorem projection_complete [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (n q p : Nat) (h : LeastPeriod s n q) (post : Word α) (x : Layout Nat)
    (hw : Witness P s n p post x) :
    decideFormula (projection P s n q p ((x.t-x.j)%q) post (phaseOf q x))
      [Int.ofNat ((x.t-x.j)/q)]=true := by
  have hp : p≤n := by
    rcases hw with ⟨h1,h2,h3,h4,h5,h6,_⟩
    omega
  apply (projection_correct P s n q p ((x.t-x.j)%q) ((x.t-x.j)/q)
    h hp post (phaseOf q x)).mpr
  have hn : x.j≤n ∧ x.t≤n ∧ x.e≤n ∧ x.k≤n ∧ x.f≤n := by
    rcases hw with ⟨h1,h2,h3,h4,h5,h6,_⟩
    exact ⟨by omega,by omega,by omega,by omega,h6⟩
  let env := envOf q x++[Int.ofNat ((x.t-x.j)/q)]
  let L := endpoints (phaseOf q x)
  have hv := canonical_valid q n x (Int.ofNat ((x.t-x.j)/q)) h.1 hn
  refine ⟨envOf q x,rfl,hv,?_,?_,?_⟩
  · rw [canonical_absolute]
    exact hw
  · exact P2Periodic.residual_mod q x.j x.t h.1 hw.2.1
  · have hj : L.j.coordinate env=coord q x.j := by
      simp [L,env,endpoints,phaseOf,Layout.map,envOf,Endpoint.coordinate,
        Endpoint.number,Endpoint.phase,Aff.eval,coord]
    have ht : L.t.coordinate env=coord q x.t := by
      simp [L,env,endpoints,phaseOf,Layout.map,envOf,Endpoint.coordinate,
        Endpoint.number,Endpoint.phase,Aff.eval,coord]
    have ho : L.j.pos q env≤L.t.pos q env := by
      change (L.j.coordinate env).pos q≤(L.t.coordinate env).pos q
      rw [hj,ht,coord_pos,coord_pos]
      exact hw.2.1
    have hc := count_natural L.j L.t q n env hv.1 hv.2.1 ho
    rw [hj,ht,copies_div q x.j x.t h.1 hw.2.1] at hc
    exact hc

/-- A long repeated outer factor fixes both phases of its second copy.
    The inner length residue fixes the inner-copy end phase. -/
theorem phase_family (P : SevenDFA α) (s : Nat→α) (n q p : Nat)
    (h : LeastPeriod s n q) (post : Word α) (x : Layout Nat)
    (hw : Witness P s n p post x) (hlong : q≤x.e-p) :
    ∃ v,v∈choices q ∧ extend q p v=phaseOf q x ∧ v.rho=(x.t-x.j)%q := by
  rcases hw with ⟨hpj,hjt,hte,hek,hkf,hfn,hD,hB,hF,hG,hH,hv⟩
  have hlen := congrArg List.length hv
  simp only [P2Periodic.factor,segment_length] at hlen
  have heq : segment s p (x.f-x.k)=segment s x.k (x.f-x.k) := by
    unfold P2Periodic.factor at hv
    rwa [hlen] at hv
  have hd := equal_long_factor_same_phase h (show p≤x.k by omega)
    (show x.k+(x.f-x.k)≤n by omega) (show q≤x.f-x.k by omega)
    ((segment_eq_points _ _ _ _).mp heq)
  have hk := P2Periodic.mod_shift q p x.k (by omega) hd
  have hf : x.f%q=x.e%q := P2Periodic.mod_shift q x.e x.f (by omega)
    (by rwa [show x.f-x.e=x.k-p by omega])
  have ht : (x.j%q+(x.t-x.j)%q)%q=x.t%q := by
    rw [← Nat.add_mod,show x.j+(x.t-x.j)=x.t by omega]
  let v : Three := ⟨x.j%q,x.e%q,(x.t-x.j)%q⟩
  refine ⟨v,choices_mem q v (Nat.mod_lt _ h.1) (Nat.mod_lt _ h.1)
    (Nat.mod_lt _ h.1),?_,rfl⟩
  cases x
  simp only [v,extend,phaseOf,Layout.map]
  rw [ht,hk,hf]

/-- Enumerate every anchored target formula, not its possible exponents. -/
def targets (q n : Nat) : List (Nat×Three) :=
  (List.range (n+1)).flatMap fun p=>(choices q).map fun v=>(p,v)

theorem targets_length (q n : Nat) : (targets q n).length=(n+1)*q^3 := by
  unfold targets
  rw [flat_length _ _ (q^3)]
  · rw [List.length_range]
  · intro p
    rw [List.length_map,choices_length]

theorem target_complete [DecidableEq α] (P : SevenDFA α) (s : Nat→α)
    (n q p : Nat) (h : LeastPeriod s n q) (post : Word α) (x : Layout Nat)
    (hw : Witness P s n p post x) (hlong : q≤x.e-p) :
    ∃ v,(p,v)∈targets q n ∧
      decideFormula (projection P s n q p v.rho post (extend q p v))
        [Int.ofNat ((x.t-x.j)/q)]=true := by
  obtain ⟨v,hv,he,hr⟩ := phase_family P s n q p h post x hw hlong
  have hp : p≤n := by
    rcases hw with ⟨h1,h2,h3,h4,h5,h6,_⟩
    omega
  refine ⟨v,List.mem_flatMap.mpr ⟨p,List.mem_range.mpr (by omega),
    List.mem_map.mpr ⟨v,hv,rfl⟩⟩,?_⟩
  rw [he,hr]
  exact projection_complete P s n q p h post x hw

open REWB.RunGeometry

theorem cubic_anchor_budget (R : Bounds) (hc : 3*R.period≤R.hi-R.lo) :
    R.hi-R.lo+1≤3*RunBudget.mass R := by
  unfold RunBudget.mass
  omega

def allTargets : List Bounds→List (Bounds×(Nat×Three))
  | [] => []
  | R::Rs => (targets R.period (R.hi-R.lo)).map (R,·)++allTargets Rs

theorem allTargets_bound (Q : Nat) (Rs : List Bounds)
    (h : ∀ R,R∈Rs→R.period≤Q ∧ 3*R.period≤R.hi-R.lo) :
    (allTargets Rs).length≤3*Q^3*RunBudget.totalMass Rs := by
  have pow_le : ∀ a b k : Nat,a≤b→a^k≤b^k := by
    intro a b k hab
    induction k with
    | zero => exact Nat.le_refl _
    | succ k ih =>
      rw [Nat.pow_succ,Nat.pow_succ]
      exact Nat.mul_le_mul ih hab
  induction Rs with
  | nil => simp [allTargets,RunBudget.totalMass]
  | cons R Rs ih =>
    obtain ⟨hq,hc⟩ := h R (by simp)
    have hr := Nat.mul_le_mul (cubic_anchor_budget R hc) (pow_le _ _ 3 hq)
    have hs := ih (fun S hS=>h S (by simp [hS]))
    simp only [allTargets,List.length_append,List.length_map,targets_length,
      RunBudget.totalMass,Nat.mul_add]
    have he : (3*RunBudget.mass R)*Q^3=3*Q^3*RunBudget.mass R := by ac_rfl
    rw [he] at hr
    exact Nat.add_le_add hr hs

theorem concrete_target_bound [DecidableEq α] (f : Nat→α) (n Q : Nat) :
    (allTargets (SmallPeriodRuns.cubic f n Q)).length≤
      3*Q^3*(2*n*DyadicIndex.heightFor n) := by
  have h := allTargets_bound Q (SmallPeriodRuns.cubic f n Q)
    (fun R hR=>((SmallPeriodRuns.cubic_mem f n Q R).mp hR).2)
  have hm := RunBudget.totalMass_bound f n _ (SmallPeriodRuns.cubic_nodup f n Q)
    (fun R hR=>((SmallPeriodRuns.cubic_mem f n Q R).mp hR).1)
  exact Nat.le_trans h (Nat.mul_le_mul_left _ hm)

end REWB.P1PhaseFamily
