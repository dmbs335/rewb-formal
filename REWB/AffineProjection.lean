import REWB.IntegerProjection

/-! Symbolic finite disjunction of conjunctions of affine inequalities
    and divisibility constraints. The normalized system eliminates one
    variable without examining the values of the remaining variables. -/
namespace REWB.AffineProjection
open REWB.IntegerProjection

inductive Aff where
  | lit : Int → Aff
  | var : Nat → Aff
  | add : Aff → Aff → Aff
  | scale : Int → Aff → Aff
  deriving Repr

def Aff.eval (env : List Int) : Aff→Int
  | .lit c => c
  | .var i => env[i]?.getD 0
  | .add a b => a.eval env+b.eval env
  | .scale k a => k*a.eval env

def Aff.sub (a b : Aff) : Aff := .add a (.scale (-1) b)

theorem Aff.eval_sub (a b : Aff) (env : List Int) :
    (a.sub b).eval env=a.eval env-b.eval env := by
  simp [Aff.sub,Aff.eval,Int.sub_eq_add_neg]

/-- Separate the first variable, shifting all remaining variable indices. -/
def Aff.split : Aff→Int × Aff
  | .lit c => (0,.lit c)
  | .var 0 => (1,.lit 0)
  | .var (i+1) => (0,.var i)
  | .add a b =>
    let x := a.split
    let y := b.split
    (x.1+y.1,.add x.2 y.2)
  | .scale k a =>
    let x := a.split
    (k*x.1,.scale k x.2)

theorem Aff.split_eval (a : Aff) (env : List Int) (x : Int) :
    a.eval (x::env)=a.split.1*x+a.split.2.eval env := by
  induction a with
  | lit c => simp [Aff.split,Aff.eval]
  | var i => cases i <;> simp [Aff.split,Aff.eval]
  | add a b ha hb =>
    simp only [Aff.eval,Aff.split,ha,hb,Int.add_mul]
    omega
  | scale k a ha =>
    simp only [Aff.eval,Aff.split,ha,Int.mul_add,Int.mul_assoc]

inductive Atom where
  | le : Aff → Atom
  | dvd : Nat → Aff → Atom
  deriving Repr

def Atom.holds (env : List Int) : Atom→Prop
  | .le a => a.eval env≤0
  | .dvd m a => (m:Int)∣a.eval env

abbrev Conj := List Atom
abbrev Formula := List Conj

def Holds (C : Conj) (env : List Int) : Prop :=
  ∀ a,a∈C→a.holds env

def Satisfies (F : Formula) (env : List Int) : Prop :=
  ∃ C,C∈F ∧ Holds C env

theorem holds_append (A B : Conj) (env : List Int) :
    Holds (A++B) env ↔ Holds A env ∧ Holds B env := by
  constructor
  · intro h
    exact ⟨fun a ha=>h a (List.mem_append.mpr (Or.inl ha)),
      fun a ha=>h a (List.mem_append.mpr (Or.inr ha))⟩
  · rintro ⟨ha,hb⟩ a hm
    exact (List.mem_append.mp hm).elim (ha a) (hb a)

structure Guard where
  modulus : Nat
  coeff : Int
  rest : Aff
  deriving Repr

def Guard.holds (env : List Int) (y : Int) (g : Guard) : Prop :=
  (g.modulus:Int)∣g.coeff*y+g.rest.eval env

def Guard.substitute (g : Guard) (c : Aff) : Atom :=
  .dvd g.modulus (.add (.scale g.coeff c) g.rest)

theorem Guard.substitute_correct (g : Guard) (c : Aff) (env : List Int) :
    (g.substitute c).holds env ↔ g.holds env (c.eval env) := Iff.rfl

structure Norm where
  lower : List Aff
  upper : List Aff
  free : Conj
  guards : List Guard
  deriving Repr

def Norm.guardHolds (N : Norm) (env : List Int) (y : Int) : Prop :=
  ∀ g,g∈N.guards→g.holds env y

def Norm.bounds (N : Norm) (env : List Int) (y : Int) : Prop :=
  Above (N.lower.map (Aff.eval env)) y ∧ Below (N.upper.map (Aff.eval env)) y

def Norm.holds (N : Norm) (env : List Int) (y : Int) : Prop :=
  Holds N.free env ∧ N.bounds env y ∧ N.guardHolds env y

theorem Norm.guard_period (N : Norm) (env : List Int) (K : Nat)
    (hK : ∀ g,g∈N.guards→g.modulus∣K) :
    ShiftInvariant (K:Int) (N.guardHolds env) := by
  intro x z
  constructor
  · intro h g hg
    obtain ⟨k,hk⟩ := hK g hg
    have hd : (g.modulus:Int)∣(K:Int) := by
      refine ⟨(k:Int),?_⟩
      rw [hk,Int.ofNat_mul]
    exact (dvd_guard _ _ _ _ hd x z).mp (h g hg)
  · intro h g hg
    obtain ⟨k,hk⟩ := hK g hg
    have hd : (g.modulus:Int)∣(K:Int) := by
      refine ⟨(k:Int),?_⟩
      rw [hk,Int.ofNat_mul]
    exact (dvd_guard _ _ _ _ hd x z).mpr (h g hg)

/-- Build affine candidates rather than evaluating the bounds. -/
def Norm.candidates (N : Norm) (K : Nat) : List Aff :=
  if N.lower.isEmpty then (List.range K).map (fun r=>Aff.lit (r:Int))
  else N.lower.flatMap (fun l=>(List.range K).map (fun r=>Aff.add l (.lit (r:Int))))

theorem Norm.candidates_eval (N : Norm) (K : Nat) (env : List Int) :
    (N.candidates K).map (Aff.eval env)=
      IntegerProjection.candidates (N.lower.map (Aff.eval env)) K := by
  unfold Norm.candidates IntegerProjection.candidates
  cases h : N.lower with
  | nil => simp [h,Aff.eval,List.map_map,Function.comp_def]
  | cons l ls =>
    simp only [h,List.isEmpty_cons,if_false,List.map_cons]
    have he : ∀ xs : List Aff,
        (xs.flatMap (fun l=>(List.range K).map (fun r=>Aff.add l (.lit (r:Int))))).map (Aff.eval env)=
          (xs.map (Aff.eval env)).flatMap (fun l=>(List.range K).map (fun r=>l+(r:Int))) := by
      intro xs
      induction xs with
      | nil => rfl
      | cons x xs ih =>
        simp only [List.flatMap_cons,List.map_append,ih,List.map_cons,List.map_map,Function.comp_def,Aff.eval]
    exact he (l::ls)

def Norm.substitute (N : Norm) (c : Aff) : Conj :=
  N.free ++
    (if N.lower.isEmpty then [] else
      N.lower.map (fun l=>Atom.le (l.sub c)) ++
      N.upper.map (fun u=>Atom.le (c.sub u))) ++
    N.guards.map (fun g=>g.substitute c)

theorem holds_map {X : Type} (xs : List X) (f : X→Atom) (env : List Int) :
    Holds (xs.map f) env ↔ ∀ x,x∈xs→(f x).holds env := by
  constructor
  · intro h x hx
    exact h _ (List.mem_map.mpr ⟨x,hx,rfl⟩)
  · intro h a ha
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha
    exact h x hx

theorem lower_map (xs : List Aff) (env : List Int) (c : Aff) :
    Holds (xs.map (fun l=>Atom.le (l.sub c))) env ↔
      Above (xs.map (Aff.eval env)) (c.eval env) := by
  rw [holds_map]
  constructor
  · intro h l hl
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hl
    have hh := h a ha
    change (a.sub c).eval env≤0 at hh
    rw [Aff.eval_sub] at hh
    omega
  · intro h a ha
    have hh := h _ (List.mem_map.mpr ⟨a,ha,rfl⟩)
    change (a.sub c).eval env≤0
    rw [Aff.eval_sub]
    omega

theorem upper_map (xs : List Aff) (env : List Int) (c : Aff) :
    Holds (xs.map (fun u=>Atom.le (c.sub u))) env ↔
      Below (xs.map (Aff.eval env)) (c.eval env) := by
  rw [holds_map]
  constructor
  · intro h u hu
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hu
    have hh := h a ha
    change (c.sub a).eval env≤0 at hh
    rw [Aff.eval_sub] at hh
    omega
  · intro h a ha
    have hh := h _ (List.mem_map.mpr ⟨a,ha,rfl⟩)
    change (c.sub a).eval env≤0
    rw [Aff.eval_sub]
    omega

theorem Norm.substitute_correct (N : Norm) (c : Aff) (env : List Int) :
    Holds (N.substitute c) env ↔ Holds N.free env ∧
      (if N.lower.isEmpty then N.guardHolds env (c.eval env)
       else feasible (N.lower.map (Aff.eval env)) (N.upper.map (Aff.eval env))
          (N.guardHolds env) (c.eval env)) := by
  unfold Norm.substitute
  rw [holds_append,holds_append,holds_map]
  simp only [Guard.substitute_correct]
  cases h : N.lower with
  | nil => simp [h,Holds,Norm.guardHolds]
  | cons l ls =>
    simp only [h,List.isEmpty_cons,if_false,holds_append,lower_map,upper_map,feasible,Norm.guardHolds]
    constructor
    · rintro ⟨⟨hf,hl,hu⟩,hg⟩
      exact ⟨hf,hl,hu,hg⟩
    · rintro ⟨hf,hl,hu,hg⟩
      exact ⟨⟨hf,hl,hu⟩,hg⟩

def Norm.eliminate (N : Norm) (K : Nat) : Formula :=
  (N.candidates K).map N.substitute

/-- Symbolic one-variable elimination. A conjunction over y and its
    remaining variables is exactly a finite DNF over the latter alone. -/
theorem Norm.eliminate_correct (N : Norm) (K : Nat) (env : List Int)
    (hK : 0<K) (hd : ∀ g,g∈N.guards→g.modulus∣K) :
    (∃ y,N.holds env y) ↔ Satisfies (N.eliminate K) env := by
  let lo := N.lower.map (Aff.eval env)
  let hi := N.upper.map (Aff.eval env)
  have h := finite_elimination lo hi K hK (N.guardHolds env) (N.guard_period env K hd)
  have hempty : lo.isEmpty=N.lower.isEmpty := by simp [lo]
  rw [hempty,← N.candidates_eval K env] at h
  unfold Satisfies Norm.eliminate
  constructor
  · rintro ⟨y,hf,⟨hl,hu⟩,hg⟩
    obtain ⟨c,hc,hvalid⟩ := h.mp ⟨y,hl,hu,hg⟩
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hc
    exact ⟨N.substitute a,List.mem_map.mpr ⟨a,ha,rfl⟩,
      (N.substitute_correct a env).mpr ⟨hf,hvalid⟩⟩
  · rintro ⟨C,hC,hholds⟩
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hC
    obtain ⟨hf,hvalid⟩ := (N.substitute_correct a env).mp hholds
    obtain ⟨y,hl,hu,hg⟩ := h.mpr ⟨a.eval env,List.mem_map.mpr ⟨a,ha,rfl⟩,hvalid⟩
    exact ⟨y,hf,⟨hl,hu⟩,hg⟩

theorem Norm.eliminate_length (N : Norm) (K : Nat) :
    (N.eliminate K).length=(max 1 N.lower.length)*K := by
  have h := congrArg List.length (N.candidates_eval K [])
  rw [List.length_map,candidates_length,List.length_map] at h
  unfold Norm.eliminate
  rw [List.length_map]
  exact h

end REWB.AffineProjection
