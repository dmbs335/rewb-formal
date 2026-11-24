import REWB.PhaseSolver

/-! Simultaneous constraints over shared affine block coordinates.
    Unlike per-factor independent searches, this constructs one formula
    and projects all existential coordinates together. -/
namespace REWB.PhaseSolver
open REWB.Periodic
open REWB.AffineProjection
variable {α : Type}

def equalFormula [DecidableEq α] (p n : Nat) (f : Nat→α)
    (a b c d : Endpoint) : Formula :=
  both (both (orderFormula p n a b) (orderFormula p n c d))
    (both (orderFormula p n a c) (equalityCore p f a b c d))

theorem equalFormula_good [DecidableEq α] (p n : Nat) (f : Nat→α)
    (a b c d : Endpoint) : FormulaGood (equalFormula p n f a b c d) := by
  exact both_good _ _
    (both_good _ _ (orderFormula_good _ _ _ _) (orderFormula_good _ _ _ _))
    (both_good _ _ (orderFormula_good _ _ _ _) (equalityCore_good _ _ _ _ _ _))

theorem equalFormula_correct [DecidableEq α] (p n : Nat) (f : Nat→α)
    (h : LeastPeriod f n p) (a b c d : Endpoint) (env : List Int) :
    Satisfies (equalFormula p n f a b c d) env ↔
      (a.valid p n env ∧ b.valid p n env ∧ a.pos p env≤b.pos p env) ∧
      (c.valid p n env ∧ d.valid p n env ∧ c.pos p env≤d.pos p env) ∧
      a.pos p env≤c.pos p env ∧
      (interval a b env).value p f=(interval c d env).value p f := by
  unfold equalFormula
  simp only [both_correct,orderFormula_correct _ _ _ _ _ h.1]
  constructor
  · rintro ⟨⟨⟨ha,hb,hab⟩,⟨hc,hd,hcd⟩⟩,⟨_,_,hac⟩,he⟩
    exact ⟨⟨ha,hb,hab⟩,⟨hc,hd,hcd⟩,hac,
      (equalityCore_correct p n f h a b c d env ha hb hc hd hab hcd hac).mp he⟩
  · rintro ⟨⟨ha,hb,hab⟩,⟨hc,hd,hcd⟩,hac,he⟩
    exact ⟨⟨⟨ha,hb,hab⟩,⟨hc,hd,hcd⟩⟩,⟨ha,hc,hac⟩,
      (equalityCore_correct p n f h a b c d env ha hb hc hd hab hcd hac).mpr he⟩

inductive Constraint (α : Type) where
  | bound : Endpoint → Constraint α
  | order : Endpoint → Endpoint → Constraint α
  | regular : DFA α → Endpoint → Endpoint → Constraint α
  | equal : Endpoint → Endpoint → Endpoint → Endpoint → Constraint α

def Ordered (p n : Nat) (env : List Int) (a b : Endpoint) : Prop :=
  a.valid p n env ∧ b.valid p n env ∧ a.pos p env≤b.pos p env

def Constraint.plain (p n : Nat) (f : Nat→α) (env : List Int) : Constraint α→Prop
  | .bound a => a.valid p n env
  | .order a b => Ordered p n env a b
  | .regular d a b => Ordered p n env a b ∧ d.accepts ((interval a b env).value p f)
  | .equal a b c d =>
    Ordered p n env a b ∧ Ordered p n env c d ∧ a.pos p env≤c.pos p env ∧
      (interval a b env).value p f=(interval c d env).value p f

def Constraint.compile [DecidableEq α] (p n : Nat) (f : Nat→α) : Constraint α→Formula
  | .bound a => a.bound p n
  | .order a b => orderFormula p n a b
  | .regular d a b => regularFormula p n f d a b
  | .equal a b c d => equalFormula p n f a b c d

theorem Constraint.compile_good [DecidableEq α] (p n : Nat) (f : Nat→α)
    (h : LeastPeriod f n p) (c : Constraint α) :
    FormulaGood (c.compile p n f) := by
  cases c with
  | bound a => exact a.bound_good p n
  | order a b => exact orderFormula_good p n a b
  | regular d a b => exact regularFormula_good p n f d a b h.2.1
  | equal a b c d => exact equalFormula_good p n f a b c d

theorem Constraint.compile_correct [DecidableEq α] (p n : Nat) (f : Nat→α)
    (h : LeastPeriod f n p) (c : Constraint α) (env : List Int) :
    Satisfies (c.compile p n f) env ↔ c.plain p n f env := by
  cases c with
  | bound a => exact a.bound_correct p n env h.1
  | order a b => exact orderFormula_correct p n a b env h.1
  | regular d a b =>
    rw [Constraint.compile,regularFormula_correct p n f d a b env h.1 h.2.1]
    simp only [Constraint.plain,Ordered]
    constructor
    · rintro ⟨ha,hb,ho,hd⟩
      exact ⟨⟨ha,hb,ho⟩,hd⟩
    · rintro ⟨⟨ha,hb,ho⟩,hd⟩
      exact ⟨ha,hb,ho,hd⟩
  | equal a b c d => exact equalFormula_correct p n f h a b c d env

def compileSystem [DecidableEq α] (p n : Nat) (f : Nat→α) :
    List (Constraint α)→Formula
  | [] => [[]]
  | c::cs => both (c.compile p n f) (compileSystem p n f cs)

def Plain (p n : Nat) (f : Nat→α) (cs : List (Constraint α)) (env : List Int) : Prop :=
  ∀ c,c∈cs→c.plain p n f env

theorem compileSystem_correct [DecidableEq α] (p n : Nat) (f : Nat→α)
    (h : LeastPeriod f n p) (cs : List (Constraint α)) (env : List Int) :
    Satisfies (compileSystem p n f cs) env ↔ Plain p n f cs env := by
  induction cs with
  | nil => simp [compileSystem,Satisfies,Holds,Plain]
  | cons c cs ih =>
    rw [compileSystem,both_correct,Constraint.compile_correct p n f h c env,ih]
    constructor
    · rintro ⟨hc,ht⟩ x hx
      rcases List.mem_cons.mp hx with he|hm
      · subst x
        exact hc
      · exact ht x hm
    · intro hall
      exact ⟨hall c (by simp),fun x hx=>hall x (by simp [hx])⟩

theorem compileSystem_good [DecidableEq α] (p n : Nat) (f : Nat→α)
    (h : LeastPeriod f n p) (cs : List (Constraint α)) :
    FormulaGood (compileSystem p n f cs) := by
  induction cs with
  | nil => simp [compileSystem,FormulaGood,Good]
  | cons c cs ih =>
    exact both_good _ _ (Constraint.compile_good p n f h c) ih

/-- Quantify the initial k block coordinates, retaining the remaining
    free coordinates. The variables in every factor stay synchronized. -/
def Quantify (P : List Int→Prop) : Nat→List Int→Prop
  | 0,env => P env
  | k+1,env => ∃ x,Quantify P k (x::env)

theorem quantify_congr (P Q : List Int→Prop) (h : ∀ env,P env↔Q env)
    (k : Nat) (env : List Int) :
    Quantify P k env ↔ Quantify Q k env := by
  induction k generalizing env with
  | zero => exact h env
  | succ k ih =>
    constructor
    · rintro ⟨x,hx⟩
      exact ⟨x,(ih (x::env)).mp hx⟩
    · rintro ⟨x,hx⟩
      exact ⟨x,(ih (x::env)).mpr hx⟩

theorem prefix_quantify (F : Formula) (k : Nat) (env : List Int) :
    ExistsPrefix k F env ↔ Quantify (Satisfies F) k env := by
  induction k generalizing env with
  | zero => rfl
  | succ k ih =>
    constructor
    · rintro ⟨x,hx⟩
      exact ⟨x,(ih (x::env)).mp hx⟩
    · rintro ⟨x,hx⟩
      exact ⟨x,(ih (x::env)).mpr hx⟩

theorem quantify_env (P : List Int→Prop) (k : Nat) (env : List Int) :
    Quantify P k env ↔ ∃ xs : List Int,xs.length=k ∧ P (xs++env) := by
  induction k generalizing env with
  | zero =>
    constructor
    · intro h
      exact ⟨[],rfl,h⟩
    · rintro ⟨xs,hxs,h⟩
      cases xs with
      | nil => exact h
      | cons x xs => simp at hxs
  | succ k ih =>
    constructor
    · rintro ⟨x,hx⟩
      obtain ⟨ys,hy,h⟩ := (ih (x::env)).mp hx
      exact ⟨ys++[x],by simp [hy],by simpa only [List.append_assoc,List.singleton_append] using h⟩
    · rintro ⟨xs,hxs,h⟩
      have hne : xs≠[] := by intro he; simp [he] at hxs
      have hsplit : xs=xs.dropLast++[xs.getLast hne] :=
        (List.dropLast_append_getLast hne).symm
      have hlen : xs.dropLast.length=k := by rw [List.length_dropLast,hxs]; omega
      refine ⟨xs.getLast hne,(ih _).mpr ⟨xs.dropLast,hlen,?_⟩⟩
      rw [hsplit,List.append_assoc,List.singleton_append] at h
      exact h

def solveSystem [DecidableEq α] (p n : Nat) (f : Nat→α)
    (cs : List (Constraint α)) (k : Nat) (env : List Int) : Bool :=
  solve k (compileSystem p n f cs) env

theorem solveSystem_correct [DecidableEq α] (p n : Nat) (f : Nat→α)
    (h : LeastPeriod f n p) (cs : List (Constraint α)) (k : Nat) (env : List Int) :
    solveSystem p n f cs k env=true ↔
      ∃ xs : List Int,xs.length=k ∧ Plain p n f cs (xs++env) := by
  unfold solveSystem
  rw [solve_correct _ _ _ (compileSystem_good p n f h cs),prefix_quantify]
  exact (quantify_congr _ _ (compileSystem_correct p n f h cs) k env).trans
    (quantify_env _ k env)

end REWB.PhaseSolver
