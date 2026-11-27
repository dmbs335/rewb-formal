import REWB.CountedProjection
import REWB.ActualModulusCalls

/-! Exact LCM-call observations of the projection implementation.
`multiplier` and `commonPeriod` record each operand pair after the
recursive tail has produced its value. The enclosing observations follow
the actual normalization, projection, and depth-first search definitions.
They are proof observations, not extra runtime traversals.

Literal erasure preserves the complete eager projection trace and the
unpruned depth-first trace. Actual short-circuit search can select fewer
calls according to literal values; its observed calls are contained in
the unpruned trace. No enclosing machine execution is postulated here. -/
namespace REWB.ProjectionModulus.Calls
open REWB.AffineProjection REWB.UniformProjection

abbrev Call := ActualModulus.Calls.Call
abbrev Observation := ActualModulus.Calls.Observation

def multiplier : Conj → Observation
  | [] => ⟨1,[]⟩
  | a::as =>
    let tail := multiplier as
    ⟨Nat.lcm a.factor tail.value,tail.calls++[(a.factor,tail.value)]⟩

theorem multiplier_value (C : Conj) :
    (multiplier C).value=(CountedProjection.multiplier C).1 := by
  induction C with
  | nil => rfl
  | cons a as ih =>
    simp only [multiplier,CountedProjection.multiplier,CountedProjection.factor_value,ih]

theorem multiplier_cons_calls (a : Atom) (C : Conj) :
    (multiplier (a::C)).calls=(multiplier C).calls++
      [((CountedProjection.factor a).1,(CountedProjection.multiplier C).1)] := by
  simp only [multiplier,CountedProjection.factor_value,multiplier_value]

theorem multiplier_erase (C : Conj) : multiplier C=multiplier (LiteralShape.conj C) := by
  induction C with
  | nil => rfl
  | cons a as ih =>
    change (⟨Nat.lcm a.factor (multiplier as).value,
      (multiplier as).calls++[(a.factor,(multiplier as).value)]⟩ : Observation)=
      ⟨Nat.lcm (LiteralShape.atom a).factor (multiplier (LiteralShape.conj as)).value,
      (multiplier (LiteralShape.conj as)).calls++
        [((LiteralShape.atom a).factor,(multiplier (LiteralShape.conj as)).value)]⟩
    rw [LiteralShape.factor_atom,ih]

theorem multiplier_length (C : Conj) : (multiplier C).calls.length=C.length := by
  induction C with
  | nil => rfl
  | cons a as ih => simp only [multiplier,List.length_append,List.length_cons,List.length_nil,ih]

theorem multiplier_length_le (C : Conj) :
    (multiplier C).calls.length≤(CountedProjection.multiplier C).2 := by
  rw [multiplier_length]
  induction C with
  | nil => decide
  | cons a as ih => simp only [List.length_cons,CountedProjection.multiplier]; omega

def commonPeriod : List Guard → Observation
  | [] => ⟨1,[]⟩
  | g::gs =>
    let tail := commonPeriod gs
    ⟨Nat.lcm g.modulus tail.value,tail.calls++[(g.modulus,tail.value)]⟩

theorem commonPeriod_value (gs : List Guard) :
    (commonPeriod gs).value=(CountedProjection.commonPeriod gs).1 := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp only [commonPeriod,CountedProjection.commonPeriod,ih]

theorem commonPeriod_cons_calls (g : Guard) (gs : List Guard) :
    (commonPeriod (g::gs)).calls=(commonPeriod gs).calls++
      [(g.modulus,(CountedProjection.commonPeriod gs).1)] := by
  simp only [commonPeriod,commonPeriod_value]

theorem commonPeriod_erase (gs : List Guard) :
    commonPeriod gs=commonPeriod (gs.map LiteralShape.guard) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons,commonPeriod,LiteralShape.guard,ih]

theorem commonPeriod_length (gs : List Guard) : (commonPeriod gs).calls.length=gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp only [commonPeriod,List.length_append,List.length_cons,List.length_nil,ih]

theorem commonPeriod_length_le (gs : List Guard) :
    (commonPeriod gs).calls.length≤(CountedProjection.commonPeriod gs).2 := by
  rw [commonPeriod_length,CountedProjection.commonPeriod_steps]
  omega

def eliminateConj (C : Conj) : List Call :=
  (multiplier C).calls++(commonPeriod (CountedProjection.normalize C).1.guards).calls

theorem eliminateConj_erase (C : Conj) :
    eliminateConj C=eliminateConj (LiteralShape.conj C) := by
  simp only [eliminateConj,CountedProjection.normalize_value]
  rw [←LiteralShape.norm_normalize]
  change (multiplier C).calls++(commonPeriod (AffineProjection.normalize C).guards).calls=
    (multiplier (LiteralShape.conj C)).calls++
      (commonPeriod ((AffineProjection.normalize C).guards.map LiteralShape.guard)).calls
  rw [multiplier_erase,commonPeriod_erase]

theorem eliminateConj_length_le (C : Conj) :
    (eliminateConj C).length≤(CountedProjection.eliminateConj C).2 := by
  have hm := multiplier_length_le C
  have hg := commonPeriod_length_le (CountedProjection.normalize C).1.guards
  have hn : (CountedProjection.multiplier C).2≤(CountedProjection.normalize C).2 := by
    simp only [CountedProjection.normalize]
    omega
  simp only [eliminateConj,List.length_append,CountedProjection.eliminateConj]
  omega

def formula : Formula → List Call
  | [] => []
  | C::Cs => eliminateConj C++formula Cs

theorem formula_erase (F : Formula) : formula F=formula (LiteralShape.formula F) := by
  induction F with
  | nil => rfl
  | cons C Cs ih =>
    change eliminateConj C++formula Cs=
      eliminateConj (LiteralShape.conj C)++formula (LiteralShape.formula Cs)
    rw [eliminateConj_erase,ih]

theorem formula_length_le (F : Formula) :
    (formula F).length≤(CountedProjection.eliminateFormula F).2 := by
  induction F with
  | nil => decide
  | cons C Cs ih =>
    have hc := eliminateConj_length_le C
    change (eliminateConj C++formula Cs).length≤
      (CountedProjection.eliminateConj C).2+(CountedProjection.eliminateFormula Cs).2+
        (CountedProjection.append (CountedProjection.eliminateConj C).1
          (CountedProjection.eliminateFormula Cs).1).2+1
    rw [List.length_append]
    omega

def project : Nat → Formula → List Call
  | 0,_ => []
  | k+1,F => project k F++formula (CountedProjection.project k F).1

theorem project_shape (k : Nat) (F G : Formula)
    (h : LiteralShape.formula F=LiteralShape.formula G) : project k F=project k G := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [project,CountedProjection.project_value]
    rw [ih,formula_erase (AffineProjection.project k F),
      formula_erase (AffineProjection.project k G),LiteralShape.project_shape k F G h]

theorem erased_idempotent (F : Formula) :
    LiteralShape.formula (LiteralShape.formula F)=LiteralShape.formula F := by
  simp only [LiteralShape.formula,LiteralShape.conj,List.map_map,Function.comp_def,
    LiteralShape.atom_idem]
  rfl

theorem project_erase (k : Nat) (F : Formula) :
    project k F=project k (LiteralShape.formula F) :=
  project_shape k F (LiteralShape.formula F) (erased_idempotent F).symm

theorem project_length_le (k : Nat) (F : Formula) :
    (project k F).length≤(CountedProjection.project k F).2 := by
  induction k with
  | zero => simp [project,CountedProjection.project]
  | succ k ih =>
    have hf := formula_length_le (CountedProjection.project k F).1
    simp only [project,List.length_append,CountedProjection.project]
    omega

/-- Unpruned depth-first observation, used only to bound all possible
short-circuit runs of this fixed formula shape. -/
def searchAll : Nat → Formula → List Call
  | 0,_ => []
  | _+1,[] => []
  | k+1,C::Cs => eliminateConj C++searchAll k (CountedProjection.eliminateConj C).1++
      searchAll (k+1) Cs
termination_by k F => (k,F.length)

theorem searchAll_erase (k : Nat) (F : Formula) :
    searchAll k F=searchAll k (LiteralShape.formula F) := by
  induction k generalizing F with
  | zero => simp only [searchAll]
  | succ k ih =>
    induction F with
    | nil => rfl
    | cons C Cs ih' =>
      change searchAll (k+1) (C::Cs)=
        searchAll (k+1) (LiteralShape.conj C::LiteralShape.formula Cs)
      rw [searchAll,searchAll]
      rw [eliminateConj_erase,ih',CountedProjection.eliminateConj_value,
        CountedProjection.eliminateConj_value,ih (AffineProjection.eliminateConj C),
        ih (AffineProjection.eliminateConj (LiteralShape.conj C)),LiteralShape.eliminateConj_shape]

theorem searchAll_shape (k : Nat) (F G : Formula)
    (h : LiteralShape.formula F=LiteralShape.formula G) : searchAll k F=searchAll k G := by
  rw [searchAll_erase k F,searchAll_erase k G,h]

def search (env : List Int) : Nat → Formula → List Call
  | 0,_ => []
  | _+1,[] => []
  | k+1,C::Cs =>
    let E := (CountedProjection.eliminateConj C).1
    let head := eliminateConj C++search env k E
    if (CountedProjection.search env k E).1 then head
    else head++search env (k+1) Cs
termination_by k F => (k,F.length)

theorem search_subset (env : List Int) (k : Nat) (F : Formula) :
    ∀ call,call∈search env k F→call∈searchAll k F := by
  induction k generalizing F with
  | zero => simp [search]
  | succ k ih =>
    induction F with
    | nil => simp [search]
    | cons C Cs ih' =>
      intro call hc
      have he := ih (CountedProjection.eliminateConj C).1 call
      simp only [search] at hc
      rw [searchAll]
      simp only [List.mem_append]
      split at hc
      · rcases List.mem_append.mp hc with hc|hc
        · exact Or.inl (Or.inl hc)
        · exact Or.inl (Or.inr (he hc))
      · rcases List.mem_append.mp hc with hc|hc
        · rcases List.mem_append.mp hc with hc|hc
          · exact Or.inl (Or.inl hc)
          · exact Or.inl (Or.inr (he hc))
        · exact Or.inr (ih' call hc)

theorem search_length_le (env : List Int) (k : Nat) (F : Formula) :
    (search env k F).length≤(CountedProjection.search env k F).2 := by
  induction k generalizing F with
  | zero => simp only [search,List.length_nil]; exact Nat.zero_le _
  | succ k ih =>
    induction F with
    | nil => simp [search,CountedProjection.search]
    | cons C Cs ih' =>
      have he := eliminateConj_length_le C
      have hh := ih (CountedProjection.eliminateConj C).1
      rw [search,CountedProjection.search]
      split <;> simp only [List.length_append] <;> omega

/-- A finite, explicit bound for every operand appearing in a trace. -/
def operandCap : List Call → Nat
  | [] => 1
  | pair::rest => max (max pair.1 pair.2) (operandCap rest)

theorem operandCap_positive (calls : List Call) : 0<operandCap calls := by
  induction calls with
  | nil => decide
  | cons pair rest ih => exact Nat.lt_of_lt_of_le ih (Nat.le_max_right _ _)

theorem operands_le (calls : List Call) (pair : Call) (hp : pair∈calls) :
    pair.1≤operandCap calls ∧ pair.2≤operandCap calls := by
  induction calls with
  | nil => simp at hp
  | cons head rest ih =>
    rcases List.mem_cons.mp hp with rfl|hp
    · exact ⟨Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _),
        Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)⟩
    · have h := ih hp
      exact ⟨Nat.le_trans h.1 (Nat.le_max_right _ _),
        Nat.le_trans h.2 (Nat.le_max_right _ _)⟩

/-- Both traversal orders use one cap selected from the fixed finite
shape family, before any numeric text literals are selected. -/
def familyCap (k : Nat) : Family → Nat
  | [] => 1
  | F::fs => max (max (operandCap (project k F)) (operandCap (searchAll k F))) (familyCap k fs)

theorem familyCap_positive (k : Nat) (fs : Family) : 0<familyCap k fs := by
  induction fs with
  | nil => simp [familyCap]
  | cons F fs ih => exact Nat.lt_of_lt_of_le ih (Nat.le_max_right _ _)

theorem member_familyCap (k : Nat) (fs : Family) (F : Formula) (h : F∈fs) :
    operandCap (project k F)≤familyCap k fs ∧
      operandCap (searchAll k F)≤familyCap k fs := by
  induction fs with
  | nil => simp at h
  | cons G gs ih =>
    rcases List.mem_cons.mp h with rfl|h
    · exact ⟨Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _),
        Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)⟩
    · have hh := ih h
      exact ⟨Nat.le_trans hh.1 (Nat.le_max_right _ _),
        Nat.le_trans hh.2 (Nat.le_max_right _ _)⟩

theorem project_operands (k : Nat) (F : Formula) (fs : Family) (h : Covered F fs)
    (pair : Call) (hp : pair∈project k F) :
    pair.1≤familyCap k fs ∧ pair.2≤familyCap k fs := by
  have hb := (member_familyCap k fs (LiteralShape.formula F) h).1
  rw [←project_erase] at hb
  have hh := operands_le _ pair hp
  exact ⟨Nat.le_trans hh.1 hb,Nat.le_trans hh.2 hb⟩

theorem search_operands (env : List Int) (k : Nat) (F : Formula) (fs : Family)
    (h : Covered F fs) (pair : Call) (hp : pair∈search env k F) :
    pair.1≤familyCap k fs ∧ pair.2≤familyCap k fs := by
  have hb := (member_familyCap k fs (LiteralShape.formula F) h).2
  rw [←searchAll_erase] at hb
  have hh := operands_le _ pair (search_subset env k F pair hp)
  exact ⟨Nat.le_trans hh.1 hb,Nat.le_trans hh.2 hb⟩

end REWB.ProjectionModulus.Calls
