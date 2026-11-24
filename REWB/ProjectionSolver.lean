import REWB.Cooper

/-! Repeated elimination on DNF formulas. This implements existential
    projection, leaving any suffix of the input coordinate vector free.
    The resulting formula is still a finite DNF of affine inequalities
    and positive-modulus divisibility atoms. -/
namespace REWB.AffineProjection

theorem Good_append (A B : Conj) : Good (A++B) ↔ Good A ∧ Good B := by
  constructor
  · intro h
    exact ⟨fun a ha=>h a (List.mem_append.mpr (Or.inl ha)),
      fun a ha=>h a (List.mem_append.mpr (Or.inr ha))⟩
  · rintro ⟨ha,hb⟩ a hm
    exact (List.mem_append.mp hm).elim (ha a) (hb a)

theorem normalizeAtom_free (D : Nat) (a : Atom) : Good (normalizeAtom D a).free := by
  cases a with
  | le t =>
    intro x hx
    unfold normalizeAtom at hx
    dsimp only at hx
    split at hx
    · simp only [List.mem_cons,List.mem_nil,false_or] at hx
      subst x
      trivial
    · split at hx <;> simp at hx
  | dvd m t =>
    intro x hx
    simp [normalizeAtom] at hx

theorem normalizeRows_free (D : Nat) (C : Conj) : Good (normalizeRows D C).free := by
  induction C with
  | nil => intro x hx; simp [normalizeRows,Norm.empty] at hx
  | cons a as ih =>
    change Good ((normalizeAtom D a).free++(normalizeRows D as).free)
    exact (Good_append _ _).mpr ⟨normalizeAtom_free D a,ih⟩

theorem normalize_free (C : Conj) : Good (normalize C).free := by
  unfold normalize
  change Good ((normalizeRows (multiplier C) C).free++[])
  rw [List.append_nil]
  exact normalizeRows_free _ _

theorem substitute_good (N : Norm) (c : Aff) (hf : Good N.free)
    (hg : ∀ g,g∈N.guards→0<g.modulus) : Good (N.substitute c) := by
  unfold Norm.substitute
  rw [Good_append,Good_append]
  refine ⟨⟨hf,?_⟩,?_⟩
  · split
    · intro a ha
      simp at ha
    · rw [Good_append]
      constructor
      · intro a ha
        obtain ⟨l,hl,rfl⟩ := List.mem_map.mp ha
        trivial
      · intro a ha
        obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ha
        trivial
  · intro a ha
    obtain ⟨g,hg',rfl⟩ := List.mem_map.mp ha
    exact hg g hg'

def FormulaGood (F : Formula) : Prop := ∀ C,C∈F→Good C

theorem eliminateConj_good (C : Conj) (hC : Good C) :
    FormulaGood (eliminateConj C) := by
  intro B hB
  change B∈((normalize C).candidates (commonPeriod (normalize C).guards)).map
    (normalize C).substitute at hB
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hB
  exact substitute_good (normalize C) c (normalize_free C) (normalize_moduli C hC)

def eliminateFormula (F : Formula) : Formula := F.flatMap eliminateConj

theorem eliminateFormula_good (F : Formula) (hF : FormulaGood F) :
    FormulaGood (eliminateFormula F) := by
  intro B hb
  obtain ⟨C,hC,hb'⟩ := List.mem_flatMap.mp hb
  exact eliminateConj_good C (hF C hC) B hb'

theorem eliminateFormula_correct (F : Formula) (env : List Int) (hF : FormulaGood F) :
    Satisfies (eliminateFormula F) env ↔ ∃ x,Satisfies F (x::env) := by
  constructor
  · rintro ⟨B,hB,hb⟩
    obtain ⟨C,hC,hb'⟩ := List.mem_flatMap.mp hB
    obtain ⟨x,hx⟩ := (eliminateConj_correct C env (hF C hC)).mp ⟨B,hb',hb⟩
    exact ⟨x,C,hC,hx⟩
  · rintro ⟨x,C,hC,hx⟩
    obtain ⟨B,hB,hb⟩ := (eliminateConj_correct C env (hF C hC)).mpr ⟨x,hx⟩
    exact ⟨B,List.mem_flatMap.mpr ⟨C,hC,hB⟩,hb⟩

def project : Nat→Formula→Formula
  | 0,F => F
  | k+1,F => eliminateFormula (project k F)

def ExistsPrefix : Nat→Formula→List Int→Prop
  | 0,F,env => Satisfies F env
  | k+1,F,env => ∃ x,ExistsPrefix k F (x::env)

theorem project_good (k : Nat) (F : Formula) (hF : FormulaGood F) :
    FormulaGood (project k F) := by
  induction k with
  | zero => exact hF
  | succ k ih => exact eliminateFormula_good _ ih

theorem project_correct (k : Nat) (F : Formula) (env : List Int) (hF : FormulaGood F) :
    Satisfies (project k F) env ↔ ExistsPrefix k F env := by
  induction k generalizing env with
  | zero => rfl
  | succ k ih =>
    change Satisfies (eliminateFormula (project k F)) env ↔
      ∃ x,ExistsPrefix k F (x::env)
    rw [eliminateFormula_correct _ env (project_good k F hF)]
    constructor
    · rintro ⟨x,h⟩
      exact ⟨x,(ih (x::env)).mp h⟩
    · rintro ⟨x,h⟩
      exact ⟨x,(ih (x::env)).mpr h⟩

def Atom.test (env : List Int) : Atom→Bool
  | .le a => decide (a.eval env≤0)
  | .dvd m a => decide (a.eval env%(m:Int)=0)

theorem Atom.test_correct (a : Atom) (env : List Int) (h : a.good) :
    a.test env=true ↔ a.holds env := by
  cases a with
  | le a => simp [Atom.test,Atom.holds]
  | dvd m a =>
    change (decide (a.eval env%(m:Int)=0)=true) ↔ (m:Int)∣a.eval env
    rw [decide_eq_true_eq]
    exact (Int.dvd_iff_emod_eq_zero _ _).symm

def decideFormula (F : Formula) (env : List Int) : Bool :=
  F.any (fun C=>C.all (Atom.test env))

theorem decideFormula_correct (F : Formula) (env : List Int) (hF : FormulaGood F) :
    decideFormula F env=true ↔ Satisfies F env := by
  unfold decideFormula Satisfies
  rw [List.any_eq_true]
  constructor
  · rintro ⟨C,hC,hall⟩
    refine ⟨C,hC,?_⟩
    intro a ha
    exact (a.test_correct env (hF C hC a ha)).mp (List.all_eq_true.mp hall a ha)
  · rintro ⟨C,hC,h⟩
    refine ⟨C,hC,List.all_eq_true.mpr ?_⟩
    intro a ha
    exact (a.test_correct env (hF C hC a ha)).mpr (h a ha)

/-- A projected formula is executable for every remaining free-coordinate
    assignment. With k equal to the full dimension, env is empty. -/
def solve (k : Nat) (F : Formula) (env : List Int) : Bool :=
  decideFormula (project k F) env

theorem solve_correct (k : Nat) (F : Formula) (env : List Int) (hF : FormulaGood F) :
    solve k F env=true ↔ ExistsPrefix k F env :=
  (decideFormula_correct _ _ (project_good k F hF)).trans (project_correct k F env hF)

end REWB.AffineProjection
