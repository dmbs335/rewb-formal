import REWB.ExponentIntervals
import REWB.LiteralShape

/-! Finite families of erased formulas give uniform projection bounds.
    The families are proof witnesses determined by a fixed pattern; the
    matching algorithm does not enumerate them on each text. In particular,
    constants in interval endpoints do not affect the common modulus. -/
namespace REWB.UniformProjection
open REWB.AffineProjection REWB.PhaseSolver

abbrev Family := List Formula

def Covered (F : Formula) (fs : Family) : Prop := LiteralShape.formula F ∈ fs

def combine (fs gs : Family) : Family :=
  fs.flatMap fun F => gs.map fun G => both F G

theorem erase_both (F G : Formula) :
    LiteralShape.formula (both F G)=both (LiteralShape.formula F) (LiteralShape.formula G) := by
  simp only [both,LiteralShape.formula,List.map_flatMap,List.flatMap_map,List.map_map,
    Function.comp_def,LiteralShape.conj_append]

theorem covered_both (F G : Formula) (fs gs : Family)
    (hF : Covered F fs) (hG : Covered G gs) :
    Covered (both F G) (combine fs gs) := by
  unfold Covered
  rw [erase_both]
  exact List.mem_flatMap.mpr ⟨LiteralShape.formula F,hF,
    List.mem_map.mpr ⟨LiteralShape.formula G,hG,rfl⟩⟩

theorem covered_empty (fs : Family) (h : []∈fs) : Covered [] fs := h

theorem erase_le (a b : Aff) : LiteralShape.formula (le a b)=le (LiteralShape.aff a) (LiteralShape.aff b) := rfl

theorem erase_eq (a b : Aff) : LiteralShape.formula (eq a b)=eq (LiteralShape.aff a) (LiteralShape.aff b) := by
  rw [eq,erase_both,erase_le,erase_le]
  rfl

def countShape (a b : Aff) : Aff := (b.sub a).sub (.lit 0)

theorem erase_count (a b : Endpoint) :
    LiteralShape.aff (countExpr a b)=countShape (LiteralShape.aff a.1) (LiteralShape.aff b.1) := rfl

def bounds (a : Aff) : Family :=
  [[],both (le (.lit 0) a) (le a (.lit 0))]

theorem covered_bound (q n : Nat) (a : Endpoint) :
    Covered (a.bound q n) (bounds (LiteralShape.aff a.1)) := by
  unfold Endpoint.bound
  split
  · unfold Covered
    rw [erase_both,erase_le,erase_le]
    simp only [LiteralShape.aff]
    exact List.mem_cons.mpr (Or.inr (List.mem_cons_self))
  · exact List.mem_cons_self

def orders (a b : Aff) : Family :=
  combine (combine (bounds a) (bounds b)) [le (.lit 0) (countShape a b)]

theorem covered_order (q n : Nat) (a b : Endpoint) :
    Covered (orderFormula q n a b) (orders (LiteralShape.aff a.1) (LiteralShape.aff b.1)) := by
  apply covered_both
  · exact covered_both _ _ _ _ (covered_bound q n a) (covered_bound q n b)
  · unfold Covered
    rw [erase_le,erase_count]
    exact List.mem_cons_self

def descriptors (S : Nat) (t : Aff) : Family :=
  (List.range (S+1)).flatMap fun i =>
    (List.range (S+1)).flatMap fun j =>
      (List.range (S+1)).map fun m =>
        List.replicate i (exactCount t 0) ++ List.replicate j (progression t 0 m)

theorem erase_exact (t : Aff) (v : Nat) :
    LiteralShape.conj (exactCount t v)=exactCount (LiteralShape.aff t) 0 := rfl

theorem erase_progression (t : Aff) (v m : Nat) :
    LiteralShape.conj (progression t v m)=progression (LiteralShape.aff t) 0 m := rfl

theorem erase_descriptor (D : FiniteOrbit.Descriptor) (t : Aff) :
    LiteralShape.formula (descriptorFormula D t)=
      List.replicate (D.initialCounts.filter (fun k=>decide (k<D.threshold))).length
        (exactCount (LiteralShape.aff t) 0) ++
      List.replicate D.residues.length (progression (LiteralShape.aff t) 0 D.period) := by
  simp only [descriptorFormula,LiteralShape.formula,List.map_append,List.map_map,
    Function.comp_def,erase_exact,erase_progression,List.map_const']

theorem covered_descriptor (D : FiniteOrbit.Descriptor) (S : Nat) (t : Aff)
    (hs : D.initialCounts.length+D.residues.length≤S) (hm : D.period≤S) :
    Covered (descriptorFormula D t) (descriptors S (LiteralShape.aff t)) := by
  have hi := List.length_filter_le (fun k=>decide (k<D.threshold)) D.initialCounts
  unfold Covered
  rw [erase_descriptor]
  refine List.mem_flatMap.mpr ⟨(D.initialCounts.filter (fun k=>decide (k<D.threshold))).length,
    List.mem_range.mpr (by omega),?_⟩
  refine List.mem_flatMap.mpr ⟨D.residues.length,List.mem_range.mpr (by omega),?_⟩
  exact List.mem_map.mpr ⟨D.period,List.mem_range.mpr (by omega),rfl⟩

theorem descriptors_empty (S : Nat) (t : Aff) : []∈descriptors S t := by
  refine List.mem_flatMap.mpr ⟨0,List.mem_range.mpr (by omega),?_⟩
  refine List.mem_flatMap.mpr ⟨0,List.mem_range.mpr (by omega),?_⟩
  exact List.mem_map.mpr ⟨0,List.mem_range.mpr (by omega),rfl⟩

def regulars (S : Nat) (a b : Aff) : Family :=
  combine (orders a b) (descriptors S (countShape a b))

theorem covered_regular {α : Type} (q n : Nat) (s : Nat→α) (d : DFA α)
    (a b : Endpoint) :
    Covered (regularFormula q n s d a b) (regulars d.stateCount (LiteralShape.aff a.1) (LiteralShape.aff b.1)) := by
  unfold regularFormula
  apply covered_both _ _ _ _ (covered_order q n a b)
  cases he : Periodic.factorDescriptor d s a.phase q (tailLen q a b) with
  | none => exact descriptors_empty _ _
  | some D =>
    have hs := FiniteOrbit.compress_size (FiniteRelation.finEnum d.stateCount)
      (fun v=>d.run v (Periodic.segment s a.phase q)) d.initial
      (fun v=>d.final (d.run v (Periodic.segment s a.phase (tailLen q a b)))) D he
    obtain ⟨E,hE,hp,hb,_⟩ := FiniteOrbit.compress_spec (FiniteRelation.finEnum d.stateCount)
      (fun v=>d.run v (Periodic.segment s a.phase q)) d.initial
      (fun v=>d.final (d.run v (Periodic.segment s a.phase (tailLen q a b))))
    change Periodic.factorDescriptor d s a.phase q (tailLen q a b)=some E at hE
    rw [he] at hE
    have hDE := Option.some.inj hE
    subst E
    have hS : D.initialCounts.length+D.residues.length≤d.stateCount := by
      simpa only [FiniteRelation.finEnum,List.length_ofFn] using hs
    have hM : D.period≤d.stateCount := by
      have hB : D.threshold+D.period≤d.stateCount := by
        simpa only [FiniteRelation.finEnum,List.length_ofFn] using hb
      omega
    have h := covered_descriptor D d.stateCount (countExpr a b) hS hM
    rwa [erase_count] at h

def equalityCores (a b c d : Aff) : Family :=
  [[],eq (countShape a b) (countShape c d),
    both (eq (countShape a b) (.lit 0)) (eq (countShape c d) (.lit 0))]

theorem covered_equalityCore {α : Type} [DecidableEq α] (q : Nat) (s : Nat→α)
    (a b c d : Endpoint) :
    Covered (equalityCore q s a b c d)
      (equalityCores (LiteralShape.aff a.1) (LiteralShape.aff b.1) (LiteralShape.aff c.1) (LiteralShape.aff d.1)) := by
  unfold equalityCore
  split
  · split
    · unfold Covered
      rw [erase_eq,erase_count,erase_count]
      exact List.mem_cons.mpr (Or.inr (List.mem_cons_self))
    · split
      · unfold Covered
        rw [erase_both,erase_eq,erase_eq,erase_count,erase_count]
        exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons_self))))
      · exact List.mem_cons_self
  · exact List.mem_cons_self

def equalities (a b c d : Aff) : Family :=
  combine (combine (orders a b) (orders c d))
    (combine (orders a c) (equalityCores a b c d))

theorem covered_equal {α : Type} [DecidableEq α] (q n : Nat) (s : Nat→α)
    (a b c d : Endpoint) :
    Covered (equalFormula q n s a b c d)
      (equalities (LiteralShape.aff a.1) (LiteralShape.aff b.1) (LiteralShape.aff c.1) (LiteralShape.aff d.1)) := by
  exact covered_both _ _ _ _
    (covered_both _ _ _ _ (covered_order q n a b) (covered_order q n c d))
    (covered_both _ _ _ _ (covered_order q n a c) (covered_equalityCore q s a b c d))

def constraintFamily {α : Type} : Constraint α→Family
  | .bound a => bounds (LiteralShape.aff a.1)
  | .order a b => orders (LiteralShape.aff a.1) (LiteralShape.aff b.1)
  | .regular d a b => regulars d.stateCount (LiteralShape.aff a.1) (LiteralShape.aff b.1)
  | .equal a b c d => equalities (LiteralShape.aff a.1) (LiteralShape.aff b.1) (LiteralShape.aff c.1) (LiteralShape.aff d.1)

theorem covered_constraint {α : Type} [DecidableEq α] (q n : Nat) (s : Nat→α)
    (c : Constraint α) : Covered (c.compile q n s) (constraintFamily c) := by
  cases c with
  | bound a => exact covered_bound q n a
  | order a b => exact covered_order q n a b
  | regular d a b => exact covered_regular q n s d a b
  | equal a b c d => exact covered_equal q n s a b c d

def systemFamily {α : Type} : List (Constraint α)→Family
  | [] => [[[]]]
  | c::cs => combine (constraintFamily c) (systemFamily cs)

theorem covered_system {α : Type} [DecidableEq α] (q n : Nat) (s : Nat→α)
    (cs : List (Constraint α)) : Covered (compileSystem q n s cs) (systemFamily cs) := by
  induction cs with
  | nil => exact List.mem_cons_self
  | cons c cs ih => exact covered_both _ _ _ _ (covered_constraint q n s c) ih

/-- Erased tree size, coefficient multipliers, variable indices and atom
    moduli are all accounted for, while numeric literals are ignored. -/
def affMeasure : Aff→Nat
  | .lit _ => 1
  | .var i => i+2
  | .add a b => affMeasure a+affMeasure b+1
  | .scale c a => (c.natAbs+1)*(affMeasure a+1)

def atomMeasure : Atom→Nat
  | .le a => affMeasure a+1
  | .dvd m a => affMeasure a+m+1

def conjMeasure : Conj→Nat
  | [] => 0
  | a::as => atomMeasure a+conjMeasure as+1

def measure : Formula→Nat
  | [] => 0
  | C::Cs => conjMeasure C+measure Cs+1

theorem affMeasure_erase (a : Aff) : affMeasure (LiteralShape.aff a)=affMeasure a := by
  induction a <;> simp_all [affMeasure,LiteralShape.aff]

theorem atomMeasure_erase (a : Atom) : atomMeasure (LiteralShape.atom a)=atomMeasure a := by
  cases a <;> simp only [atomMeasure,LiteralShape.atom,affMeasure_erase]

theorem conjMeasure_erase (C : Conj) : conjMeasure (LiteralShape.conj C)=conjMeasure C := by
  induction C with
  | nil => rfl
  | cons a as ih =>
    change atomMeasure (LiteralShape.atom a)+conjMeasure (LiteralShape.conj as)+1=_
    rw [atomMeasure_erase,ih]
    rfl

theorem measure_erase (F : Formula) : measure (LiteralShape.formula F)=measure F := by
  induction F with
  | nil => rfl
  | cons C Cs ih =>
    change conjMeasure (LiteralShape.conj C)+measure (LiteralShape.formula Cs)+1=_
    rw [conjMeasure_erase,ih]
    rfl

theorem length_le_measure (F : Formula) : F.length≤measure F := by
  induction F with
  | nil => exact Nat.le_refl _
  | cons C Cs ih =>
    change Cs.length+1≤conjMeasure C+measure Cs+1
    omega

/-- The coefficient actually used by the elimination algorithm is
    bounded as an integer, including sums and nested multiplications. -/
theorem split_coefficient_bound (a : Aff) : a.split.1.natAbs≤affMeasure a := by
  induction a with
  | lit c => simp [Aff.split,affMeasure]
  | var i => cases i <;> simp [Aff.split,affMeasure]
  | add a b ha hb =>
    change (a.split.1+b.split.1).natAbs≤affMeasure a+affMeasure b+1
    exact Nat.le_trans (Int.natAbs_add_le _ _) (by omega)
  | scale c a ha =>
    change (c*a.split.1).natAbs≤(c.natAbs+1)*(affMeasure a+1)
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul (by omega) (by omega)

def payload : Atom→Aff
  | .le a => a
  | .dvd _ a => a

theorem payload_measure (a : Atom) : affMeasure (payload a)≤atomMeasure a := by
  cases a <;> simp only [payload,atomMeasure] <;> omega

theorem member_atom_measure (C : Conj) (a : Atom) (h : a∈C) :
    atomMeasure a≤conjMeasure C := by
  induction C with
  | nil => simp at h
  | cons b bs ih =>
    rcases List.mem_cons.mp h with he|hm
    · subst a
      change atomMeasure b≤atomMeasure b+conjMeasure bs+1
      omega
    · have hh := ih hm
      change atomMeasure a≤atomMeasure b+conjMeasure bs+1
      omega

theorem member_conj_measure (F : Formula) (C : Conj) (h : C∈F) :
    conjMeasure C≤measure F := by
  induction F with
  | nil => simp at h
  | cons D Ds ih =>
    rcases List.mem_cons.mp h with he|hm
    · subst C
      change conjMeasure D≤conjMeasure D+measure Ds+1
      omega
    · have hh := ih hm
      change conjMeasure C≤conjMeasure D+measure Ds+1
      omega

theorem formula_coefficient_bound (F : Formula) (C : Conj) (a : Atom)
    (hC : C∈F) (ha : a∈C) : (payload a).split.1.natAbs≤measure F :=
  Nat.le_trans (split_coefficient_bound _)
    (Nat.le_trans (payload_measure _)
      (Nat.le_trans (member_atom_measure C a ha) (member_conj_measure F C hC)))

theorem formula_modulus_bound (F : Formula) (C : Conj) (m : Nat) (a : Aff)
    (hC : C∈F) (ha : Atom.dvd m a∈C) : m≤measure F := by
  have hh := Nat.le_trans (member_atom_measure C (.dvd m a) ha)
    (member_conj_measure F C hC)
  change affMeasure a+m+1≤measure F at hh
  omega

def budget (k : Nat) : Family→Nat
  | [] => 0
  | F::fs => measure (project k F)+budget k fs

theorem member_budget (k : Nat) (fs : Family) (F : Formula) (h : F∈fs) :
    measure (project k F)≤budget k fs := by
  induction fs with
  | nil => simp at h
  | cons G gs ih =>
    rcases List.mem_cons.mp h with he|hm
    · subst F
      change measure (project k G)≤measure (project k G)+budget k gs
      omega
    · have hh := ih hm
      change measure (project k F)≤measure (project k G)+budget k gs
      omega

/-- For a fixed input-shape family, every fixed number of elimination
    stages has one uniform structural bound. No RHS value is bounded. -/
theorem projection_budget (k : Nat) (F : Formula) (fs : Family) (h : Covered F fs) :
    measure (project k F)≤budget k fs := by
  have he := LiteralShape.project_shape k F (LiteralShape.formula F) (by
    simp only [LiteralShape.formula,LiteralShape.conj,List.map_map,Function.comp_def,LiteralShape.atom_idem]
    rfl)
  have hm := congrArg measure he
  rw [measure_erase,measure_erase] at hm
  rw [hm]
  exact member_budget k fs (LiteralShape.formula F) h

theorem projection_branches (k : Nat) (F : Formula) (fs : Family) (h : Covered F fs) :
    (project k F).length≤budget k fs :=
  Nat.le_trans (length_le_measure _) (projection_budget k F fs h)

theorem projection_coefficient (k : Nat) (F : Formula) (fs : Family)
    (h : Covered F fs) (C : Conj) (a : Atom) (hC : C∈project k F) (ha : a∈C) :
    (payload a).split.1.natAbs≤budget k fs :=
  Nat.le_trans (formula_coefficient_bound _ C a hC ha) (projection_budget k F fs h)

theorem projection_modulus (k : Nat) (F : Formula) (fs : Family)
    (h : Covered F fs) (C : Conj) (m : Nat) (a : Aff)
    (hC : C∈project k F) (ha : Atom.dvd m a∈C) : m≤budget k fs :=
  Nat.le_trans (formula_modulus_bound _ C m a hC ha) (projection_budget k F fs h)

def stageBudget : Nat→Family→Nat
  | 0,fs => budget 0 fs
  | k+1,fs => stageBudget k fs+budget (k+1) fs

theorem budget_le_stageBudget (k K : Nat) (fs : Family) (hk : k≤K) :
    budget k fs≤stageBudget K fs := by
  induction K with
  | zero =>
    have he : k=0 := by omega
    subst k
    exact Nat.le_refl _
  | succ K ih =>
    by_cases he : k=K+1
    · subst k
      change budget (K+1) fs≤stageBudget K fs+budget (K+1) fs
      omega
    · have hh := ih (by omega)
      change budget k fs≤stageBudget K fs+budget (K+1) fs
      omega

theorem projection_stage_budget (k K : Nat) (F : Formula) (fs : Family)
    (h : Covered F fs) (hk : k≤K) : measure (project k F)≤stageBudget K fs :=
  Nat.le_trans (projection_budget k F fs h) (budget_le_stageBudget k K fs hk)

def atomModulus : Atom→Nat
  | .le _ => 1
  | .dvd m _ => max 1 m

def conjModulus : Conj→Nat
  | [] => 1
  | a::as => atomModulus a*conjModulus as

def formulaModulus : Formula→Nat
  | [] => 1
  | C::Cs => conjModulus C*formulaModulus Cs

def commonModulus (k : Nat) : Family→Nat
  | [] => 1
  | F::fs => formulaModulus (project k F)*commonModulus k fs

theorem atomModulus_pos (a : Atom) : 0<atomModulus a := by
  cases a <;> simp only [atomModulus] <;> omega

theorem conjModulus_pos (C : Conj) : 0<conjModulus C := by
  induction C with
  | nil => exact Nat.zero_lt_one
  | cons a as ih => exact Nat.mul_pos (atomModulus_pos a) ih

theorem formulaModulus_pos (F : Formula) : 0<formulaModulus F := by
  induction F with
  | nil => exact Nat.zero_lt_one
  | cons C Cs ih => exact Nat.mul_pos (conjModulus_pos C) ih

theorem commonModulus_pos (k : Nat) (fs : Family) : 0<commonModulus k fs := by
  induction fs with
  | nil => exact Nat.zero_lt_one
  | cons F fs ih => exact Nat.mul_pos (formulaModulus_pos _) ih

theorem atomModulus_dvd (C : Conj) (a : Atom) (h : a∈C) :
    atomModulus a∣conjModulus C := by
  induction C with
  | nil => simp at h
  | cons b bs ih =>
    rcases List.mem_cons.mp h with he|hm
    · subst a
      exact Nat.dvd_mul_right _ _
    · exact Nat.dvd_mul_left_of_dvd (ih hm) _

theorem conjModulus_dvd (F : Formula) (C : Conj) (h : C∈F) :
    conjModulus C∣formulaModulus F := by
  induction F with
  | nil => simp at h
  | cons D Ds ih =>
    rcases List.mem_cons.mp h with he|hm
    · subst C
      exact Nat.dvd_mul_right _ _
    · exact Nat.dvd_mul_left_of_dvd (ih hm) _

theorem member_modulus (k : Nat) (fs : Family) (F : Formula) (h : F∈fs) :
    formulaModulus (project k F)∣commonModulus k fs := by
  induction fs with
  | nil => simp at h
  | cons G gs ih =>
    rcases List.mem_cons.mp h with he|hm
    · subst F
      exact Nat.dvd_mul_right _ _
    · exact Nat.dvd_mul_left_of_dvd (ih hm) _

theorem atomModulus_erase (a : Atom) : atomModulus (LiteralShape.atom a)=atomModulus a := by
  cases a <;> rfl

theorem conjModulus_erase (C : Conj) : conjModulus (LiteralShape.conj C)=conjModulus C := by
  induction C with
  | nil => rfl
  | cons a as ih =>
    change atomModulus (LiteralShape.atom a)*conjModulus (LiteralShape.conj as)=_
    rw [atomModulus_erase,ih]
    rfl

theorem formulaModulus_erase (F : Formula) : formulaModulus (LiteralShape.formula F)=formulaModulus F := by
  induction F with
  | nil => rfl
  | cons C Cs ih =>
    change conjModulus (LiteralShape.conj C)*formulaModulus (LiteralShape.formula Cs)=_
    rw [conjModulus_erase,ih]
    rfl

theorem formula_compatible (F : Formula) (h : FormulaGood F) :
    ExponentIntervals.Compatible (formulaModulus F) F := by
  intro C hC a ha
  cases a with
  | le t => trivial
  | dvd m t =>
    have hp : 0<m := h C hC (.dvd m t) ha
    have hd := Nat.dvd_trans (atomModulus_dvd C (.dvd m t) ha) (conjModulus_dvd F C hC)
    have he : max 1 m=m := by omega
    change max 1 m∣formulaModulus F at hd
    rwa [he] at hd

theorem projection_compatible (k : Nat) (F : Formula) (fs : Family)
    (h : Covered F fs) (hg : FormulaGood F) :
    ExponentIntervals.Compatible (commonModulus k fs) (project k F) := by
  have he := LiteralShape.project_shape k F (LiteralShape.formula F) (by
    simp only [LiteralShape.formula,LiteralShape.conj,List.map_map,Function.comp_def,LiteralShape.atom_idem]
    rfl)
  have hm := congrArg formulaModulus he
  rw [formulaModulus_erase,formulaModulus_erase] at hm
  have hd : formulaModulus (project k F)∣commonModulus k fs := by
    rw [hm]
    exact member_modulus k fs (LiteralShape.formula F) h
  have hc := formula_compatible (project k F) (project_good k F hg)
  intro C hC a ha
  have hh := hc C hC a ha
  cases a with
  | le t => trivial
  | dvd m t => exact Nat.dvd_trans hh hd

end REWB.UniformProjection
