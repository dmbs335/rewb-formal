import REWB.MaskedPeriodic

/-! A common modulus from LCMs of actual projected atom moduli. Products
    of every shape modulus are sufficient but unnecessarily inflate the
    residue enumeration. This executable fixed-pattern precomputation
    preserves the same shape argument while retaining only an LCM.
-/
namespace REWB.MaskedPeriodic.Modulus
open REWB.AffineProjection REWB.UniformProjection

def conj : Conj → Nat
  | [] => 1
  | a::as => Nat.lcm (atomModulus a) (conj as)

def formula : Formula → Nat
  | [] => 1
  | C::Cs => Nat.lcm (conj C) (formula Cs)

def family (n : Nat) : Family → Nat
  | [] => 1
  | F::Fs => Nat.lcm (formula (project n F)) (family n Fs)

def familyTR.go (n : Nat) : Family → Nat → Nat
  | [],acc => acc
  | F::Fs,acc => go n Fs (Nat.lcm acc (formula (project n F)))

theorem familyTR.go_eq (n : Nat) (Fs : Family) (acc : Nat) :
    go n Fs acc=Nat.lcm acc (family n Fs) := by
  induction Fs generalizing acc with
  | nil => simp only [go,family,Nat.lcm_one_right]
  | cons F Fs ih =>
    rw [go,ih,Nat.lcm_assoc]
    rfl

def familyTR (n : Nat) (Fs : Family) : Nat := familyTR.go n Fs 1

/-- Pattern preprocessing may have many shapes; the executable fold is
    tail recursive while its result remains kernel-proved identical. -/
@[csimp] theorem family_eq_familyTR : family=familyTR := by
  funext n Fs
  simp only [familyTR,familyTR.go_eq,Nat.lcm_one_left]

theorem conj_pos (C : Conj) : 0<conj C := by
  induction C with
  | nil => decide
  | cons a as ih =>
    exact Nat.pos_of_ne_zero (Nat.lcm_ne_zero (Nat.ne_of_gt (atomModulus_pos a)) (Nat.ne_of_gt ih))

theorem formula_pos (F : Formula) : 0<formula F := by
  induction F with
  | nil => decide
  | cons C Cs ih =>
    exact Nat.pos_of_ne_zero (Nat.lcm_ne_zero (Nat.ne_of_gt (conj_pos C)) (Nat.ne_of_gt ih))

theorem family_pos (n : Nat) (Fs : Family) : 0<family n Fs := by
  induction Fs with
  | nil => exact Nat.zero_lt_one
  | cons F Fs ih =>
    exact Nat.pos_of_ne_zero (Nat.lcm_ne_zero (Nat.ne_of_gt (formula_pos _)) (Nat.ne_of_gt ih))

theorem atom_dvd (C : Conj) (a : Atom) (h : a∈C) : atomModulus a∣conj C := by
  induction C with
  | nil => simp at h
  | cons b bs ih =>
    rcases List.mem_cons.mp h with rfl|h
    · exact Nat.dvd_lcm_left _ _
    · exact Nat.dvd_trans (ih h) (Nat.dvd_lcm_right _ _)

theorem conj_dvd (F : Formula) (C : Conj) (h : C∈F) : conj C∣formula F := by
  induction F with
  | nil => simp at h
  | cons D Ds ih =>
    rcases List.mem_cons.mp h with rfl|h
    · exact Nat.dvd_lcm_left _ _
    · exact Nat.dvd_trans (ih h) (Nat.dvd_lcm_right _ _)

theorem member_dvd (n : Nat) (Fs : Family) (F : Formula) (h : F∈Fs) :
    formula (project n F)∣family n Fs := by
  induction Fs with
  | nil => simp at h
  | cons G Gs ih =>
    rcases List.mem_cons.mp h with rfl|h
    · exact Nat.dvd_lcm_left _ _
    · exact Nat.dvd_trans (ih h) (Nat.dvd_lcm_right _ _)

theorem conj_erase (C : Conj) : conj (LiteralShape.conj C)=conj C := by
  induction C with
  | nil => rfl
  | cons a as ih =>
    change Nat.lcm (atomModulus (LiteralShape.atom a)) (conj (LiteralShape.conj as))=_
    rw [atomModulus_erase,ih]
    rfl

theorem formula_erase (F : Formula) : formula (LiteralShape.formula F)=formula F := by
  induction F with
  | nil => rfl
  | cons C Cs ih =>
    change Nat.lcm (conj (LiteralShape.conj C)) (formula (LiteralShape.formula Cs))=_
    rw [conj_erase,ih]
    rfl

theorem formula_compatible (F : Formula) (hF : FormulaGood F) :
    ExponentIntervals.Compatible (formula F) F := by
  intro C hC a ha
  cases a with
  | le t => trivial
  | dvd m t =>
    have hp : 0<m := hF C hC (.dvd m t) ha
    have hd := Nat.dvd_trans (atom_dvd C (.dvd m t) ha) (conj_dvd F C hC)
    change max 1 m∣formula F at hd
    rwa [show max 1 m=m by omega] at hd

theorem projection_compatible (n : Nat) (F : Formula) (Fs : Family)
    (h : Covered F Fs) (hF : FormulaGood F) :
    ExponentIntervals.Compatible (family n Fs) (project n F) := by
  have he := LiteralShape.project_shape n F (LiteralShape.formula F) (by
    simp only [LiteralShape.formula,LiteralShape.conj,List.map_map,Function.comp_def,LiteralShape.atom_idem]
    rfl)
  have hm := congrArg formula he
  rw [formula_erase,formula_erase] at hm
  have hd : formula (project n F)∣family n Fs := by
    rw [hm]
    exact member_dvd n Fs (LiteralShape.formula F) h
  have hc := formula_compatible (project n F) (project_good n F hF)
  intro C hC a ha
  have hh := hc C hC a ha
  cases a with
  | le t => trivial
  | dvd m t => exact Nat.dvd_trans hh hd

end REWB.MaskedPeriodic.Modulus
