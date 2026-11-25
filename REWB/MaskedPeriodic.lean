import REWB.MaskedPeriodicOrbit

/-! The three exact block-coordinate families of the within-run 1-use
    branch. Only the source exponent a is projected; the target exponent
    k remains free. A positive cut contributes one borrow in the gap.
    The final-fragment case has no remaining full period in the E factor.
    Realizability of the three maps by one common cut is connected in the
    DFA/tuple adapter, not assumed by this arithmetic compiler.
-/
namespace REWB.MaskedPeriodic
open REWB.AffineProjection REWB.PhaseSolver REWB.UniformProjection

inductive Branch where
  | zero
  | interior
  | ending
  deriving Repr, DecidableEq

def Branch.carry : Branch → Nat
  | .zero => 0
  | .interior | .ending => 1

def Branch.endOK : Branch → Nat → Nat → Nat → Prop
  | .zero,N,a,k => k+a≤N
  | .interior,N,a,k => k+a+1≤N
  | .ending,N,a,k => k+a=N

def Geometry (branch : Branch) (N a k : Nat) : Prop :=
  2≤a ∧ a+branch.carry≤k ∧ branch.endOK N a k

def tailCount : Branch → Nat → Nat → Nat → Nat
  | .zero,N,a,k => N-k-a
  | .interior,N,a,k => N-k-a-1
  | .ending,_,_,_ => 0

def aExpr : Aff := .var 0
def kExpr : Aff := .var 1
def gapExpr (branch : Branch) : Aff := (kExpr.sub aExpr).sub (.lit branch.carry)
def tailExpr : Branch → Nat → Aff
  | .zero,N => ((Aff.lit N).sub kExpr).sub aExpr
  | .interior,N => (((Aff.lit N).sub kExpr).sub aExpr).sub (.lit 1)
  | .ending,_ => .lit 0

def upperFormula : Branch → Nat → Formula
  | .zero,N => le (.add kExpr aExpr) (.lit N)
  | .interior,N => le (.add (.add kExpr aExpr) (.lit 1)) (.lit N)
  | .ending,N => eq (.add kExpr aExpr) (.lit N)

def boundsFormula (branch : Branch) (N : Nat) : Formula :=
  both (le (.lit 2) aExpr)
    (both (le (.add aExpr (.lit branch.carry)) kExpr) (upperFormula branch N))

theorem boundsFormula_correct (branch : Branch) (N a k : Nat) :
    Satisfies (boundsFormula branch N) [(a:Int),(k:Int)] ↔ Geometry branch N a k := by
  cases branch <;>
    simp only [boundsFormula,upperFormula,both_correct,le_correct,eq_correct,
      Geometry,Branch.carry,Branch.endOK,aExpr,kExpr,Aff.eval,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some] <;> omega

theorem boundsFormula_nonneg (branch : Branch) (N : Nat) (a k : Int)
    (h : Satisfies (boundsFormula branch N) [a,k]) : 0≤a := by
  have hh := ((both_correct _ _ _).mp h).1
  rw [le_correct] at hh
  change (2:Int)≤a at hh
  omega

theorem boundsFormula_good (branch : Branch) (N : Nat) :
    FormulaGood (boundsFormula branch N) := by
  apply both_good _ _ (le_good _ _)
  apply both_good _ _ (le_good _ _)
  cases branch
  · exact le_good _ _
  · exact le_good _ _
  · exact eq_good _ _

theorem gapExpr_eval (branch : Branch) (N a k : Nat) (h : Geometry branch N a k) :
    (gapExpr branch).eval [(a:Int),(k:Int)]=((k-a-branch.carry:Nat):Int) := by
  have hh := h.2.1
  simp only [gapExpr,kExpr,aExpr,Aff.eval_sub,Aff.eval,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  omega

theorem tailExpr_eval (branch : Branch) (N a k : Nat) (h : Geometry branch N a k) :
    (tailExpr branch N).eval [(a:Int),(k:Int)]=(tailCount branch N a k:Int) := by
  have hh := h.2.2
  cases branch <;>
    simp only [tailExpr,tailCount,kExpr,aExpr,Aff.eval_sub,Aff.eval,Branch.endOK,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some] at * <;> omega

structure Data (b c e : Nat) where
  capture : OrbitData b
  gap : OrbitData c
  suffix : OrbitData e

def Accepts {b c e : Nat} (data : Data b c e) (branch : Branch) (N a k : Nat) : Prop :=
  Geometry branch N a k ∧ data.capture.test a=true ∧
    data.gap.test (k-a-branch.carry)=true ∧ data.suffix.test (tailCount branch N a k)=true

def formula {b c e : Nat} (data : Data b c e) (branch : Branch) (N : Nat) : Formula :=
  both (boundsFormula branch N)
    (both (data.capture.formula aExpr)
      (both (data.gap.formula (gapExpr branch)) (data.suffix.formula (tailExpr branch N))))

theorem formula_good {b c e : Nat} (data : Data b c e) (branch : Branch) (N : Nat) :
    FormulaGood (formula data branch N) :=
  both_good _ _ (boundsFormula_good branch N)
    (both_good _ _ (data.capture.formula_good _)
      (both_good _ _ (data.gap.formula_good _) (data.suffix.formula_good _)))

theorem formula_correct {b c e : Nat} (data : Data b c e) (branch : Branch) (N a k : Nat) :
    Satisfies (formula data branch N) [(a:Int),(k:Int)] ↔ Accepts data branch N a k := by
  simp only [formula,both_correct,boundsFormula_correct]
  constructor
  · rintro ⟨hg,hb,hc,he⟩
    exact ⟨hg,(data.capture.formula_correct _ _ a rfl).mp hb,
      (data.gap.formula_correct _ _ _ (gapExpr_eval branch N a k hg)).mp hc,
      (data.suffix.formula_correct _ _ _ (tailExpr_eval branch N a k hg)).mp he⟩
  · rintro ⟨hg,hb,hc,he⟩
    exact ⟨hg,(data.capture.formula_correct _ _ a rfl).mpr hb,
      (data.gap.formula_correct _ _ _ (gapExpr_eval branch N a k hg)).mpr hc,
      (data.suffix.formula_correct _ _ _ (tailExpr_eval branch N a k hg)).mpr he⟩

def projection {b c e : Nat} (data : Data b c e) (branch : Branch) (N : Nat) : Formula×Nat :=
  CountedProjection.project 1 (formula data branch N)

theorem projection_value {b c e : Nat} (data : Data b c e) (branch : Branch) (N : Nat) :
    (projection data branch N).1=AffineProjection.project 1 (formula data branch N) :=
  CountedProjection.project_value _ _

theorem projection_correct {b c e : Nat} (data : Data b c e) (branch : Branch) (N k : Nat) :
    Satisfies (projection data branch N).1 [(k:Int)] ↔ ∃ a,Accepts data branch N a k := by
  rw [projection_value,AffineProjection.project_correct _ _ _ (formula_good data branch N)]
  change (∃ a : Int,Satisfies (formula data branch N) [a,(k:Int)]) ↔ _
  constructor
  · rintro ⟨a,ha⟩
    have hb : Satisfies (boundsFormula branch N) [a,(k:Int)] :=
      ((both_correct _ _ _).mp ha).1
    have hn := boundsFormula_nonneg branch N a (k:Int) hb
    have he : (a.toNat:Int)=a := by omega
    refine ⟨a.toNat,(formula_correct data branch N a.toNat k).mp ?_⟩
    simpa only [he] using ha
  · rintro ⟨a,ha⟩
    exact ⟨(a:Int),(formula_correct data branch N a k).mpr ha⟩

theorem accepts_target_bound {b c e : Nat} (data : Data b c e) (branch : Branch)
    (N a k : Nat) (h : Accepts data branch N a k) : k≤N := by
  have hh := h.1.2.2
  cases branch <;> simp only [Branch.endOK] at hh <;> omega

end REWB.MaskedPeriodic
