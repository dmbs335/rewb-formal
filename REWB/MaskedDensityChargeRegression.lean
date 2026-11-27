import REWB.MaskedDensityChargeBudget

/-! First-threshold regressions: an equal-depth refinement is a real
serialized node and contains the same suffix start, but cannot receive
the threshold charge. Actual suffix preparation is also instantiated. -/
namespace REWB.MaskedDensityCharge.Regression
open REWB.BoundaryTrie
open REWB.MaskedRunDiscovery
open REWB.MaskedOrdered.Owner
open REWB.RunGeometry REWB.Periodic

def a : Key 6 Nat := ⟨0,2,by decide,0⟩
def b : Key 6 Nat := ⟨1,2,by decide,1⟩
def c : Key 6 Nat := ⟨2,2,by decide,2⟩
def refinement : Tree 6 Nat := .node a 2 (.leaf a) (.leaf b)
def whole : Tree 6 Nat := .node a 2 refinement (.leaf c)

theorem refinement_is_stored : Location whole none 0 refinement (some ⟨2,0⟩) 1 :=
  .left (.here _ _ _)

theorem same_start_below_refinement : 0∈positions refinement := by decide

theorem parent_has_charge : At whole ⟨0,0,1⟩ :=
  ⟨whole,none,.here _ _ _,.here _ (by decide),by decide⟩

theorem refinement_cannot_charge : ¬At whole ⟨1,0,1⟩ := by
  intro h
  have hn : (positions whole).Nodup := by decide
  have he:=at_injective whole hn ⟨1,0,1⟩ ⟨0,0,1⟩ h parent_has_charge rfl
  have hid:=congrArg Charge.node he
  cases hid

def text : Array (Fin 2) := #[0,0,1,0,0,0]

theorem actual_square : PrimitiveSquare (ArrayText.read text 0) text.size 0 1 := by
  refine ⟨by decide,by decide,?_,?_⟩
  · intro i hi
    have he : i=0 := by omega
    subst i
    rfl
  · intro p hp _
    omega

theorem actual_unique_charge :
    ∃id,Certified text 0 ⟨id,0,1⟩ ∧ ∀other,Certified text 0 ⟨other,0,1⟩→other=id :=
  canonical_exists text 0 0 1 actual_square

theorem empty_records (cs : List Charge) (hd : cs.Nodup)
    (hc : ∀c,c∈cs→Certified (#[] : Array (Fin 2)) 0 c) : cs=[] := by
  have hb:=certified_budget (#[] : Array (Fin 2)) 0 cs hd hc
  simp only [Array.size_empty,Nat.mul_zero,Nat.zero_mul] at hb
  exact List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hb)

end REWB.MaskedDensityCharge.Regression
