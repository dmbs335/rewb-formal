import REWB.BoundaryBorderDyadic

/-! Kernel checks for the actual text-built suffix/prefix query. The
compiled preparation and each physical result are checked independently
in the accompanying runtime audit. -/
namespace REWB.BoundaryBorder.Window.Regression
open REWB.BoundaryBorder

theorem truncated_lower_boundary : Dyadic.lower 5 4=0 ∧ Dyadic.upper 5 4=1 := by decide

theorem empty_positive (p : Nat) :
    ¬(Dyadic.query (WindowIndex.prepare (#[] : Array (Fin 2)) 0) 0 0).Holds p := by
  rw [Dyadic.query_correct _ _ _ _ (by decide)]
  rintro ⟨hh,_⟩
  omega

def twoWord : Word (Fin 2) := [0,0,1,0,0,1,0]
def twoIndex := WindowIndex.prepare twoWord.toArray 0

theorem two_component_sources :
    (Dyadic.query twoIndex 7 0).Holds 0 ∧
    (Dyadic.query twoIndex 7 0).Holds 3 ∧
    ¬(Dyadic.query twoIndex 7 0).Holds 1 := by
  constructor
  · exact (Dyadic.query_iff_slices twoWord 0 7 0 (by decide) 0).mpr ⟨by decide,by decide,by decide⟩
  constructor
  · exact (Dyadic.query_iff_slices twoWord 0 7 0 (by decide) 3).mpr ⟨by decide,by decide,by decide⟩
  · unfold twoIndex
    rw [Dyadic.query_iff_slices twoWord 0 7 0 (by decide) 1]
    decide

def alternating : Word (Fin 2) := [0,1,0,1,0,1,0,1]

theorem dense_holes (p : Fin 9) :
    (Dyadic.query (WindowIndex.prepare alternating.toArray 0) 8 0).Holds p.val ↔
      p.val=0 ∨ p.val=2 ∨ p.val=4 ∨ p.val=6 := by
  rw [Dyadic.query_iff_slices alternating 0 8 0 (by decide) p.val]
  have hh : ∀p : Fin 9,
      (p.val<8 ∧ 0+(8-p.val)≤alternating.length ∧
        Spec.slice alternating p.val 8=Spec.slice alternating 0 (0+(8-p.val))) ↔
      p.val=0 ∨ p.val=2 ∨ p.val=4 ∨ p.val=6 := by decide
  exact hh p

theorem target_at_end (p : Nat) :
    ¬(Dyadic.query (WindowIndex.prepare alternating.toArray 0) 8 8).Holds p := by
  rw [Dyadic.query_iff_slices alternating 0 8 8 (by decide) p]
  rintro ⟨hpa,hb,_⟩
  change 8+(8-p)≤8 at hb
  omega

theorem epsilon_excluded :
    ¬(Dyadic.query (WindowIndex.prepare alternating.toArray 0) 8 0).Holds 8 := by
  rw [Dyadic.query_iff_slices alternating 0 8 0 (by decide) 8]
  rintro ⟨hh,_⟩
  omega

end REWB.BoundaryBorder.Window.Regression
