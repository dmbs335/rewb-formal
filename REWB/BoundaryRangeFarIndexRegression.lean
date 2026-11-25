import REWB.BoundaryRangeFarIndex
import REWB.BoundaryRangeRegression

namespace REWB.BoundaryRange.FarLeft.Regression
open REWB.BoundaryRange.Regression

theorem empty_actual_query :
    (query all all (build all all all all all all [] 0 0 (by decide)) 0 0).1=true := by
  apply (query_correct all all all all all all [] 0 0 (by decide) 0 0 0 (by decide) (by decide)).mpr
  refine ⟨0,0,0,?_,⟨Nat.le_refl _,Nat.le_refl _⟩⟩
  refine ⟨by decide,by decide,by decide,rfl,rfl,rfl,0,by decide,by decide,rfl,rfl,rfl,rfl⟩

theorem invalid_left_rejected :
    (query all all (build all all all all all all [] 0 0 (by decide)) 1 0).1=false := by
  simp [query,build]

theorem invalid_right_rejected :
    (query all all (build all all all all all all [] 0 0 (by decide)) 0 1).1=false := by
  simp [query,build]

end REWB.BoundaryRange.FarLeft.Regression
