import REWB.MaskedSourceFanoutPrepared

namespace REWB.MaskedSourceFanout.Regression
open REWB.RunGeometry

def windows : List Bounds := [⟨0,4,1⟩,⟨2,6,1⟩]
def index : Built := build 6 windows

theorem overlapping_memberships :
    (read index.rows 3).ids=[1,0] ∧ (read index.rows 3).count=2 ∧
    index.memberships=10 := by decide

theorem duplicate_removal :
    (take 3 index).1.ids=[1,0] ∧ (take 3 (take 3 index).2).1.ids=[] := by decide

theorem mixed_requests :
    (drain [3,3,0,6,20] index).visits=4 ∧
    (drain [3,3,0,6,20] index).remaining.memberships=6 ∧
    (read (drain [3,3,0,6,20] index).remaining.rows 2).ids=[1,0] := by decide

theorem empty_preparation (fallback : Fin σ) :
    (prepare (#[] : Array (Fin σ)) fallback).sources.memberships=0 := by
  have h:=prepare_memberships (#[] : Array (Fin σ)) fallback
  simpa using h

end REWB.MaskedSourceFanout.Regression
