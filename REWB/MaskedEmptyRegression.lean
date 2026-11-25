import REWB.MaskedEmptyCost

namespace REWB.MaskedEmpty.Regression

def allWords : DFA Nat := ⟨1,⟨0,by decide⟩,fun _ _=>⟨0,by decide⟩,fun _=>true⟩
def epsilon : DFA Nat := ⟨2,⟨0,by decide⟩,fun _ _=>⟨1,by decide⟩,
  fun q=>decide (q.val=0)⟩
def nonempty : DFA Nat := ⟨2,⟨0,by decide⟩,fun _ _=>⟨1,by decide⟩,
  fun q=>decide (q.val=1)⟩
def endsOne : DFA Nat := ⟨2,⟨0,by decide⟩,
  fun _ c=>if c=1 then ⟨1,by decide⟩ else ⟨0,by decide⟩,
  fun q=>decide (q.val=1)⟩

theorem empty_terminal :
    (solve epsilon epsilon epsilon [] #[true] #[true]).answers=#[true] := by decide

theorem source_gate :
    (solve epsilon allWords epsilon [1,0,1] #[true,false,true,false]
      #[false,false,false,true]).answers=#[true,false,true,false] := by decide

theorem target_terminal :
    (solve epsilon allWords epsilon [1,0,1] #[true,true,true,true]
      #[false,false,false,true]).answers=#[true,true,true,true] := by decide

theorem positive_B_rejects_empty :
    (solve nonempty allWords allWords [1,0] #[true,true,true]
      #[true,true,true]).answers=#[false,false,false] := by decide

theorem noninjective_transition :
    (solve epsilon endsOne epsilon [1,0,1] #[true,true,true,true]
      #[false,false,false,true]).answers=#[true,true,true,false] := by decide

theorem missing_target_is_false :
    (solve epsilon allWords epsilon [1] #[true,true] #[]).answers=#[false,false] := by decide

theorem final_boundary_kept :
    (solve epsilon epsilon epsilon [0,1] #[false,false,true]
      #[false,false,true]).answers=#[false,false,true] := by decide

end REWB.MaskedEmpty.Regression
