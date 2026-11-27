import REWB.MaskedMutableProgressionCost

/-! Kernel reductions for persistent physical deletion, residue isolation,
short masks, huge steps, empty windows and clipped AP witnesses. -/
namespace REWB.MaskedMutableProgression.Regression

private def source : Array Bool := #[false,true,true,true,false,true,false]
private def initial : Index := (build source 1 5 2).index
private def afterOne : Index := (erase initial 1).index

theorem physical_delete :
    (grid initial 0 3).value=some 1 ∧
    (grid afterOne 0 3).value=some 3 ∧
    (member afterOne 1).1=false ∧
    (member afterOne 2).1=true := by
  simp only [initial,afterOne,source,build,
    show height 5=6 by simp [height,Nat.log2],
    show height 7=8 by simp [height,Nat.log2],
    show height 8=8 by simp [height,Nat.log2]]
  decide

theorem persistent_previous :
    (grid (erase afterOne 3).index 0 3).value=some 5 ∧
    (grid afterOne 0 3).value=some 3 ∧
    (grid initial 0 3).value=some 1 := by
  simp only [initial,afterOne,source,build,
    show height 5=6 by simp [height,Nat.log2],
    show height 7=8 by simp [height,Nat.log2],
    show height 8=8 by simp [height,Nat.log2]]
  decide

theorem repeated_and_outside :
    (grid (erase afterOne 1).index 0 3).value=some 3 ∧
    (grid (erase afterOne 0).index 0 3).value=some 3 ∧
    (grid (erase afterOne 6).index 0 3).value=some 3 := by
  simp only [initial,afterOne,source,build,
    show height 5=6 by simp [height,Nat.log2],
    show height 7=8 by simp [height,Nat.log2],
    show height 8=8 by simp [height,Nat.log2]]
  decide

theorem short_mask_huge_step :
    (grid (build #[true,false,true] 2 7 1000000007).index 0 999999).value=some 2 ∧
    (grid (erase (build #[true,false,true] 2 7 1000000007).index 2).index 0 999999).value=none ∧
    (grid (build #[true,false,true] 2 7 1000000007).index 1 999999).value=none := by
  simp only [initial,afterOne,source,build,
    show height 5=6 by simp [height,Nat.log2],
    show height 7=8 by simp [height,Nat.log2],
    show height 8=8 by simp [height,Nat.log2]]
  decide

theorem empty_and_zero_request :
    (grid (build source 1 0 2).index 0 100).value=none ∧
    (grid initial 0 0).value=none ∧
    (grid initial 5 4).value=none := by
  simp only [initial,afterOne,source,build,
    show height 5=6 by simp [height,Nat.log2],
    show height 7=8 by simp [height,Nat.log2],
    show height 8=8 by simp [height,Nat.log2]]
  decide

private def apSource : Array Bool :=
  #[false,false,false,false,false,false,true,false,false,false,true,false,false]
private def apInitial : Index := (build apSource 5 8 4).index

theorem clipped_ap_delete :
    (ap apInitial 2 2 0 0 10 1).value=some 6 ∧
    (ap (erase apInitial 6).index 2 2 0 0 10 1).value=some 10 ∧
    (ap apInitial 2 2 0 0 10 2).value=none ∧
    (ap apInitial 2 3 0 0 10 1).value=none := by
  simp only [apInitial,apSource,build,
    show height 5=6 by simp [height,Nat.log2],
    show height 7=8 by simp [height,Nat.log2],
    show height 8=8 by simp [height,Nat.log2]]
  decide

end REWB.MaskedMutableProgression.Regression
