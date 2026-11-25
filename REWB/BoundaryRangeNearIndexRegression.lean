import REWB.BoundaryRangeNearIndexScanCost

/-! Kernel regressions for dependent table payloads, noninjective C
subset selection, empty blocks, and each of the three cached branches. -/
namespace REWB.BoundaryRange.NearIndex.Regression
open REWB.BoundaryApplication
open REWB.BoundaryIndex

def dependent : Table.Index (fun i : Fin 4=>Vector Nat (i.val+1)) :=
  Table.build fun i=>(Vector.ofFn (fun j=>10*i.val+j.val),i.val+2)

theorem dependent_payload : (Table.get dependent 2).toList=[20,21,22] := by decide
theorem factory_counts_once : dependent.work=27 := by decide

def allWords : DFA (Fin 2) := ⟨1,0,fun _ _=>0,fun _=>true⟩
def epsilon : DFA (Fin 2) := ⟨2,0,fun _ _=>1,fun q=>decide (q=0)⟩
def nonempty : DFA (Fin 2) := ⟨2,0,fun _ _=>1,fun q=>decide (q=1)⟩
def reset : DFA (Fin 2) := ⟨2,0,fun _ c=>c,fun q=>decide (q=1)⟩
def word : Word (Fin 2) := [0,1,0]

theorem coalesced_final_subset :
    let chosen:=TableColor.choose reset (TableColor.build reset)
      (fun q=>reset.final ((Range.query reset (Range.build reset word) 0 2).map.get q))
    Colors.decode reset chosen.1 ⟨0,by decide⟩=true ∧ Colors.decode reset chosen.1 ⟨1,by decide⟩=true := by
  dsimp only
  rw [TableColor.choose_correct]
  simp only [Range.query_correct reset word 0 2 (by decide) (by decide)]
  decide

theorem zero_width :
    (queryThree (build allWords allWords allWords allWords allWords allWords [] 0 0 0
      (Nat.le_refl 0) (Nat.le_refl 0)) 0 0)=(false,5) := rfl

private theorem witness : Copy epsilon nonempty epsilon word 1 2 3 := by
  refine ⟨1,by decide,by decide,?_,?_,?_,?_⟩
  all_goals first | decide | (unfold DFA.accepts; decide)

theorem cached_separated :
    (querySeparated (build epsilon nonempty epsilon allWords nonempty epsilon word 0 1 2
      (by decide) (by decide)) 1 3).1=true := by
  apply (querySeparated_correct epsilon nonempty epsilon allWords nonempty epsilon word 0 1 2
    (by decide) (by decide) 1 3 (by decide) (by decide) (by decide)).mpr
  refine ⟨1,1,2,⟨by decide,by decide,by decide,?_,?_,?_,witness⟩,by decide,by decide,by decide⟩
  all_goals unfold DFA.accepts; decide

theorem cached_end :
    (queryEnd (build epsilon nonempty epsilon allWords nonempty epsilon word 0 0 2
      (by decide) (by decide)) 1 3).1=true := by
  apply (queryEnd_correct epsilon nonempty epsilon allWords nonempty epsilon word 0 0 2
    (by decide) (by decide) 1 3 (by decide) (by decide) (by decide)).mpr
  refine ⟨1,1,2,⟨by decide,by decide,by decide,?_,?_,?_,witness⟩,by decide,by decide,by decide⟩
  all_goals unfold DFA.accepts; decide

theorem cached_start :
    (queryStart (build epsilon nonempty epsilon allWords nonempty epsilon word 0 1 3
      (by decide) (by decide)) 1 3).1=true := by
  apply (queryStart_correct epsilon nonempty epsilon allWords nonempty epsilon word 0 1 3
    (by decide) (by decide) 1 3 (by decide) (by decide) (by decide)).mpr
  refine ⟨1,1,2,⟨by decide,by decide,by decide,?_,?_,?_,witness⟩,by decide,by decide,by decide⟩
  all_goals unfold DFA.accepts; decide

end REWB.BoundaryRange.NearIndex.Regression
