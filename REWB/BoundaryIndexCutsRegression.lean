import REWB.BoundaryIndexFixedEnd

/-! Endpoint and orientation regressions for the variable cut window. -/
namespace REWB.BoundaryIndex.CutsRegression

def anyWord : DFA Bool := ⟨1,0,fun _ _=>0,fun _=>true⟩
def emptyWord : DFA Bool := ⟨2,0,fun _ _=>1,fun q=>decide (q=0)⟩
def sample : Word Bool := [true,false]

/-- The explicit epsilon matrix includes a=b=r. -/
theorem right_endpoint :
    (Cuts.query anyWord emptyWord (Cuts.build anyWord emptyWord sample).1
      0 2 2 2 (0 : Fin 1)).answer=some true := by
  apply (Cuts.query_correct anyWord emptyWord sample 0 2 2 2 (0 : Fin 1)
    (by decide) (by decide) (by decide) (by decide)).mpr
  exact ⟨2,by decide,by decide,by decide,by rfl⟩

/-- Excluding the terminal cut cannot accidentally accept it. -/
theorem right_endpoint_excluded :
    (Cuts.query anyWord emptyWord (Cuts.build anyWord emptyWord sample).1
      0 0 1 2 (0 : Fin 1)).answer≠some true := by
  intro hh
  obtain ⟨i,hi,hj,_,hb⟩ := (Cuts.query_correct anyWord emptyWord sample 0 0 1 2 (0 : Fin 1)
    (by decide) (by decide) (by decide) (by decide)).mp hh
  have he : i=0 ∨ i=1 := by omega
  rcases he with rfl|rfl <;> simp [DFA.accepts,DFA.run,emptyWord,sample,Spec.slice] at hb

/-- a=b=l is included, even when the text interval is nonempty. -/
theorem left_endpoint :
    (Cuts.query emptyWord anyWord (Cuts.build emptyWord anyWord sample).1
      0 0 0 2 (0 : Fin 2)).answer=some true := by
  apply (Cuts.query_correct emptyWord anyWord sample 0 0 0 2 (0 : Fin 2)
    (by decide) (by decide) (by decide) (by decide)).mpr
  exact ⟨0,by decide,by decide,by decide,by rfl⟩

/-- The prefix segment has all switches disabled. -/
theorem left_endpoint_excluded :
    (Cuts.query emptyWord anyWord (Cuts.build emptyWord anyWord sample).1
      0 1 2 2 (0 : Fin 2)).answer≠some true := by
  intro hh
  obtain ⟨i,hi,hj,hd,_⟩ := (Cuts.query_correct emptyWord anyWord sample 0 1 2 2 (0 : Fin 2)
    (by decide) (by decide) (by decide) (by decide)).mp hh
  have he : i=1 ∨ i=2 := by omega
  rcases he with rfl|rfl <;> simp [DFA.run,emptyWord,sample,Spec.slice] at hd

/-- The empty input has one admissible boundary. -/
theorem empty_input :
    (Cuts.query emptyWord emptyWord (Cuts.build emptyWord emptyWord []).1
      0 0 0 0 (0 : Fin 2)).answer=some true := by
  apply (Cuts.query_correct emptyWord emptyWord [] 0 0 0 0 (0 : Fin 2)
    (by decide) (by decide) (by decide) (by decide)).mpr
  exact ⟨0,by decide,by decide,by decide,by rfl⟩

def singleton (c : Bool) : DFA Bool :=
  ⟨3,0,fun q x=>if q=0 ∧ x=c then 1 else 2,fun q=>decide (q=1)⟩

/-- X is a reversed-trie label. X=[false,true] represents the actual
fragment [true,false], split into the A word [true] and B word [false]. -/
theorem reversed_label_orientation :
    (FixedEnd.query (singleton true) (singleton false) anyWord
      (FixedEnd.build (singleton true) (singleton false) anyWord [true,false]).1
      2 2 1 1 (0 : Fin 3) (0 : Fin 1)).answer=some true := by
  apply (FixedEnd.reverse_query_correct (singleton true) (singleton false) anyWord
    [false,true] 1 1 (0 : Fin 3) (0 : Fin 1) (by decide) (by decide)).mpr
  exact ⟨1,by decide,by decide,by rfl,by rfl,by rfl⟩

end REWB.BoundaryIndex.CutsRegression
