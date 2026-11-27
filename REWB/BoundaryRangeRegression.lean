import REWB.BoundaryRangeMask

/-! Kernel examples for block classification, noninjective reversal,
shared regular split selection, and the actually materialized masks. -/
namespace REWB.BoundaryRange.Regression

abbrev all : DFA (Fin 2) := ⟨1,0,fun _ _=>0,fun _=>true⟩
abbrev emptyOnly : DFA (Fin 2) := ⟨2,0,fun _ _=>1,fun q=>decide (q=0)⟩
abbrev positive : DFA (Fin 2) := ⟨2,0,fun _ _=>1,fun q=>decide (q=1)⟩
abbrev reset : DFA (Fin 2) := ⟨2,0,fun _ c=>c,fun q=>decide (q=1)⟩

theorem all_six_regions :
    regionOf 4 8 6 9 12=.farLeft ∧
    regionOf 4 8 9 9 12=.farRight ∧
    regionOf 4 8 3 6 9=.nearSeparated ∧
    regionOf 4 8 5 6 9=.nearEnd ∧
    regionOf 4 8 3 6 7=.nearStart ∧
    regionOf 4 8 5 6 7=.nearBorder := by decide

theorem boundary_equalities :
    regionOf 4 8 8 8 8=.farLeft ∧
    regionOf 4 8 4 7 8=.nearSeparated ∧
    regionOf 4 8 4 7 7=.nearStart := by decide

theorem noninjective_reversal :
    (Automata.reverse reset).accepts [1,0,0] ∧
      ¬(Automata.reverse reset).accepts [0,1,1] := by
  constructor
  · apply (Automata.reverse_accepts reset _).mpr
    unfold DFA.accepts
    decide
  · rw [Automata.reverse_accepts]
    unfold DFA.accepts
    decide

theorem separate_regular_splits_rejected :
    ¬(Automata.gap emptyOnly positive all emptyOnly.initial positive.initial).accepts [0] := by
  rw [Automata.gap,Automata.join_accepts]
  rintro ⟨u,v,he,hmeet,_⟩
  obtain ⟨hu,hv⟩:=(Automata.meet_accepts _ _ u).mp hmeet
  rw [Automata.start_accepts] at hu hv
  cases u with
  | nil => exact Bool.noConfusion hv
  | cons a u =>
    have hr : ∀s : Fin 2,∀z : Word (Fin 2),emptyOnly.run 1 z=1 := by
      intro s z
      induction z with
      | nil => rfl
      | cons c z ih => exact ih
    change decide (emptyOnly.run 1 u=0)=true at hu
    rw [hr 0 u] at hu
    contradiction

def maskWord : Word (Fin 2) := [0,1,0,1]

theorem real_reversed_mask :
    (FarMask.build reset (BoundaryApplication.Range.build reset maskWord) 4 1 0 1).bits.toList=
      [true,false,true,false,false] := by
  change (FarMask.build reset (BoundaryApplication.Range.build reset maskWord) maskWord.length 1 0 1).bits.toList=_
  rw [FarMask.build_bits,Vector.toList_ofFn]
  decide

theorem no_tail_beyond_text :
    (FarMask.build reset (BoundaryApplication.Range.build reset maskWord) 4 9 0 1).bits.toList=
      [false,false,false,false,false] := by decide

theorem original_terminal_not_selected :
    (FarMask.build reset (BoundaryApplication.Range.build reset maskWord) 4 0 0 1).bits.get 4=false := by
  decide

end REWB.BoundaryRange.Regression
