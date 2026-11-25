import REWB.ResidualSeparatedP1
import REWB.ResidualSeparatedP2

namespace REWB.ResidualSeparated.Regression

abbrev all : DFA (Fin 2) := ⟨1,0,(fun _ _=>0),(fun _=>true)⟩
abbrev empty : DFA (Fin 2) := ⟨2,0,(fun _ _=>1),(fun q=>decide (q=0))⟩
abbrev positive : DFA (Fin 2) := ⟨2,0,(fun _ _=>1),(fun q=>decide (q=1))⟩
abbrev p1 : SevenDFA (Fin 2) := ⟨empty,positive,empty,empty,empty,empty,empty⟩
abbrev p2 : SevenDFA (Fin 2) := ⟨empty,empty,positive,empty,empty,empty,empty⟩

theorem earlier_source_outside_strip :
    ∃q : Fin p1.G.stateCount,Spec.boundaryRange p1.A p1.B p1.C
      (gapStart p1.G (BoundaryApplication.Range.build p1.G [0,0,0]) 1 2 1 q) p1.D
      (outerSuffix p1.F p1.G p1.H (BoundaryApplication.Range.build p1.H [0,0,0]) 2 1 3 q)
      [0,0,0] 1 2 := by
  have hw : Window ([0,0,0] : Word (Fin 2)) 1 2 1:=⟨by (try unfold DFA.accepts); decide,by (try unfold DFA.accepts); decide,by (try unfold DFA.accepts); decide,by (try unfold DFA.accepts); decide⟩
  apply (p1_iff p1 [0,0,0] 1 2 1 hw).mpr
  exact ⟨⟨0,1,1,1,2,2,by (try unfold DFA.accepts); decide,by (try unfold DFA.accepts); decide,by (try unfold DFA.accepts); decide,by (try unfold DFA.accepts); decide,by (try unfold DFA.accepts); decide,by (try unfold DFA.accepts); decide,by (try unfold DFA.accepts); decide,
    by (try unfold DFA.accepts); decide,by (try unfold DFA.accepts); decide,by (try unfold DFA.accepts); decide,by (try unfold DFA.accepts); decide,by (try unfold DFA.accepts); decide,by (try unfold DFA.accepts); decide,by (try unfold DFA.accepts); decide,by (try unfold DFA.accepts); decide⟩⟩

theorem nested_inner_inside_strip :
    ∃q : Fin p2.G.stateCount,Spec.oneUseRange
      (innerPrefix p2.A p2.B p2.G (BoundaryApplication.Range.build p2.A [0,0,0,0])
        (BoundaryApplication.Range.build p2.G [0,0,0,0]) 0 2 2 q)
      p2.C p2.D (outerSuffix p2.F p2.G p2.H
        (BoundaryApplication.Range.build p2.H [0,0,0,0]) 2 2 4 q) [0,0,0,0] 0 2 := by
  have hw : Window ([0,0,0,0] : Word (Fin 2)) 0 2 2:=⟨by (try unfold DFA.accepts); decide,by (try unfold DFA.accepts); decide,by (try unfold DFA.accepts); decide,by (try unfold DFA.accepts); decide⟩
  apply (p2_iff p2 [0,0,0,0] 0 2 2 hw).mpr
  exact ⟨⟨0,0,1,1,2,2,by (try unfold DFA.accepts); decide,by (try unfold DFA.accepts); decide,by (try unfold DFA.accepts); decide,by (try unfold DFA.accepts); decide,by (try unfold DFA.accepts); decide,by (try unfold DFA.accepts); decide,by (try unfold DFA.accepts); decide,
    by (try unfold DFA.accepts); decide,by (try unfold DFA.accepts); decide,by (try unfold DFA.accepts); decide,by (try unfold DFA.accepts); decide,by (try unfold DFA.accepts); decide,by (try unfold DFA.accepts); decide,by (try unfold DFA.accepts); decide,by (try unfold DFA.accepts); decide⟩⟩

theorem boundary_allows_earlier_source :
    Spec.boundaryRange all positive all all all all ([0,0] : Word (Fin 2)) 1 2 := by
  refine ⟨by (try unfold DFA.accepts); decide,by (try unfold DFA.accepts); decide,0,1,1,1,2,by (try unfold DFA.accepts); decide,by (try unfold DFA.accepts); decide,by (try unfold DFA.accepts); decide,by (try unfold DFA.accepts); decide,by (try unfold DFA.accepts); decide,by (try unfold DFA.accepts); decide,
    by (try unfold DFA.accepts); decide,by (try unfold DFA.accepts); decide,by (try unfold DFA.accepts); decide,by (try unfold DFA.accepts); decide,by (try unfold DFA.accepts); decide,by (try unfold DFA.accepts); decide,by (try unfold DFA.accepts); decide⟩

theorem one_use_enforces_source_lower_bound :
    ¬Spec.oneUseRange all positive all all ([0,0] : Word (Fin 2)) 1 2 := by
  rintro ⟨_,_,i,a,j,t,hli,hia,haj,hjt,htr,he,_,hB,_,_⟩
  have hpos : i<a := by
    by_cases hp : i<a
    · exact hp
    · have hi : i=a := by omega
      subst i
      rw [OuterColumn.slice_self] at hB
      exact False.elim (by simpa [DFA.accepts,DFA.run,positive] using hB)
  have hlen:=congrArg List.length he
  rw [OuterColumn.slice_length _ i a hia (by change a≤2; omega),
    OuterColumn.slice_length _ j t hjt (by change t≤2; omega)] at hlen
  omega

end REWB.ResidualSeparated.Regression
