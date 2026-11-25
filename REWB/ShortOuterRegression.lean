import REWB.ShortOuterDispatch
import REWB.ShortOuterBandRegression

namespace REWB.ShortOuter.Regression
open REWB.ShortOuter.Band.Regression

def emptyPattern : SevenDFA (Fin 2):=⟨eps,eps,eps,eps,eps,eps,eps⟩
def anyPattern : SevenDFA (Fin 2):=⟨any,any,any,any,any,any,any⟩
def gapPattern : SevenDFA (Fin 2):=⟨eps,eps,eps,eps,eps,nonempty,eps⟩
def earlierPattern : SevenDFA (Fin 2):=⟨eps,nonempty,any,eps,eps,eps,eps⟩
def earlierText : Array (Fin 2):=#[zero,one,one,one,one,zero,zero]

theorem empty_p1 : (P1.solve emptyPattern #[] zero 1).answer=true := by
  apply (P1.solve_correct emptyPattern #[] zero 1).mpr
  refine ⟨⟨0,⟨0,0,0,0,0⟩,0,?_,by decide,rfl,?_,?_⟩,by change 0-0<1; decide⟩
  · unfold P1Target.Witness P2Periodic.factor DFA.accepts
    decide
  · unfold DFA.accepts
    decide
  · unfold DFA.accepts
    decide

theorem empty_p2 : (P2.solve emptyPattern #[] zero 1).answer=true := by
  apply (P2.solve_correct emptyPattern #[] zero 1).mpr
  refine ⟨⟨0,0,0,0,0,0,0,0⟩,?_,by decide⟩
  unfold P2Periodic.Witness P2Periodic.factor DFA.accepts
  decide

theorem empty_outer_nonempty_gap_p1 : (P1.solve gapPattern #[one] zero 1).answer=true := by
  apply (P1.solve_correct gapPattern #[one] zero 1).mpr
  refine ⟨⟨0,⟨0,0,0,1,1⟩,0,?_,by decide,rfl,?_,?_⟩,by change 0-0<1; decide⟩
  · unfold P1Target.Witness P2Periodic.factor DFA.accepts
    decide
  · unfold DFA.accepts
    decide
  · unfold DFA.accepts
    decide

theorem empty_outer_nonempty_gap_p2 : (P2.solve gapPattern #[one] zero 1).answer=true := by
  apply (P2.solve_correct gapPattern #[one] zero 1).mpr
  refine ⟨⟨0,0,0,0,0,0,1,1⟩,?_,by decide⟩
  unfold P2Periodic.Witness P2Periodic.factor DFA.accepts
  decide

/-- The source is at zero, five positions before the short outer start.
A source restricted to the width-two target window would lose this hit. -/
theorem global_earlier_source : (P1.solve earlierPattern earlierText zero 2).answer=true := by
  apply (P1.solve_correct earlierPattern earlierText zero 2).mpr
  refine ⟨⟨5,⟨5,6,6,6,7⟩,0,?_,by decide,?_,?_,?_⟩,by change 6-5<2; decide⟩
  · unfold P1Target.Witness P2Periodic.factor DFA.accepts
    decide
  · decide
  · unfold DFA.accepts
    decide
  · unfold DFA.accepts
    decide

theorem p2_empty_inner : (P2.solve earlierPattern #[zero,zero] zero 2).answer=true := by
  apply (P2.solve_correct earlierPattern #[zero,zero] zero 2).mpr
  refine ⟨⟨0,1,1,1,1,1,1,2⟩,?_,by decide⟩
  unfold P2Periodic.Witness P2Periodic.factor DFA.accepts
  decide

theorem nonempty_rejects_nil : ¬nonempty.accepts [] := by unfold DFA.accepts; decide

theorem strict_limit_p1 : (P1.solve earlierPattern earlierText zero 1).answer=false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨v,hs⟩:=(P1.solve_correct earlierPattern earlierText zero 1).mp h
  obtain ⟨hpj,hjt,hte,_,_,_,_,hB,_⟩:=v.target_ok
  have hzero : v.target.t-v.target.j=0 := by omega
  change nonempty.accepts (Periodic.segment (ArrayText.read earlierText zero) v.target.j
    (v.target.t-v.target.j)) at hB
  rw [hzero] at hB
  exact nonempty_rejects_nil hB

theorem strict_limit_p2 : (P2.solve earlierPattern #[zero,zero] zero 1).answer=false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨x,hx,hs⟩:=(P2.solve_correct earlierPattern #[zero,zero] zero 1).mp h
  obtain ⟨hpi,hia,haj,hjt,hte,_,_,_,_,hB,_⟩:=hx
  have hzero : x.i-x.p=0 := by omega
  change nonempty.accepts (Periodic.segment (ArrayText.read #[zero,zero] zero) x.p (x.i-x.p)) at hB
  rw [hzero] at hB
  exact nonempty_rejects_nil hB

theorem zero_limit_p1 : (P1.solve anyPattern #[] zero 0).answer=false := P1.solve_zero_limit _ _ _
theorem zero_limit_p2 : (P2.solve anyPattern #[] zero 0).answer=false := P2.solve_zero_limit _ _ _

end REWB.ShortOuter.Regression
