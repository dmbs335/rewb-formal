import REWB.ResidualDispatchCost
import REWB.ResidualSeparatedRegression

/-! Kernel tests for actual candidate collection, generated dispatch
membership, and preservation of the earlier P1 source. -/
namespace REWB.ResidualDispatch.Regression
open REWB.RunGeometry REWB.IndexedGrid REWB.GlobalCoverage
open REWB.ResidualSeparated.Regression

theorem candidate_once :
    (select [(⟨0,6,1⟩,(2,1)),(⟨0,6,1⟩,(7,1))]).windows=[⟨2,3,1⟩] ∧
    (select [(⟨0,6,1⟩,(2,1)),(⟨0,6,1⟩,(7,1))]).count=1 := by decide

theorem concrete_rows :
    (lowRows 1 [⟨0,3,1⟩]).1=[(⟨0,3,1⟩,(0,1)),(⟨0,3,1⟩,(1,1)),(⟨0,3,1⟩,(2,1))] ∧
    (largeRows 1 [⟨0,3,1⟩]).1=[] := by decide

private def text : Nat→Fin 2 := fun _=>0

private theorem earlier_window : (⟨1,2,1⟩ : Strip)∈(prepare text 3 1 1 1 0).windows := by
  let R : Strip:=⟨0,2,1⟩
  have hv : MaximalStrip text 3 R.lo R.hi R.distance :=
    ⟨by decide,by decide,by decide,by intro i _ _; rfl,Or.inl rfl,Or.inl rfl⟩
  have hg:=ResidualStripSchedule.generate_maximal text 3 1 1 R (by decide) (by decide) hv (by decide)
  have hr:=(ResidualStripSchedule.generate_mem text 3 1 1 R).mp hg |>.1
  obtain ⟨W,hW,hl,hr,hq⟩:=ResidualStripSchedule.prepare_existing_cut text 3 1 1 1 R 1 2 2
    hr (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hw:=(ResidualStripSchedule.prepare_sound text 3 1 1 1 W hW).2.2
  have hs:=hw.separated
  have he : stripWindow W=(⟨1,2,1⟩ : Strip) := by
    have hdist : W.distance=1 := hq
    have hleft : W.left=1 := by omega
    have hright : W.right=2 := by omega
    simp only [stripWindow,hleft,hright,hdist]
  exact (prepare_mem text 3 1 1 1 0 _).mpr (Or.inl ⟨W,hW,he⟩)

theorem earlier_source_dispatched :
    ∃c,c∈(prepare text 3 1 1 1 0).windows ∧ c.lo=1 ∧
      P1Query p1 (Periodic.segment text 0 3) c := by
  refine ⟨⟨1,2,1⟩,earlier_window,rfl,?_⟩
  exact earlier_source_outside_strip

theorem earlier_source_match : MatchesWithin p1.nested1 (Periodic.segment text 0 3) 2 := by
  obtain ⟨c,hc,_,hq⟩:=earlier_source_dispatched
  exact scheduled_p1_sound p1 text 3 1 1 1 0 c hc hq

theorem empty_dispatch :
    MatchesWithin (⟨all,all,all,all,all,all,all⟩ : SevenDFA (Fin 2)).nested2 [] 2 ↔
      (SmallPeriodP2.solve (⟨all,all,all,all,all,all,all⟩ : SevenDFA (Fin 2)) text 0 0).accepted=true ∨
      ShortP2 (⟨all,all,all,all,all,all,all⟩ : SevenDFA (Fin 2)) text 0 1 ∨
      ∃c,c∈(prepare text 0 1 1 1 0).windows ∧
        P2Query (⟨all,all,all,all,all,all,all⟩ : SevenDFA (Fin 2)) [] c :=
  p2_dispatch_iff _ text 0 1 1 1 0 (by decide) (by decide) (by decide) (by decide)

end REWB.ResidualDispatch.Regression
