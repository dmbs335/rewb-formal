import REWB.OneUseRangeBorderPartition

namespace REWB.OneUseRange.Border.Regression
open REWB.Spec

def all : DFA (Fin 2) := ⟨1,0,fun _ _=>0,fun _=>true⟩
def positive : DFA (Fin 2) := ⟨2,0,fun _ _=>1,fun q=>decide (q=1)⟩
def epsilon : DFA (Fin 2) := ⟨2,0,fun _ _=>1,fun q=>decide (q=0)⟩
def reset : DFA (Fin 2) := ⟨2,0,fun _ c=>c,fun q=>decide (q=1)⟩

theorem lower_bound_preserved :
    (query (build all positive all all ([0,0] : Word (Fin 2)) 0) 1 2 2 1).1=false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨i,t,h,_,_⟩:=(query_correct all positive all all ([0,0] : Word (Fin 2)) 0 1 2 2 1 (by decide)).mp h
  rcases h with ⟨hli,_,htr,_,_,L,hLen,_,hB,_⟩
  have hz : L=0 := by omega
  subst L
  simp only [Nat.add_zero,OuterColumn.slice_self] at hB
  exact Bool.noConfusion hB

theorem common_midpoint_state :
    (inner (build all positive positive all ([0,0] : Word (Fin 2)) 0) ⟨0,by decide⟩ 2).1=false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨L,hLen,_,hB,hC⟩:=(inner_correct all positive positive all ([0,0] : Word (Fin 2)) 0
    ⟨0,by decide⟩ 2 (by decide) (by decide)).mp h
  by_cases hz : L=0
  · subst L
    simp only [Nat.add_zero,OuterColumn.slice_self] at hB
    exact Bool.noConfusion hB
  · have h1 : L=1 := by omega
    subst L
    change positive.accepts [] at hC
    exact Bool.noConfusion hC

theorem odd_midpoint_positive :
    (query (build all positive positive all ([0,1,1,1,0] : Word (Fin 2)) 0) 0 5 1 4).1=true := by
  apply (query_correct all positive positive all _ 0 0 5 1 4 (by decide)).mpr
  refine ⟨0,5,?_,by decide,by decide⟩
  refine ⟨by decide,by decide,by decide,by rfl,by rfl,1,by decide,?_,?_,?_⟩ <;> rfl

theorem reset_gap_positive :
    (query (build all positive reset all ([0,1,0] : Word (Fin 2)) 0) 0 3 1 2).1=true := by
  apply (query_correct all positive reset all _ 0 0 3 1 2 (by decide)).mpr
  refine ⟨0,3,?_,by decide,by decide⟩
  refine ⟨by decide,by decide,by decide,by rfl,by rfl,1,by decide,?_,?_,?_⟩ <;> rfl

theorem empty_at_terminal :
    (queryAt (build all epsilon all all ([1] : Word (Fin 2)) 0) 1 1 1 1).1=true := by
  apply (queryAt_correct all epsilon all all _ 0 1 1 1 1 (by decide)).mpr
  refine ⟨by decide,by decide,by decide,by rfl,by rfl,0,by decide,?_,?_,?_⟩ <;> rfl

theorem empty_input :
    query (build all all all all ([] : Word (Fin 2)) 0) 0 0 0 0=(false,1) := rfl

theorem stop_shares_tree (w : Word (Fin 2)) (q : Fin reset.stateCount) :
    (stopRanges reset (BoundaryApplication.Range.build reset w) q).tree=
      (BoundaryApplication.Range.build reset w).tree := rfl

end REWB.OneUseRange.Border.Regression
