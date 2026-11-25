import REWB.MaskedTraversalInitialCost
import REWB.MaskedTraversalAggregateCollect
import REWB.MaskedTraversalSuspended

namespace REWB.MaskedTraversalAnswers.Regression

def seed : State := fromBits #[true,false,false,true,false]
def added : State := push [1,4] seed

theorem seed_history : seed.history=[0,3] := by decide
theorem added_bits : added.bits=#[true,true,false,true,true] := by decide
theorem added_history : added.history=[4,1,0,3] := by decide
theorem added_count : added.count=4 := by decide
theorem added_work : added.work=seed.work+12 := by decide
theorem persistent_seed : seed.bits=#[true,false,false,true,false] := by decide
theorem no_false_growth : (push [] seed)=seed := rfl

abbrev all : DFA (Fin 1) := ⟨1,0,fun _ _=>0,fun _=>true⟩

theorem initial_terminal_empty :
    MaskedProgression.readMask
      (MaskedTraversalInitial.start all all all #[] 0 #[true] #[true] 1).answers.bits 0=true := by
  apply (MaskedTraversalInitial.start_read all all all #[] 0 #[true] #[true] 1 0).mpr
  refine ⟨by decide,Or.inl ?_⟩
  exact ⟨rfl,0,Nat.le_refl _,Nat.le_refl _,by decide,rfl,rfl⟩

theorem initial_missing_target :
    MaskedProgression.readMask
      (MaskedTraversalInitial.start all all all #[] 0 #[true] #[] 1).answers.bits 0=false := by
  cases hh : MaskedProgression.readMask
      (MaskedTraversalInitial.start all all all #[] 0 #[true] #[] 1).answers.bits 0 with
  | false=>rfl
  | true=>
    obtain ⟨_,hm⟩:=(MaskedTraversalInitial.start_read all all all #[] 0 #[true] #[] 1 0).mp hh
    have hw:=MaskedTraversalInitial.handled_sound all all all #[] 0 #[] 0 hm
    obtain ⟨a,j,t,_,_,_,_,ht,_⟩:=hw
    simp only [MaskedProgression.readMask,Array.getElem?_empty,Option.getD_none,Bool.false_eq_true] at ht

end REWB.MaskedTraversalAnswers.Regression
