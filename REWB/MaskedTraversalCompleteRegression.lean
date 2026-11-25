import REWB.MaskedTraversalCompleteCorrect

namespace REWB.MaskedTraversalComplete.Regression
open REWB.Spec REWB.MaskedCluster REWB.MaskedTraversalAggregate REWB.MaskedClusterDescriptor

abbrev all : DFA (Fin 2) := ⟨1,0,fun _ _=>0,fun _=>true⟩

def word : Word (Fin 2) := [0,1,0,0,1,0,1,0,0,1,0,0,1,0]

def partition : MaskedClusterLeaders.State 4 :=
  (MaskedClusterLeaders.execute 4 6 [.insert 8,.insert 5,.insert 0]).state

def sourceDescriptor : Descriptor := ⟨0,0,1,0,some 5,none,some 8⟩
def targetDescriptor : Descriptor := ⟨5,8,3,1,none,some 5,none⟩

theorem actual_descriptors :
    (describeLeader partition 16 0).1=some sourceDescriptor ∧
      (describeLeader partition 16 5).1=some targetDescriptor := by decide

theorem actual_enabled_incoming :
    (MaskedTraversalBankReady.incoming partition 16 5 6 (Array.replicate 15 (some 6))).cursor=6 ∧
      (MaskedTraversalBankReady.incoming partition 16 5 6 (Array.replicate 15 (some 6))).enabled=true := by decide

def sourcePart : Part := ⟨⟨sourceDescriptor,6,6,0,false,⟨true,0,15⟩,none,#[]⟩,true⟩
def targetPart : Part := ⟨⟨targetDescriptor,6,6,6,true,⟨true,0,15⟩,none,#[]⟩,true⟩

def source : Array Bool := #[true,false,false,false,false,false,false,false,false,false,false,false,false,false,false]
def target : Array Bool := #[false,false,false,false,false,false,false,false,true,false,false,false,false,false,false]

theorem overshoot_skips_first_target :
    jumpMode word.length 6 sourcePart 0=true ∧
      ¬(position sourcePart 0+6≤position targetPart 0) ∧
      targetPart.input true≤position targetPart 1 := by decide

theorem actual_distinct_owners :
    (locate partition 16 0).1=some 0 ∧ (locate partition 16 8).1=some 5 := by decide

theorem immediate_dense_target_path :
    PhysicalChain all all word 6 source [] target [sourcePart,targetPart]
      (stageCode all all false .waiting) (stageCode all all false (.suffix 0)) := by
  have continuous : Continuous word.length [sourcePart,targetPart] sourcePart.input (targetPart.output word.length) :=
    Continuous.cons _ _ _ _ (fun _ _=>rfl)
      (Continuous.cons _ _ _ _ (by intro mode hm; cases mode <;> rfl) (Continuous.nil _))
  have safe : ∀p,p∈[sourcePart,targetPart]→Safe word.length 6 p := by
    intro p hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl <;> unfold Safe <;> decide
  have enabled : Enabled word.length [sourcePart,targetPart] := by
    refine ⟨?_,?_,True.intro⟩
    · intro q he _
      have hq : targetPart=q := Option.some.inj he
      subst q
      rfl
    · intro q he; cases he
  have hh:=two_jumps all all word 6 source [] target [] [] [] sourcePart targetPart 0 1
    sourcePart.input (targetPart.output word.length) continuous (by decide) safe enabled
    (by intro _; constructor <;> decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by change true=true; rfl)
  exact hh

theorem empty_path_rejects :
    ¬PhysicalChain all all word 6 source [] target []
      (stageCode all all false .waiting) (stageCode all all false (.suffix 0)) := by
  change stageCode all all false .waiting≠stageCode all all false (.suffix 0)
  decide

end REWB.MaskedTraversalComplete.Regression
