import REWB.MaskedTraversalPeriodicCoverage

namespace REWB.MaskedTraversalPeriodicCoverage.Regression
open REWB.Spec REWB.MaskedClusterDescriptor REWB.MaskedRunDiscovery REWB.MaskedProgression

abbrev all : DFA (Fin 1) := ⟨1,0,fun _ _=>0,fun _=>true⟩
def text : Array (Fin 1) := #[0,0,0,0,0,0]
def source : Array Bool := #[false,true,false,false,false,false,false]
def target : Array Bool := #[false,false,false,true,false,false,false]
def operations : List MaskedClusterLeaders.Operation := [.insert 4,.insert 3,.insert 2,.insert 1,.insert 0]
def partition : MaskedClusterLeaders.State 3 := (MaskedClusterLeaders.execute 3 2 operations).state

theorem actual_invariant : MaskedClusterLeaders.Invariant 2 partition :=
  (MaskedClusterLeaders.execute_valid 3 2 operations).invariant

theorem actual_complete : Complete (ArrayText.read text 0) text.size 0 2 partition.occurrences.entries := by
  have he : partition.occurrences.entries=[0,1,2,3,4] := by decide
  intro p
  rw [he]
  constructor
  · intro hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl <;> unfold Occurs <;> decide
  · intro hp
    have hb : p+2≤6 := hp.1
    have hh : p=0 ∨ p=1 ∨ p=2 ∨ p=3 ∨ p=4 := by omega
    rcases hh with rfl|rfl|rfl|rfl|rfl <;> decide

theorem actual_same_owner : (locate partition 8 1).1=(locate partition 8 3).1 := by decide

theorem enumerated_pair :
    ∃R : RunGeometry.Bounds,∃k : Nat,R∈(MaskedOrdered.Owner.enumerateAuto text 0).runs ∧
      R.Valid (ArrayText.read text 0) text.size ∧ R.lo≤1 ∧ 2*R.period≤2 ∧ 3=1+k*R.period ∧ 3+2≤R.hi :=
  same_owner_run text 0 partition 8 0 2 1 3 actual_invariant (by decide) actual_complete
    (by decide) (by decide) (by decide) actual_same_owner (by decide)

theorem actual_periodic_hit :
    readMask (MaskedPeriodic.Batch.solve all all all text 0 source target).output.hits 1=true :=
  same_owner_hit all all all text 0 source target partition 8 0 2 1 3 actual_invariant (by decide) actual_complete
    (by decide) (by decide) (by decide) actual_same_owner (by decide) rfl rfl rfl rfl rfl

theorem original_cut_partition :
    readMask (MaskedPeriodic.Batch.solve all all all text 0 source target).output.hits 1=true ∨
      MaskedTraversalComplete.BandGood all all all text.toList partition 8 2 2 source [] target 1 :=
  original_partition all all all text 0 source target [] partition 8 0 2 2 1 3 3 5
    actual_invariant (by decide) actual_complete (by decide) (by decide) rfl (by decide)
    (by decide) (by decide) (by decide) (by decide) rfl rfl rfl rfl rfl

end REWB.MaskedTraversalPeriodicCoverage.Regression
