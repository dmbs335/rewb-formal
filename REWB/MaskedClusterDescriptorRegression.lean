import REWB.MaskedClusterDescriptorAnchor

/-! Kernel regressions for the actual maintained occurrence/leader state
and cached descriptor queries. Irregular temporary components are kept
separate from complete-class arithmetic-progression interpretation. -/
namespace REWB.MaskedClusterDescriptor.Regression
open REWB.MaskedClusterLeaders REWB.MaskedRunDiscovery REWB.Periodic

private def mixedOps : List Operation := [.insert 10,.insert 0,.insert 4,.insert 2,.insert 12]
private def mixed := execute 4 4 mixedOps
private def split := execute 4 4 (mixedOps++[.lower 3])

theorem dense_components :
    (describeLeader mixed.state 16 0).1=some ⟨0,4,2,2,some 10,some 2,some 12⟩ ∧
    (describeLeader mixed.state 16 10).1=some ⟨10,12,2,1,none,some 10,none⟩ ∧
    (describeLeader mixed.state 16 2).1=none := by decide

theorem locator_endpoints_and_absent :
    (locate mixed.state 16 0).1=some 0 ∧
    (locate mixed.state 16 2).1=some 0 ∧
    (locate mixed.state 16 4).1=some 0 ∧
    (locate mixed.state 16 12).1=some 10 ∧
    (locate mixed.state 16 3).1=none ∧
    (locate mixed.state 16 16).1=none ∧
    (describe mixed.state 16 100).1=none := by decide

theorem density_split :
    (describe split.state 16 2).1=some ⟨2,2,1,0,some 4,none,some 10⟩ ∧
    (describe split.state 16 4).1=some ⟨4,4,1,0,some 10,none,some 12⟩ ∧
    (describe split.state 16 12).1=some ⟨12,12,1,0,none,none,none⟩ ∧
    (describe mixed.state 16 2).1=some ⟨0,4,2,2,some 10,some 2,some 12⟩ := by decide

theorem singleton_and_empty :
    (describe (execute 4 100 [.insert 7]).state 16 7).1=some ⟨7,7,1,0,none,none,none⟩ ∧
    (describe (execute 4 100 []).state 16 0).1=none ∧
    (describeLeader (execute 4 100 [.insert 16]).state 16 16).1=none := by decide

/-- A partial class can be irregular even when every gap is dense.
The executable fields alone are not an AP certificate. -/
theorem partial_component_is_not_assumed_ap :
    (describe (execute 4 10 [.insert 5,.insert 0,.insert 2]).state 16 2).1=
      some ⟨0,5,2,2,none,some 2,none⟩ ∧ (5:Nat)≠0+2*2 := by decide

def alternating (i : Nat) : Fin 2 := ⟨i%2,Nat.mod_lt _ (by decide)⟩
def periodicState := execute 4 4 [.insert 6,.insert 2,.insert 0,.insert 4]

theorem periodic_complete : Complete alternating 10 0 4 periodicState.state.occurrences.entries := by
  have he : periodicState.state.occurrences.entries=[0,2,4,6] := by decide
  rw [he]
  intro k
  constructor
  · intro hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl <;> exact ⟨by decide,by decide⟩
  · intro hk
    have hh:=(segment_eq_points alternating k 0 4).mp hk.2 0 (by decide)
    have hz:=congrArg Fin.val hh
    simp only [alternating,Nat.add_zero,Nat.zero_mod] at hz
    have hb:=hk.1
    have hm : k=0 ∨ k=2 ∨ k=4 ∨ k=6 := by omega
    simpa only [List.mem_cons,List.not_mem_nil,or_false] using hm

theorem complete_periodic_descriptor :
    (describe periodicState.state 16 4).1=some ⟨0,6,2,3,none,some 4,none⟩ := by decide

theorem complete_periodic_geometry :
    Geometry alternating 10 0 4 periodicState.state.occurrences.entries
      ⟨0,6,2,3,none,some 4,none⟩ := by
  have hi:= (execute_valid 4 4 [.insert 6,.insert 2,.insert 0,.insert 4]).invariant
  have hl : periodicState.length=4 := by decide
  change MaskedClusterLeaders.Invariant periodicState.length periodicState.state at hi
  rw [hl] at hi
  exact describe_geometry periodicState.state 16 4 4 hi (by decide) _ complete_periodic_descriptor
    alternating 10 0 periodic_complete (by decide)

theorem terminal_anchor_strict :
    MaskedLocalAnchor.Certificate alternating 10 0 4 periodicState.state.occurrences.entries
      6 10 (some 4) none 4 ∧ (6:Nat)<10 :=
  ⟨complete_periodic_geometry.anchor,complete_periodic_geometry.next_strict⟩

end REWB.MaskedClusterDescriptor.Regression
