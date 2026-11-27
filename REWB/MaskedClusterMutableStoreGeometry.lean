import REWB.MaskedClusterMutableStoreCost

/-! The cost preconditions are obtained from the actual descriptor at
    an H=L reset. Source erasure then preserves the fixed configurations
    and their geometry. Choosing a global traversal/reset schedule and
    its incoming cursor remains a separate obligation.
-/
namespace REWB.MaskedCluster.Mutable.Store
variable {α : Type} {h : Nat}

theorem Geometry.reset (f : Nat→α) (n base L : Nat) (xs : List Nat)
    (d : MaskedClusterDescriptor.Descriptor) (hg : MaskedClusterDescriptor.Geometry f n base L xs d)
    (incoming : Nat) (enabled : Bool) (window : SourceWindow) (runId : Option Nat) (targetCounts : Array Nat)
    (hin : enabled=true→d.first<incoming ∧ incoming≤if d.repetitions=0 then d.nextAt n else d.first+d.period) :
    Geometry ⟨d,L,L,incoming,enabled,window,runId,targetCounts⟩ n := by
  refine ⟨Nat.le_refl _,?_,?_,?_,hg.next_bound,?_,hin⟩
  · intro hm
    change d.repetitions≠0 at hm
    have hd:=(hg.dense (by omega)).1
    change d.period≤L
    omega
  · intro hm
    change d.repetitions≠0 at hm
    have hp:=(hg.dense (by omega)).2.2
    exact hg.anchor.previousSafe _ hp
  · change d.first+d.repetitions*d.period<d.nextAt n
    rw [←hg.endpoint]
    exact hg.next_strict
  · change d.first+d.repetitions*d.period+L≤n
    rw [←hg.endpoint]
    exact hg.anchor.lastBound

theorem describe_reset_geometry (partition : MaskedClusterLeaders.State h) (capacity L first : Nat)
    (hi : MaskedClusterLeaders.Invariant L partition) (hc : capacity=2^h)
    (d : MaskedClusterDescriptor.Descriptor)
    (hd : (MaskedClusterDescriptor.describeLeader partition capacity first).1=some d)
    (f : Nat→α) (n base : Nat) (hfull : MaskedRunDiscovery.Complete f n base L partition.occurrences.entries)
    (hL : 0<L) (incoming : Nat) (enabled : Bool) (window : SourceWindow) (runId : Option Nat) (targetCounts : Array Nat)
    (hin : enabled=true→d.first<incoming ∧ incoming≤if d.repetitions=0 then d.nextAt n else d.first+d.period) :
    Geometry ⟨d,L,L,incoming,enabled,window,runId,targetCounts⟩ n :=
  Geometry.reset f n base L partition.occurrences.entries d
    (MaskedClusterDescriptor.describeLeader_geometry partition capacity L first hi hc d hd f n base hfull hL)
    incoming enabled window runId targetCounts hin

theorem eraseSource_geometry (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (partition : MaskedClusterLeaders.State h) (capacity : Nat) (target : Array Bool) (p n : Nat) (st : State C E)
    (hg : ∀(first : Nat) (entry : Entry C E),st.slots[first]?=some (some entry)→Geometry entry.config n) :
    ∀(first : Nat) (entry : Entry C E),
      (eraseSource C E book prepared ci ei partition capacity target p st).slots[first]?=some (some entry)→Geometry entry.config n := by
  intro first entry he
  by_cases ho : (MaskedClusterDescriptor.locate partition capacity p).1=some first
  · let mid : State C E := {st with
      sources:=MaskedMutableProgression.Batch.eraseSource p st.sources
      repairWork:=st.repairWork+(MaskedClusterDescriptor.locate partition capacity p).2+2}
    have hh : (rebuild C E book prepared ci ei target first mid).slots[first]?=some (some entry) := by
      simpa only [eraseSource,ho] using he
    obtain ⟨old,hold,heq,_⟩:=rebuild_selected C E book prepared ci ei target first mid entry hh
    rw [heq]
    exact hg first old hold
  · rw [eraseSource_other C E book prepared ci ei partition capacity target p first st ho] at he
    exact hg first entry he

end REWB.MaskedCluster.Mutable.Store
