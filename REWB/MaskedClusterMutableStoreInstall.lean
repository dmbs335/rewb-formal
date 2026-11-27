import REWB.MaskedClusterMutableStoreCorrect

/-! Constructing coherent owned slots by actual descriptor query and
    compilation. Successful installation stores the queried descriptor
    and exactly the returned bank. Empty and failed slots are explicit.
-/
namespace REWB.MaskedCluster.Mutable.Store
variable {α : Type} {h : Nat}

theorem empty_coherent (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (partition : MaskedClusterLeaders.State h) (capacity : Nat) (target : Array Bool)
    (sources : Batch.Sources) : Coherent C E book prepared ci ei partition capacity target (empty C E sources) := by
  intro first entry he
  simp [empty] at he

theorem set_compiled_coherent (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (partition : MaskedClusterLeaders.State h) (capacity : Nat) (target : Array Bool)
    (st : State C E) (hs : Coherent C E book prepared ci ei partition capacity target st)
    (first : Nat) (cfg : Config)
    (hd : (MaskedClusterDescriptor.describeLeader partition capacity first).1=some cfg.descriptor)
    (work rebuilds writes : Nat) :
    Coherent C E book prepared ci ei partition capacity target
      {st with
        slots:=st.slots.setIfInBounds first ((compile C E book prepared ci ei st.sources target cfg).1.map fun bank=>⟨cfg,bank⟩)
        repairWork:=work,rebuilds:=rebuilds,writes:=writes} := by
  intro other entry he
  by_cases hfo : first=other
  · subst other
    have hb:=(Array.getElem?_eq_some_iff.mp he).1
    simp only [Array.size_setIfInBounds] at hb
    rw [Array.getElem?_setIfInBounds_self_of_lt hb] at he
    cases hout : (compile C E book prepared ci ei st.sources target cfg).1 with
    | none => simp only [hout,Option.map,Option.some.injEq,reduceCtorEq] at he
    | some bank =>
      simp only [hout,Option.map,Option.some.injEq] at he
      have heq : entry=⟨cfg,bank⟩ := he.symm
      subst entry
      exact ⟨hd,hout⟩
  · rw [Array.getElem?_setIfInBounds_ne hfo] at he
    exact hs other entry he

theorem install_coherent (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (partition : MaskedClusterLeaders.State h) (capacity first L H incoming : Nat) (enabled : Bool)
    (window : SourceWindow) (runId : Option Nat) (target : Array Bool) (targetCounts : Array Nat)
    (st : State C E) (hs : Coherent C E book prepared ci ei partition capacity target st) :
    Coherent C E book prepared ci ei partition capacity target
      (install C E book prepared ci ei partition capacity first L H incoming enabled window runId target targetCounts st) := by
  cases hd : (MaskedClusterDescriptor.describeLeader partition capacity first).1 with
  | none => simpa only [install,hd,Coherent] using hs
  | some d =>
    simp only [install,hd]
    exact set_compiled_coherent C E book prepared ci ei partition capacity target st hs first _ hd _ _ _

theorem install_other (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (partition : MaskedClusterLeaders.State h) (capacity first L H incoming other : Nat) (enabled : Bool)
    (window : SourceWindow) (runId : Option Nat) (target : Array Bool) (targetCounts : Array Nat)
    (st : State C E) (hne : first≠other) :
    (install C E book prepared ci ei partition capacity first L H incoming enabled window runId target targetCounts st).slots[other]?=
      st.slots[other]? := by
  cases hd : (MaskedClusterDescriptor.describeLeader partition capacity first).1 <;>
    simp only [install,hd,Array.getElem?_setIfInBounds_ne hne]

theorem install_selected (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (partition : MaskedClusterLeaders.State h) (capacity first L H incoming : Nat) (enabled : Bool)
    (window : SourceWindow) (runId : Option Nat) (target : Array Bool) (targetCounts : Array Nat)
    (st : State C E) (d : MaskedClusterDescriptor.Descriptor)
    (hd : (MaskedClusterDescriptor.describeLeader partition capacity first).1=some d)
    (hb : first<st.slots.size) (bank : Bank C E)
    (hout : (compile C E book prepared ci ei st.sources target ⟨d,L,H,incoming,enabled,window,runId,targetCounts⟩).1=some bank) :
    (install C E book prepared ci ei partition capacity first L H incoming enabled window runId target targetCounts st).slots[first]?=
      some (some ⟨⟨d,L,H,incoming,enabled,window,runId,targetCounts⟩,bank⟩) := by
  simp only [install,hd,hout,Option.map]
  exact Array.getElem?_setIfInBounds_self_of_lt hb

end REWB.MaskedCluster.Mutable.Store
