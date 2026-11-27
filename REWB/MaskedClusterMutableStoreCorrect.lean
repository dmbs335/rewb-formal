import REWB.MaskedClusterMutableStore

/-! Exact one-slot repair for a fixed complete occurrence class. The
    affected slot comes from the actual leader query. Descriptor AP
    completeness excludes every candidate of every other slot, including
    when the deleted point is a non-occurrence inside a cluster hull.
    All finite replay entries remain current; target eligibility is fixed.
-/
namespace REWB.MaskedCluster.Mutable.Store
variable {α : Type} {h : Nat}

theorem compile_presence_erase (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (source : Array Bool) (removed : List Nat) (sources : Batch.Sources)
    (hv : MaskedMutableProgression.Batch.Valid source removed sources)
    (target : Array Bool) (cfg : Config) (p : Nat) :
    (compile C E book prepared ci ei (MaskedMutableProgression.Batch.eraseSource p sources) target cfg).1.isSome=
      (compile C E book prepared ci ei sources target cfg).1.isSome := by
  have hv':=MaskedMutableProgression.Batch.eraseSource_valid hv p
  unfold compile
  by_cases hm : cfg.descriptor.repetitions=0
  · simp only [hm,if_true,Option.isSome_some]
  · simp only [hm,if_false,MaskedMutableProgression.Batch.eraseSource_runs,MaskedMutableProgression.Batch.eraseSource_n]
    cases hid : cfg.runId with
    | none => rfl
    | some id =>
      simp only
      cases hR : sources.runs[id]? with
      | none => simp only [hR]
      | some R =>
        simp only [hR]
        obtain ⟨a,ha,_⟩:=hv.rows id R hR
        obtain ⟨b,hb,_⟩:=hv'.rows id R hR
        by_cases hc : R.period=cfg.descriptor.period ∧ R.lo≤cfg.descriptor.first ∧ cfg.descriptor.last+cfg.anchor≤R.hi+1
        · by_cases hK : sources.modulus=prepared.K
          · simp only [hc,if_true,Batch.compileRun,MaskedMutableProgression.Batch.eraseSource_modulus,
              MaskedMutableProgression.Batch.eraseSource_runs,hR,ha,hb,hK,Option.isSome_some,true_and]
          · simp only [hc,if_true,Batch.compileRun,MaskedMutableProgression.Batch.eraseSource_modulus,hK,if_false]
        · simp only [hc,if_false]

theorem rebuild_selected (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (target : Array Bool) (first : Nat) (st : State C E) (entry : Entry C E)
    (he : (rebuild C E book prepared ci ei target first st).slots[first]?=some (some entry)) :
    ∃old,st.slots[first]?=some (some old) ∧ entry.config=old.config ∧
      (compile C E book prepared ci ei st.sources target entry.config).1=some entry.bank := by
  cases hs : st.slots[first]? with
  | none => simp only [rebuild,hs,reduceCtorEq] at he
  | some slot =>
    cases slot with
    | none => simp only [rebuild,hs,Option.some.injEq,reduceCtorEq] at he
    | some old =>
      have hb:=(Array.getElem?_eq_some_iff.mp hs).1
      simp only [rebuild,hs] at he
      rw [Array.getElem?_setIfInBounds_self_of_lt hb] at he
      cases hout : (compile C E book prepared ci ei st.sources target old.config).1 with
      | none => simp only [hout,Option.map,Option.some.injEq,reduceCtorEq] at he
      | some bank =>
        simp only [hout,Option.map,Option.some.injEq] at he
        have hentry : entry=⟨old.config,bank⟩ := he.symm
        subst entry
        exact ⟨old,rfl,rfl,hout⟩

theorem erased_other_compile (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (partition : MaskedClusterLeaders.State h) (capacity L : Nat)
    (hi : MaskedClusterLeaders.Invariant L partition) (hc : capacity=2^h)
    (f : Nat→α) (n base : Nat) (hfull : MaskedRunDiscovery.Complete f n base L partition.occurrences.entries)
    (source : Array Bool) (removed : List Nat) (sources : Batch.Sources)
    (hv : MaskedMutableProgression.Batch.Valid source removed sources) (target : Array Bool)
    (first : Nat) (cfg : Config)
    (hd : (MaskedClusterDescriptor.describeLeader partition capacity first).1=some cfg.descriptor)
    (p : Nat) (hne : (MaskedClusterDescriptor.locate partition capacity p).1≠some first) :
    (compile C E book prepared ci ei (MaskedMutableProgression.Batch.eraseSource p sources) target cfg).1=
      (compile C E book prepared ci ei sources target cfg).1 := by
  apply compile_erase C E book prepared ci ei source removed sources hv target cfg p
  intro hp
  obtain ⟨_,hs⟩:=MaskedClusterDescriptor.describeLeader_sound partition capacity L first hi hc cfg.descriptor hd
  have hap:=hs.progression partition capacity L hi hc cfg.descriptor f n base hfull
  have hmem:=(hap.2.2 p).mpr hp
  have ho:=MaskedClusterDescriptor.locate_descriptor partition capacity L first hi hc cfg.descriptor hd p
    hmem.1 hmem.2.1 hmem.2.2
  exact False.elim (hne ho)

theorem eraseSource_coherent (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (partition : MaskedClusterLeaders.State h) (capacity L : Nat)
    (hi : MaskedClusterLeaders.Invariant L partition) (hc : capacity=2^h)
    (f : Nat→α) (n base : Nat) (hfull : MaskedRunDiscovery.Complete f n base L partition.occurrences.entries)
    (source : Array Bool) (removed : List Nat) (target : Array Bool) (p : Nat) (st : State C E)
    (hv : MaskedMutableProgression.Batch.Valid source removed st.sources)
    (hs : Coherent C E book prepared ci ei partition capacity target st) :
    Coherent C E book prepared ci ei partition capacity target
      (eraseSource C E book prepared ci ei partition capacity target p st) := by
  intro first entry he
  by_cases ho : (MaskedClusterDescriptor.locate partition capacity p).1=some first
  · let mid : State C E := {st with
      sources:=MaskedMutableProgression.Batch.eraseSource p st.sources
      repairWork:=st.repairWork+(MaskedClusterDescriptor.locate partition capacity p).2+2}
    have hh : (rebuild C E book prepared ci ei target first mid).slots[first]?=some (some entry) := by
      simpa only [eraseSource,ho] using he
    obtain ⟨old,hold,heq,hcur⟩:=rebuild_selected C E book prepared ci ei target first mid entry hh
    have hcanon:=(hs first old hold).1
    refine ⟨?_,?_⟩
    · rw [heq]
      exact hcanon
    · rw [eraseSource_sources]
      exact hcur
  · have heold : st.slots[first]?=some (some entry) := by
      rw [eraseSource_other C E book prepared ci ei partition capacity target p first st ho] at he
      exact he
    obtain ⟨hd,hcurrent⟩:=hs first entry heold
    refine ⟨hd,?_⟩
    rw [eraseSource_sources,erased_other_compile C E book prepared ci ei partition capacity L hi hc f n base hfull
      source removed st.sources hv target first entry.config hd p ho]
    exact hcurrent

theorem rebuild_present (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (target : Array Bool) (first : Nat) (st : State C E) (old : Entry C E)
    (hs : st.slots[first]?=some (some old))
    (hp : (compile C E book prepared ci ei st.sources target old.config).1.isSome=true) :
    ∃entry,(rebuild C E book prepared ci ei target first st).slots[first]?=some (some entry) := by
  have hb:=(Array.getElem?_eq_some_iff.mp hs).1
  cases hout : (compile C E book prepared ci ei st.sources target old.config).1 with
  | none => simp only [hout,Option.isSome_none,Bool.false_eq_true] at hp
  | some bank =>
    refine ⟨⟨old.config,bank⟩,?_⟩
    simp only [rebuild,hs,hout,Option.map_some]
    exact Array.getElem?_setIfInBounds_self_of_lt hb

theorem eraseSource_complete (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (partition : MaskedClusterLeaders.State h) (capacity : Nat)
    (source : Array Bool) (removed : List Nat) (target : Array Bool) (p : Nat) (st : State C E)
    (hv : MaskedMutableProgression.Batch.Valid source removed st.sources)
    (hs : Coherent C E book prepared ci ei partition capacity target st) (hall : Complete C E partition st) :
    Complete C E partition (eraseSource C E book prepared ci ei partition capacity target p st) := by
  intro first hf
  obtain ⟨old,hold⟩:=hall first hf
  by_cases ho : (MaskedClusterDescriptor.locate partition capacity p).1=some first
  · have hc:=(hs first old hold).2
    have hp : (compile C E book prepared ci ei (MaskedMutableProgression.Batch.eraseSource p st.sources) target old.config).1.isSome=true := by
      rw [compile_presence_erase C E book prepared ci ei source removed st.sources hv target old.config p,hc]
      rfl
    let mid : State C E := {st with
      sources:=MaskedMutableProgression.Batch.eraseSource p st.sources
      repairWork:=st.repairWork+(MaskedClusterDescriptor.locate partition capacity p).2+2}
    have hh:=rebuild_present C E book prepared ci ei target first mid old hold hp
    simpa only [eraseSource,ho] using hh
  · refine ⟨old,?_⟩
    rw [eraseSource_other C E book prepared ci ei partition capacity target p first st ho]
    exact hold

end REWB.MaskedCluster.Mutable.Store
