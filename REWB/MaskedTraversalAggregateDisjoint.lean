import REWB.MaskedTraversalAggregateEraseMany

/-! A suspended sibling frontier stays coherent when an active disjoint
frontier reports sources. The actual mutable run indexes may change, but
all candidate source positions of a saved bank belong to its own complete
occurrence class. Its exact compiled table is therefore unchanged. Raw
slots are preserved because actual repairs write only active leaders.
No suspended bank or leaf list is traversed by the executable operation.
-/
namespace REWB.MaskedTraversalAggregate.Cells
open REWB.MaskedCluster REWB.MaskedFiniteAction
variable {α : Type} {C E : DFA α} {h g : Nat}

theorem locate_absent (partition : MaskedClusterLeaders.State h) (capacity L p : Nat)
    (hi : MaskedClusterLeaders.Invariant L partition) (hc : capacity=2^h)
    (hp : p∉partition.occurrences.entries) :
    (MaskedClusterDescriptor.locate partition capacity p).1=none := by
  cases ho : (MaskedClusterDescriptor.locate partition capacity p).1 with
  | none=>rfl
  | some first=>
    have hh:=((MaskedClusterDescriptor.locate_correct partition capacity L p first hi hc).mp ho).1
    exact False.elim (hp hh)

theorem erased_absent_compile (env : Clip.Env C E) (sources : Mutable.Batch.Sources)
    (partition : MaskedClusterLeaders.State h) (capacity old first p : Nat) (cfg : Mutable.Store.Config)
    (hi : MaskedClusterLeaders.Invariant old partition) (hc : capacity=2^h)
    (f : Nat→α) (n base : Nat) (hfull : MaskedRunDiscovery.Complete f n base old partition.occurrences.entries)
    (source : Array Bool) (removed : List Nat) (hv : MaskedMutableProgression.Batch.Valid source removed sources)
    (hd : (MaskedClusterDescriptor.describeLeader partition capacity first).1=some cfg.descriptor)
    (hp : p∉partition.occurrences.entries) :
    (Mutable.Store.compile C E env.book env.prepared env.cRanges env.eRanges
      (MaskedMutableProgression.Batch.eraseSource p sources) env.target cfg).1=
    (Mutable.Store.compile C E env.book env.prepared env.cRanges env.eRanges sources env.target cfg).1 := by
  apply Mutable.Store.erased_other_compile C E env.book env.prepared env.cRanges env.eRanges
    partition capacity old hi hc f n base hfull source removed sources hv env.target first cfg hd p
  rw [locate_absent partition capacity old p hi hc hp]
  exact Option.noConfusion

theorem eraseMany_absent_compile (env : Clip.Env C E) (sources : Mutable.Batch.Sources)
    (partition : MaskedClusterLeaders.State h) (capacity old first : Nat) (cfg : Mutable.Store.Config)
    (hi : MaskedClusterLeaders.Invariant old partition) (hc : capacity=2^h)
    (f : Nat→α) (n base : Nat) (hfull : MaskedRunDiscovery.Complete f n base old partition.occurrences.entries)
    (source : Array Bool) (removed positions : List Nat) (hv : MaskedMutableProgression.Batch.Valid source removed sources)
    (hd : (MaskedClusterDescriptor.describeLeader partition capacity first).1=some cfg.descriptor)
    (hp : ∀p,p∈positions→p∉partition.occurrences.entries) :
    (Mutable.Store.compile C E env.book env.prepared env.cRanges env.eRanges
      (MaskedMutableProgression.Batch.eraseMany positions sources) env.target cfg).1=
    (Mutable.Store.compile C E env.book env.prepared env.cRanges env.eRanges sources env.target cfg).1 := by
  induction positions generalizing sources removed with
  | nil=>rfl
  | cons p ps ih=>
    change (Mutable.Store.compile C E env.book env.prepared env.cRanges env.eRanges
      (MaskedMutableProgression.Batch.eraseMany ps (MaskedMutableProgression.Batch.eraseSource p sources)) env.target cfg).1=_
    rw [ih _ (p::removed) (MaskedMutableProgression.Batch.eraseSource_valid hv p)
      (fun q hq=>hp q (List.mem_cons_of_mem p hq))]
    exact erased_absent_compile env sources partition capacity old first p cfg hi hc f n base hfull source removed hv hd
      (hp p List.mem_cons_self)

theorem eraseMany_other (env : Clip.Env C E) (partition : MaskedClusterLeaders.State h)
    (capacity old first : Nat) (positions : List Nat) (st : Mutable.Store.State C E) (tree : BankTree C E h)
    (hp : ∀p,p∈positions→(MaskedClusterDescriptor.locate partition capacity p).1≠some first) :
    (eraseMany env partition capacity old positions st tree).store.slots[first]?=st.slots[first]? := by
  have go : ∀ps : List Nat,(∀p,p∈ps→(MaskedClusterDescriptor.locate partition capacity p).1≠some first)→
      ∀acc : SourceChange C E h,(ps.foldl (eraseStep env partition capacity old) acc).store.slots[first]?=acc.store.slots[first]? := by
    intro ps
    induction ps with
    | nil=>intro _ acc; rfl
    | cons p ps ih=>
      intro hps acc
      rw [List.foldl_cons,ih (fun q hq=>hps q (List.mem_cons_of_mem p hq))]
      exact eraseCurrent_other env partition capacity old p first acc.store acc.tree (hps p List.mem_cons_self)
  exact go positions hp ⟨st,tree,true,0,0⟩

theorem Coherent.transport_erases (env : Clip.Env C E) (st next : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity old : Nat)
    (entries : List (Option (Mutable.Store.Entry C E))) (coherent : Coherent env st partition capacity old entries)
    (hi : MaskedClusterLeaders.Invariant old partition) (hc : capacity=2^h)
    (f : Nat→α) (n base : Nat) (hfull : MaskedRunDiscovery.Complete f n base old partition.occurrences.entries)
    (source : Array Bool) (removed positions : List Nat) (hv : MaskedMutableProgression.Batch.Valid source removed st.sources)
    (hp : ∀p,p∈positions→p∉partition.occurrences.entries)
    (hs : next.sources=MaskedMutableProgression.Batch.eraseMany positions st.sources)
    (hslots : ∀first,first∈partition.leaders.entries→next.slots[first]?=st.slots[first]?) :
    Coherent env next partition capacity old entries := by
  intro first entry he
  have hh:=coherent first entry he
  have hd:=MaskedClusterDescriptor.describeLeader_sound partition capacity old first hi hc entry.config.descriptor hh.descriptor
  have hleader : first∈partition.leaders.entries := by simpa only [hd.1] using hd.2.firstLeader
  refine ⟨hh.descriptor,hh.current,?_,?_⟩
  · change (Mutable.Store.compile C E env.book env.prepared env.cRanges env.eRanges next.sources env.target entry.config).1=some entry.bank
    rw [hs,eraseMany_absent_compile env st.sources partition capacity old first entry.config hi hc f n base hfull
      source removed positions hv hh.descriptor hp]
    exact hh.compiled
  · obtain ⟨before,hbefore,hcfg⟩:=hh.raw
    exact ⟨before,by rw [hslots first hleader]; exact hbefore,hcfg⟩

theorem LinkedEntries.transport_runs (env : Clip.Env C E) (st next : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity old : Nat) (anchors : Array (Option Nat))
    (entries : List (Option (Mutable.Store.Entry C E))) (linked : LinkedEntries env st partition capacity old anchors entries)
    (hs : next.sources.runs=st.sources.runs) : LinkedEntries env next partition capacity old anchors entries := by
  intro first entry he
  have hh:=linked first entry he
  refine ⟨hh.anchor,hh.incoming,hh.enabled,?_⟩
  simpa only [MaskedTraversalContext.RunBacked,hs] using hh.run

theorem Maintained.transport_erases (env : Clip.Env C E) (st next : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity old n : Nat) (anchors : Array (Option Nat))
    (source : Array Bool) (removed positions : List Nat) (tree : BankTree C E h)
    (hm : Maintained env partition capacity old n anchors source removed st tree)
    (hi : MaskedClusterLeaders.Invariant old partition) (hc : capacity=2^h)
    (f : Nat→α) (base : Nat) (hfull : MaskedRunDiscovery.Complete f n base old partition.occurrences.entries)
    (hp : ∀p,p∈positions→p∉partition.occurrences.entries)
    (hs : next.sources=MaskedMutableProgression.Batch.eraseMany positions st.sources)
    (hslots : ∀first,first∈partition.leaders.entries→next.slots[first]?=st.slots[first]?) :
    Maintained env partition capacity old n anchors source (positions.reverse++removed) next tree := by
  obtain ⟨hv,hn,hK,hg,entries,hr,hco,hcp,hl,hu⟩:=hm
  refine ⟨?_,?_,?_,hg,entries,hr,?_,hcp,?_,hu⟩
  · rw [hs]
    exact MaskedMutableProgression.Batch.eraseMany_valid_reverse hv positions
  · rw [hs,MaskedMutableProgression.Batch.eraseMany_n,hn]
  · rw [hs,MaskedMutableProgression.Batch.eraseMany_modulus,hK]
  · exact Coherent.transport_erases env st next partition capacity old entries hco hi hc f n base hfull source removed positions hv hp hs hslots
  · apply LinkedEntries.transport_runs env st next partition capacity old anchors entries hl
    rw [hs,MaskedMutableProgression.Batch.eraseMany_runs]

theorem eraseMany_disjoint_slots (env : Clip.Env C E) (active : MaskedClusterLeaders.State g)
    (activeCapacity activeOld : Nat) (saved : MaskedClusterLeaders.State h) (savedOld first : Nat)
    (positions : List Nat) (st : Mutable.Store.State C E) (tree : BankTree C E g)
    (hai : MaskedClusterLeaders.Invariant activeOld active) (hac : activeCapacity=2^g)
    (hsi : MaskedClusterLeaders.Invariant savedOld saved) (hf : first∈saved.leaders.entries)
    (disjoint : ∀p,p∈active.occurrences.entries→p∉saved.occurrences.entries) :
    (eraseMany env active activeCapacity activeOld positions st tree).store.slots[first]?=st.slots[first]? := by
  apply eraseMany_other env active activeCapacity activeOld first positions st tree
  intro p _ ho
  have hh:=((MaskedClusterDescriptor.locate_correct active activeCapacity activeOld p first hai hac).mp ho).2.1
  exact disjoint first ((hai.represented first).mp hh).1 ((hsi.represented first).mp hf).1

theorem eraseMany_disjoint_maintained (env : Clip.Env C E) (active : MaskedClusterLeaders.State g)
    (activeCapacity activeOld : Nat) (activeTree : BankTree C E g)
    (saved : MaskedClusterLeaders.State h) (savedCapacity savedOld n : Nat) (anchors : Array (Option Nat))
    (source : Array Bool) (removed positions : List Nat) (st : Mutable.Store.State C E) (savedTree : BankTree C E h)
    (hm : Maintained env saved savedCapacity savedOld n anchors source removed st savedTree)
    (hai : MaskedClusterLeaders.Invariant activeOld active) (hac : activeCapacity=2^g)
    (hsi : MaskedClusterLeaders.Invariant savedOld saved) (hsc : savedCapacity=2^h)
    (f : Nat→α) (base : Nat) (hfull : MaskedRunDiscovery.Complete f n base savedOld saved.occurrences.entries)
    (disjoint : ∀p,p∈active.occurrences.entries→p∉saved.occurrences.entries)
    (hp : ∀p,p∈positions→p∈active.occurrences.entries) :
    Maintained env saved savedCapacity savedOld n anchors source (positions.reverse++removed)
      (eraseMany env active activeCapacity activeOld positions st activeTree).store savedTree := by
  apply Maintained.transport_erases env st _ saved savedCapacity savedOld n anchors source removed positions savedTree hm hsi hsc f base hfull
    (fun p hmem=>disjoint p (hp p hmem)) (eraseMany_sources env active activeCapacity activeOld positions st activeTree)
  intro first hf
  exact eraseMany_disjoint_slots env active activeCapacity activeOld saved savedOld first positions st activeTree hai hac hsi hf disjoint

end REWB.MaskedTraversalAggregate.Cells
