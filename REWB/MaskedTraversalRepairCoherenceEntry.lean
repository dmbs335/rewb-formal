import REWB.MaskedTraversalRepairCoherence

/-! Concrete presence and metadata lemmas for the repair compiler. The
dense branch uses an actual retained run-array ID; the reset branch
obtains this ID from the shared discovery/catalog operation.
-/
namespace REWB.MaskedTraversalRepairCoherence
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedTraversalAggregate
open REWB.MaskedTraversalBankReady REWB.MaskedTraversalContext REWB.MaskedClusterDescriptor
variable {α : Type} {C E : DFA α} {h n h' σ : Nat}

theorem compile_present (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (cfg : Mutable.Store.Config) (source : Array Bool) (removed : List Nat)
    (hv : MaskedMutableProgression.Batch.Valid source removed st.sources)
    (hK : st.sources.modulus=env.prepared.K)
    (hr : RunBacked st.sources env.target env.prepared.K cfg) :
    (Clip.compiled env st cfg).1.isSome=true := by
  by_cases hm : cfg.descriptor.repetitions=0
  · simp only [Clip.compiled,Mutable.Store.compile,hm,if_true,Option.isSome_some]
  · obtain ⟨R,id,hid,hrow,hq,hlo,hhi,_⟩:=hr hm
    obtain ⟨idx,hidx,_⟩:=hv.rows id R hrow
    have hcover : R.period=cfg.descriptor.period ∧ R.lo≤cfg.descriptor.first ∧ cfg.descriptor.last+cfg.anchor≤R.hi+1 :=
      ⟨hq,hlo,hhi⟩
    simp only [Clip.compiled,Mutable.Store.compile,hm,if_false,hid,hrow,hcover,if_true,true_and,
      Mutable.Batch.compileRun,hK,hidx,Option.isSome_some]

structure RawReady (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity L first : Nat)
    (anchors : Array (Option Nat)) (entry : Mutable.Store.Entry C E) : Prop where
  slot : st.slots[first]?.join=some entry
  descriptor : (describeLeader partition capacity first).1=some entry.config.descriptor
  anchor : entry.config.anchor=readAnchor anchors first L
  run : RunBacked st.sources env.target env.prepared.K entry.config

def RawComplete (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity L : Nat) (anchors : Array (Option Nat)) : Prop :=
  ∀first,first∈partition.leaders.entries→∃entry,RawReady env st partition capacity L first anchors entry

theorem coherent_raw (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity L first : Nat) (anchors : Array (Option Nat))
    (entry : Mutable.Store.Entry C E) (he : Cells.EntryState env st partition capacity L first entry)
    (ha : entry.config.anchor=readAnchor anchors first L)
    (hr : RunBacked st.sources env.target env.prepared.K entry.config) :
    ∃raw,RawReady env st partition capacity L first anchors raw := by
  obtain ⟨raw,hs,hn⟩:=he.raw
  refine ⟨raw,hs,?_,?_,?_⟩
  · simpa only [←hn,withLength] using he.descriptor
  · simpa only [←hn,withLength] using ha
  · simpa only [←hn,withLength,RunBacked] using hr

theorem context_present (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity L first : Nat) (anchors : Array (Option Nat))
    (entry : Mutable.Store.Entry C E) (ready : RawReady env st partition capacity L first anchors entry)
    (source : Array Bool) (removed : List Nat)
    (hv : MaskedMutableProgression.Batch.Valid source removed st.sources)
    (hK : st.sources.modulus=env.prepared.K) :
    (MaskedTraversalContext.compile C E env.book env.prepared env.cRanges env.eRanges
      partition capacity first L anchors env.target st).1.isSome=true := by
  have hr:=runBacked_context partition capacity first L anchors entry.config st.sources env.target env.prepared.K
    ready.run ready.anchor.symm
  have hc:=compile_present env st (config partition capacity first L anchors entry.config) source removed hv hK hr
  simp only [MaskedTraversalContext.compile,ready.slot,prepare_known partition capacity first L anchors entry ready.descriptor]
  change ((Clip.compiled env st (config partition capacity first L anchors entry.config)).1.map _).isSome=true
  cases hb : (Clip.compiled env st (config partition capacity first L anchors entry.config)).1 with
  | none => rw [hb] at hc; cases hc
  | some bank => rfl

theorem context_selected (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity L first : Nat) (anchors : Array (Option Nat))
    (entry raw : Mutable.Store.Entry C E) (ready : RawReady env st partition capacity L first anchors raw)
    (he : (MaskedTraversalContext.compile C E env.book env.prepared env.cRanges env.eRanges
      partition capacity first L anchors env.target st).1=some entry) :
    Cells.Current env st partition capacity L first entry ∧
      Cells.Linked env st partition capacity L first anchors entry.config := by
  obtain ⟨old,hslot,hd,hcfg,hbank⟩:=MaskedTraversalContext.compile_selected C E env.book env.prepared env.cRanges env.eRanges
    partition capacity first L anchors env.target st entry he
  have heq : old=raw := Option.some.inj (hslot.symm.trans ready.slot)
  subst old
  refine ⟨⟨?_,?_,hbank⟩,?_⟩
  · simpa only [hcfg,config] using hd
  · simp only [hcfg,config]
  · rw [hcfg]
    exact ⟨rfl,rfl,rfl,runBacked_context partition capacity first L anchors raw.config st.sources env.target env.prepared.K
      ready.run ready.anchor.symm⟩

theorem reset_runBacked (text : Array (Fin σ)) (fallback : Fin σ) (source target : Array Bool)
    (K : Nat) (partition : MaskedClusterLeaders.State h) (capacity L first base : Nat)
    (anchors : Array (Option Nat)) (window : SourceWindow)
    (hi : MaskedClusterLeaders.Invariant L partition) (hc : capacity=2^h)
    (hfull : MaskedRunDiscovery.Complete (ArrayText.read text fallback) text.size base L partition.occurrences.entries)
    (hL : 0<L) (ha : readAnchor anchors first L=L) (cfg : Mutable.Store.Config)
    (he : (MaskedTraversalBankReady.prepare partition capacity first L anchors window
      (MaskedRunCatalog.ofBatch target (MaskedMutableProgression.Batch.prepare text fallback source K))
      (MaskedSuffixClass.prepare text fallback)).1=some cfg)
    (removed : List Nat) :
    RunBacked (MaskedMutableProgression.Batch.run text fallback source K removed) target K cfg := by
  have hd:=(prepare_descriptor partition capacity first L anchors window _ _ cfg he).1
  intro hm
  obtain ⟨R,id,hprep,hrow,_,hq,hlo,hhi⟩:=prepare_dense_reset text fallback source target K partition capacity L first base
    anchors window hi hc cfg.descriptor hd hfull hL (by omega) ha
  have hcfg := Option.some.inj (he.symm.trans hprep)
  refine ⟨R,id,?_,?_,?_,?_,?_,?_⟩
  · exact congrArg Mutable.Store.Config.runId hcfg
  · change (MaskedMutableProgression.Batch.eraseMany removed
      (MaskedMutableProgression.Batch.prepare text fallback source K)).runs[id]?=some R
    rw [MaskedMutableProgression.Batch.eraseMany_runs]
    exact hrow
  · exact hq
  · exact hlo
  · have hh : cfg.anchor=L := congrArg Mutable.Store.Config.anchor hcfg
    rw [hh]
    omega
  · exact congrArg Mutable.Store.Config.targetCounts hcfg

end REWB.MaskedTraversalRepairCoherence
