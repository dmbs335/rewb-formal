import REWB.MaskedTraversalAggregateErasedCoherence
import REWB.MaskedTraversalAggregateStored
import REWB.MaskedTraversalIncomingConfig

/-! Actual stored-bank coherence gives the physical meaning of every
aggregate cell. The remaining metadata are actual anchor, predecessor
and run-array reads. Common words come from the complete occurrence
class; no cell semantics or replay answer is supplied as an oracle.
-/
namespace REWB.MaskedTraversalAggregate.Cells
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedTraversalBankReady
variable {α : Type} {C E : DFA α} {h : Nat}

structure Current (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity old first : Nat)
    (entry : Mutable.Store.Entry C E) : Prop where
  descriptor : (MaskedClusterDescriptor.describeLeader partition capacity first).1=some entry.config.descriptor
  current : entry.config.length=old
  compiled : (Clip.compiled env st entry.config).1=some entry.bank

def CurrentEntries (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity old : Nat)
    (entries : List (Option (Mutable.Store.Entry C E))) : Prop :=
  ∀(first : Nat) (entry : Mutable.Store.Entry C E),entries[first]?=some (some entry)→
    Current env st partition capacity old first entry

theorem Coherent.current {env : Clip.Env C E} {st : Mutable.Store.State C E}
    {partition : MaskedClusterLeaders.State h} {capacity old : Nat}
    {entries : List (Option (Mutable.Store.Entry C E))}
    (hh : Coherent env st partition capacity old entries) : CurrentEntries env st partition capacity old entries := by
  intro first entry he
  have hentry:=hh first entry he
  exact ⟨hentry.descriptor,hentry.current,hentry.compiled⟩

structure Linked (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity old first : Nat)
    (anchors : Array (Option Nat)) (cfg : Mutable.Store.Config) : Prop where
  anchor : cfg.anchor=readAnchor anchors first old
  incoming : cfg.incoming=(MaskedTraversalBankReady.incoming partition capacity first old anchors).cursor
  enabled : cfg.incomingEnabled=(MaskedTraversalBankReady.incoming partition capacity first old anchors).enabled
  run : MaskedTraversalContext.RunBacked st.sources env.target env.prepared.K cfg

def LinkedEntries (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity old : Nat) (anchors : Array (Option Nat))
    (entries : List (Option (Mutable.Store.Entry C E))) : Prop :=
  ∀(first : Nat) (entry : Mutable.Store.Entry C E),entries[first]?=some (some entry)→
    Linked env st partition capacity old first anchors entry.config

structure BandGeometry (w : Word α) (fallback : α) (partition : MaskedClusterLeaders.State h)
    (capacity base old L : Nat) (anchors : Array (Option Nat)) : Prop where
  oldInvariant : MaskedClusterLeaders.Invariant old partition
  currentInvariant : MaskedClusterLeaders.Invariant L partition
  capacity_eq : capacity=2^h
  oldComplete : MaskedRunDiscovery.Complete (ArrayText.read w.toArray fallback) w.length base old partition.occurrences.entries
  currentComplete : MaskedRunDiscovery.Complete (ArrayText.read w.toArray fallback) w.length base L partition.occurrences.entries
  oldAnchors : MaskedTraversalRetained.Away partition capacity (ArrayText.read w.toArray fallback) w.length old anchors []
  currentAnchors : MaskedTraversalRetained.Away partition capacity (ArrayText.read w.toArray fallback) w.length L anchors []
  positive : 0<L
  ordered : L≤old
  representative : base+old≤w.length

theorem Linked.at_length (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity old fresh first : Nat)
    (anchors : Array (Option Nat)) (cfg : Mutable.Store.Config)
    (linked : Linked env st partition capacity old first anchors cfg)
    (f : Nat→α) (n : Nat) (hi : MaskedClusterLeaders.Invariant old partition) (hc : capacity=2^h)
    (ha : MaskedTraversalRetained.Away partition capacity f n old anchors [])
    (hd : (MaskedClusterDescriptor.describeLeader partition capacity first).1=some cfg.descriptor) :
    Linked env st partition capacity fresh first anchors (withLength cfg fresh) := by
  obtain ⟨H,hH,_⟩:=ha first (by simp) cfg.descriptor hd
  have hin:=MaskedTraversalIncoming.populated_length partition capacity n old fresh first f anchors hi hc ha
  refine ⟨?_,?_,?_,linked.run⟩
  · simpa only [withLength,readAnchor,hH,Option.getD_some] using linked.anchor
  · simpa only [withLength,hin] using linked.incoming
  · simpa only [withLength,hin] using linked.enabled

theorem Linked.clipped (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity old first lo hi : Nat)
    (anchors : Array (Option Nat)) (cfg : Mutable.Store.Config)
    (linked : Linked env st partition capacity old first anchors cfg) :
    Linked env st partition capacity old first anchors (Clip.config cfg old lo hi) :=
  ⟨linked.anchor,linked.incoming,linked.enabled,linked.run⟩

theorem Current.cell_meaning (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity base old L first : Nat)
    (anchors : Array (Option Nat)) (entry : Mutable.Store.Entry C E)
    (coherent : Current env st partition capacity old first entry)
    (linked : Linked env st partition capacity old first anchors entry.config)
    (w : Word α) (fallback : α) (geometry : BandGeometry w fallback partition capacity base old L anchors)
    (source : Array Bool) (removed : List Nat)
    (hv : MaskedMutableProgression.Batch.Valid source removed st.sources) (hn : st.sources.n=w.length)
    (hK : st.sources.modulus=env.prepared.K)
    (hc : env.cRanges=BoundaryApplication.Range.build C w) (he : env.eRanges=BoundaryApplication.Range.build E w)
    (gate : Bool) (i j : Fin (2*(MaskedClusterStage.dfa C E).stateCount)) :
    entry.bank.view (code _ gate (ReplayMaps.encode (ReplayMaps.word C E (Spec.slice w (base+L) (base+old))))) i j=true ↔
      partStep C E w L source removed env.target ⟨entry.config,gate⟩ i j := by
  have ownOld:=geometry.oldAnchors first (by simp) entry.config.descriptor coherent.descriptor
  have ownNew:=geometry.currentAnchors first (by simp) entry.config.descriptor coherent.descriptor
  obtain ⟨H,hH,cert⟩:=ownOld
  have hanchor : entry.config.anchor=H := by
    simpa only [readAnchor,hH,Option.getD_some] using linked.anchor
  have hanchorNew : entry.config.anchor=readAnchor anchors first L := by
    simpa only [readAnchor,hH,Option.getD_some] using hanchor
  have hHbound : entry.config.length≤entry.config.anchor := by rw [coherent.current,hanchor]; exact cert.current
  have hs:=MaskedClusterDescriptor.describeLeader_sound partition capacity old first geometry.oldInvariant
    geometry.capacity_eq entry.config.descriptor coherent.descriptor
  have hcand:=(geometry.oldComplete entry.config.descriptor.first).mp hs.2.firstMember
  have hcopy : Spec.slice w base (base+old)=
      Spec.slice w entry.config.descriptor.first (entry.config.descriptor.first+old) := by
    have hh:=hcand.2.symm
    rw [ArrayText.segment_word w fallback base old geometry.representative,
      ArrayText.segment_word w fallback entry.config.descriptor.first old hcand.1] at hh
    simpa only [Spec.slice,Nat.add_sub_cancel_left] using hh
  have hincoming:=MaskedTraversalIncoming.populated_length partition capacity w.length old L first
    (ArrayText.read w.toArray fallback) anchors geometry.oldInvariant geometry.capacity_eq geometry.oldAnchors
  have hnum := incoming_bound partition capacity w.length base L first (ArrayText.read w.toArray fallback)
    anchors geometry.currentInvariant geometry.capacity_eq geometry.currentComplete geometry.positive
    (fun p d hd=>(geometry.currentAnchors p (by simp) d hd).bounds) entry.config.descriptor coherent.descriptor
  have hnum' : entry.config.incomingEnabled=true→entry.config.descriptor.first<entry.config.incoming ∧
      entry.config.incoming≤if entry.config.descriptor.repetitions=0 then entry.config.descriptor.nextAt w.length
        else entry.config.descriptor.first+entry.config.descriptor.period := by
    simpa only [hincoming,←linked.incoming,←linked.enabled] using hnum
  have hh:=entry_current C E env.book env.prepared w fallback source env.target removed st.sources hv hn hK
    partition capacity base L first base anchors geometry.currentInvariant geometry.capacity_eq geometry.currentComplete
    geometry.positive entry coherent.descriptor ownNew hanchorNew
    (by simpa only [Clip.compiled,hc,he] using coherent.compiled)
    (by rw [coherent.current]; exact geometry.ordered) hHbound
    (by rw [coherent.current]; exact geometry.representative)
    (by simpa only [coherent.current] using hcopy) linked.run hnum' gate (codeMode _ i) (codeMode _ j)
    (codeState _ i) (codeState _ j)
  simpa only [coherent.current,code_decode,partStep,decoded] using hh

theorem CurrentEntries.denotes_region (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity base old L lo hi : Nat)
    (anchors : Array (Option Nat)) (tree : BankTree C E h)
    (entries : List (Option (Mutable.Store.Entry C E))) (represented : Represents tree entries)
    (coherent : CurrentEntries env st partition capacity old entries)
    (linked : LinkedEntries env st partition capacity old anchors entries)
    (w : Word α) (fallback : α) (geometry : BandGeometry w fallback partition capacity base old L anchors)
    (source : Array Bool) (removed : List Nat)
    (hv : MaskedMutableProgression.Batch.Valid source removed st.sources) (hn : st.sources.n=w.length)
    (hK : st.sources.modulus=env.prepared.K)
    (hc : env.cRanges=BoundaryApplication.Range.build C w) (he : env.eRanges=BoundaryApplication.Range.build E w) :
    Denotes C E w L source removed env.target
      (ReplayMaps.encode (ReplayMaps.word C E (Spec.slice w (base+L) (base+old))))
      (regionCells tree.leaves lo hi) (regionParts entries lo hi) := by
  apply Cells.denotes_region C E w L source removed env.target _ tree entries represented lo hi
  intro entry hentry gate i j
  obtain ⟨first,hslot⟩:=List.getElem?_of_mem hentry
  exact Current.cell_meaning env st partition capacity base old L first anchors entry
    (coherent first entry hslot) (linked first entry hslot) w fallback geometry source removed hv hn hK hc he gate i j

end REWB.MaskedTraversalAggregate.Cells
