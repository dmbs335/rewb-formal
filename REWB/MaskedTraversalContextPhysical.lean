import REWB.MaskedTraversalContextStored

/-! The actual successor refresh compiler preserves a cluster's H-word
certificate and actual run-row metadata while recomputing its incoming
cursor from the final anchor array. Source membership comes from the
current erased-history snapshot; target counts stay immutable. -/
namespace REWB.MaskedTraversalContext
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedTraversalBankReady REWB.MaskedRunDiscovery
variable {α : Type} {h : Nat}

private theorem any_map {α β : Type} (o : Option α) (f : α→β) (p : β→Bool) :
    (o.map f).any p=o.any (fun x=>p (f x)) := by cases o <;> rfl

theorem compile_current (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount) (w : Word α) (fallback : α)
    (source target : Array Bool) (removed : List Nat) (st : Mutable.Store.State C E)
    (hv : MaskedMutableProgression.Batch.Valid source removed st.sources) (hn : st.sources.n=w.length)
    (hK : st.sources.modulus=prepared.K)
    (partition : MaskedClusterLeaders.State h) (capacity first L fullBase anchorBase : Nat)
    (anchors : Array (Option Nat)) (entry : Mutable.Store.Entry C E)
    (he : st.slots[first]?.join=some entry)
    (hi : MaskedClusterLeaders.Invariant L partition) (hcap : capacity=2^h)
    (hd : (MaskedClusterDescriptor.describeLeader partition capacity first).1=some entry.config.descriptor)
    (hfull : Complete (ArrayText.read w.toArray fallback) w.length fullBase L partition.occurrences.entries)
    (hL : 0<L) (hb : AnchorBounds partition capacity w.length L anchors)
    (ha : readAnchor anchors first L=entry.config.anchor)
    (copies : List Nat)
    (cert : MaskedLocalAnchor.Certificate (ArrayText.read w.toArray fallback) w.length
      anchorBase L copies entry.config.descriptor.last (entry.config.descriptor.nextAt w.length)
      entry.config.descriptor.previous entry.config.descriptor.following entry.config.anchor)
    (hmem : ∀k,k≤entry.config.descriptor.repetitions→entry.config.descriptor.first+k*entry.config.descriptor.period∈copies)
    (hr : RunBacked st.sources target prepared.K entry.config)
    (gate inMode outMode : Bool) (i j : Fin (MaskedClusterStage.dfa C E).stateCount) :
    (compile C E book prepared (BoundaryApplication.Range.build C w) (BoundaryApplication.Range.build E w)
      partition capacity first L anchors target st).1.any
      (fun next=>next.bank.view (code _ gate (ReplayMaps.encode (ReplayMaps.one C.stateCount E.stateCount)))
        (code _ inMode i) (code _ outMode j))=true ↔
      Mutable.Batch.CursorStep C E w entry.config.descriptor.first entry.config.descriptor.period entry.config.descriptor.repetitions
        L entry.config.anchor (entry.config.descriptor.nextAt w.length)
        (incoming partition capacity first L anchors).cursor (incoming partition capacity first L anchors).enabled
        inMode outMode source removed target (entry.config.window.gate gate)
        (MaskedClusterStage.decode C E i) (MaskedClusterStage.decode C E j) := by
  let cfg:=config partition capacity first L anchors entry.config
  have hg:=MaskedClusterDescriptor.describeLeader_geometry partition capacity L first hi hcap entry.config.descriptor hd
    (ArrayText.read w.toArray fallback) w.length fullBase hfull hL
  have hin:=incoming_bound partition capacity w.length fullBase L first (ArrayText.read w.toArray fallback)
    anchors hi hcap hfull hL hb entry.config.descriptor hd
  have hcert : MaskedLocalAnchor.Certificate (ArrayText.read w.toArray fallback) w.length
      anchorBase cfg.length copies cfg.descriptor.last (cfg.descriptor.nextAt w.length)
      cfg.descriptor.previous cfg.descriptor.following cfg.anchor := by
    simpa only [cfg,config,ha] using cert
  have hc:=store_current C E book prepared w fallback source target removed st.sources hv hn hK cfg
    fullBase anchorBase partition.occurrences.entries copies hg hcert hmem
    (runBacked_context partition capacity first L anchors entry.config st.sources target prepared.K hr ha)
    hin gate inMode outMode i j
  rw [compile,he,prepare_known partition capacity first L anchors entry hd]
  change ((Mutable.Store.compile C E book prepared (BoundaryApplication.Range.build C w)
    (BoundaryApplication.Range.build E w) st.sources target cfg).1.map _).any _=true ↔ _
  rw [any_map]
  simpa only [cfg,config,ha] using hc

end REWB.MaskedTraversalContext
