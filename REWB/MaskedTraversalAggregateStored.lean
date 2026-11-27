import REWB.MaskedTraversalAggregateCells
import REWB.MaskedTraversalRetained

/-! The concrete maintained anchor/descriptor facts imply physical
semantics of a stored entry. Its longer word is local to its own cluster;
only the actual old prefix is shared with the aggregate representative.
-/
namespace REWB.MaskedTraversalAggregate.Cells
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedRunDiscovery
variable {α : Type} {h : Nat}

theorem entry_current (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount) (w : Word α) (fallback : α)
    (source target : Array Bool) (removed : List Nat) (sources : Mutable.Batch.Sources)
    (hv : MaskedMutableProgression.Batch.Valid source removed sources) (hn : sources.n=w.length)
    (hK : sources.modulus=prepared.K) (partition : MaskedClusterLeaders.State h)
    (capacity base L first representative : Nat) (anchors : Array (Option Nat))
    (hi : MaskedClusterLeaders.Invariant L partition) (hcap : capacity=2^h)
    (hfull : Complete (ArrayText.read w.toArray fallback) w.length base L partition.occurrences.entries)
    (hL : 0<L) (entry : Mutable.Store.Entry C E)
    (hd : (MaskedClusterDescriptor.describeLeader partition capacity first).1=some entry.config.descriptor)
    (own : MaskedTraversalRetained.Own (ArrayText.read w.toArray fallback) w.length L anchors first entry.config.descriptor)
    (ha : entry.config.anchor=MaskedTraversalBankReady.readAnchor anchors first L)
    (hc : (Mutable.Store.compile C E book prepared (BoundaryApplication.Range.build C w)
      (BoundaryApplication.Range.build E w) sources target entry.config).1=some entry.bank)
    (hnew : L≤entry.config.length) (hH : entry.config.length≤entry.config.anchor)
    (hrep : representative+entry.config.length≤w.length)
    (hcopy : Spec.slice w representative (representative+entry.config.length)=
      Spec.slice w entry.config.descriptor.first (entry.config.descriptor.first+entry.config.length))
    (hr : MaskedTraversalContext.RunBacked sources target prepared.K entry.config)
    (hin : entry.config.incomingEnabled=true→entry.config.descriptor.first<entry.config.incoming ∧
      entry.config.incoming≤if entry.config.descriptor.repetitions=0 then entry.config.descriptor.nextAt w.length
        else entry.config.descriptor.first+entry.config.descriptor.period)
    (gate inMode outMode : Bool) (i j : Fin (MaskedClusterStage.dfa C E).stateCount) :
    entry.bank.view
      (code _ gate (ReplayMaps.encode (ReplayMaps.word C E
        (Spec.slice w (representative+L) (representative+entry.config.length)))))
      (code _ inMode i) (code _ outMode j)=true ↔
      Mutable.Batch.CursorStep C E w entry.config.descriptor.first entry.config.descriptor.period
        entry.config.descriptor.repetitions L entry.config.anchor (entry.config.descriptor.nextAt w.length)
        entry.config.incoming entry.config.incomingEnabled inMode outMode source removed target
        (entry.config.window.gate gate) (MaskedClusterStage.decode C E i) (MaskedClusterStage.decode C E j) := by
  obtain ⟨H,hslot,cert⟩:=own
  have hanchor : entry.config.anchor=H := by
    simpa only [MaskedTraversalBankReady.readAnchor,hslot,Option.getD_some] using ha
  have hg:=MaskedClusterDescriptor.describeLeader_geometry partition capacity L first hi hcap
    entry.config.descriptor hd (ArrayText.read w.toArray fallback) w.length base hfull hL
  have hmem : ∀k,k≤entry.config.descriptor.repetitions→
      entry.config.descriptor.first+k*entry.config.descriptor.period∈MaskedTraversalRetained.copies entry.config.descriptor := by
    intro k hk
    exact (MaskedTraversalRetained.copies_mem _ _).mpr ⟨k,hk,rfl⟩
  have hf:=cert.words entry.config.descriptor.first (by simpa only [Nat.zero_mul,Nat.add_zero] using hmem 0 (Nat.zero_le _))
  have hs : entry.config.descriptor.first+entry.config.anchor≤w.length := by rw [hanchor]; exact hf.1
  have cert' : MaskedLocalAnchor.Certificate (ArrayText.read w.toArray fallback) w.length
      entry.config.descriptor.first L (MaskedTraversalRetained.copies entry.config.descriptor)
      entry.config.descriptor.last (entry.config.descriptor.nextAt w.length)
      entry.config.descriptor.previous entry.config.descriptor.following entry.config.anchor := by
    rw [hanchor]
    exact cert
  have hh:=store_shorter_current C E book prepared w fallback source target removed sources hv hn hK entry.config
    representative L hnew hH hrep hs hcopy base entry.config.descriptor.first partition.occurrences.entries
    (MaskedTraversalRetained.copies entry.config.descriptor) hg cert' hmem hr hin gate inMode outMode i j
  simpa only [hc,Option.any_some] using hh

end REWB.MaskedTraversalAggregate.Cells
