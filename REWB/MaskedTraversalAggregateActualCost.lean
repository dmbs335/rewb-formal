import REWB.MaskedTraversalAggregateWindowPhysical
import REWB.MaskedTraversalAggregateMetadata

/-! The compiler work preconditions follow from actual maintained
descriptors, anchors and predecessor reads. These bounds charge actual
window compilers and current-length source repairs, including lookups
and persistent replacements, rather than assuming a bank cost oracle.
-/
namespace REWB.MaskedTraversalAggregate.Cells
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedTraversalBankReady
variable {α : Type} {C E : DFA α} {h : Nat}

theorem Current.bank_geometry (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity base old L first : Nat)
    (anchors : Array (Option Nat)) (entry : Mutable.Store.Entry C E)
    (current : Current env st partition capacity old first entry)
    (linked : Linked env st partition capacity old first anchors entry.config)
    (w : Word α) (fallback : α) (geometry : BandGeometry w fallback partition capacity base old L anchors) :
    Mutable.Store.Geometry entry.config w.length := by
  have own:=geometry.oldAnchors first (by simp) entry.config.descriptor current.descriptor
  obtain ⟨H,hH,cert⟩:=own
  have hanchor : entry.config.anchor=H := by
    simpa only [readAnchor,hH,Option.getD_some] using linked.anchor
  have hpos : 0<old := by have hh:=geometry.positive; have hn:=geometry.ordered; omega
  have hg:=MaskedClusterDescriptor.describeLeader_geometry partition capacity old first geometry.oldInvariant
    geometry.capacity_eq entry.config.descriptor current.descriptor (ArrayText.read w.toArray fallback)
    w.length base geometry.oldComplete hpos
  have hnum:=incoming_bound partition capacity w.length base old first (ArrayText.read w.toArray fallback)
    anchors geometry.oldInvariant geometry.capacity_eq geometry.oldComplete hpos
    (fun p d hd=>(geometry.oldAnchors p (by simp) d hd).bounds) entry.config.descriptor current.descriptor
  apply MaskedTraversalContext.retained_geometry (ArrayText.read w.toArray fallback) w.length base
    entry.config.descriptor.first partition.occurrences.entries (MaskedTraversalRetained.copies entry.config.descriptor) entry.config
  · simpa only [current.current] using hg
  · simpa only [current.current,hanchor] using cert
  · simpa only [←linked.incoming,←linked.enabled] using hnum

theorem raw_current_geometry (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity base old L first : Nat)
    (anchors : Array (Option Nat)) (entries : List (Option (Mutable.Store.Entry C E)))
    (coherent : Coherent env st partition capacity old entries) (complete : CompleteModel partition entries)
    (linked : LinkedEntries env st partition capacity old anchors entries)
    (w : Word α) (fallback : α) (geometry : BandGeometry w fallback partition capacity base old L anchors)
    (hfirst : first∈partition.leaders.entries) (raw : Mutable.Store.Entry C E)
    (hraw : st.slots[first]?.join=some raw) :
    Mutable.Store.Geometry (withLength raw.config old) w.length := by
  obtain ⟨entry,he⟩:=complete first hfirst
  have hh:=coherent first entry he
  obtain ⟨before,hs,hn⟩:=hh.raw
  have heq : before=raw := Option.some.inj (hs.symm.trans hraw)
  subst before
  rw [hn]
  exact Current.bank_geometry env st partition capacity base old L first anchors entry
    (coherent.current first entry he) (linked first entry he) w fallback geometry

theorem queryWindow_actual_clipping_work (B : DFA α) (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity base old L lo hi lengthLo lengthHi : Nat)
    (anchors : Array (Option Nat)) (tree : BankTree C E h)
    (entries : List (Option (Mutable.Store.Entry C E)))
    (coherent : Coherent env st partition capacity old entries) (complete : CompleteModel partition entries)
    (linked : LinkedEntries env st partition capacity old anchors entries)
    (w : Word α) (fallback : α) (geometry : BandGeometry w fallback partition capacity base old L anchors)
    (source : Array Bool) (removed : List Nat)
    (hv : MaskedMutableProgression.Batch.Valid source removed st.sources) (hn : st.sources.n=w.length)
    (hc : env.cRanges=BoundaryApplication.Range.build C w) (he : env.eRanges=BoundaryApplication.Range.build E w) :
    (queryWindow B C E (Cut.build B C E w) env st partition capacity tree lo hi base lengthLo lengthHi old).clippingWork≤
      14*h+17+2*(Mutable.Store.bankLimit C E env.prepared.K w.length+
        (h+1)*Tree.replaceBudget (2*ReplayMaps.count C.stateCount E.stateCount)
          (2*(MaskedClusterStage.dfa C E).stateCount)+10) := by
  apply queryWindow_clipping_work B C E (Cut.build B C E w) env st partition capacity tree lo hi base lengthLo lengthHi old
    w source removed hv hn hc he
  intro first hk raw hraw
  have hh:=raw_current_geometry env st partition capacity base old L first anchors entries coherent complete linked
    w fallback geometry (plan_keys_leaders partition capacity old lo hi geometry.oldInvariant geometry.capacity_eq first hk) raw hraw
  have hb : old≤(withLength raw.config old).anchor := hh.current
  exact Clip.config_geometry (withLength raw.config old) old lo hi w.length hh hb

theorem eraseCurrent_actual_work (env : Clip.Env C E) (st : Mutable.Store.State C E)
    (partition : MaskedClusterLeaders.State h) (capacity base old L p : Nat)
    (anchors : Array (Option Nat)) (tree : BankTree C E h)
    (entries : List (Option (Mutable.Store.Entry C E)))
    (coherent : Coherent env st partition capacity old entries) (complete : CompleteModel partition entries)
    (linked : LinkedEntries env st partition capacity old anchors entries)
    (w : Word α) (fallback : α) (geometry : BandGeometry w fallback partition capacity base old L anchors)
    (source : Array Bool) (removed : List Nat)
    (hv : MaskedMutableProgression.Batch.Valid source removed st.sources) (hn : st.sources.n=w.length)
    (hc : env.cRanges=BoundaryApplication.Range.build C w) (he : env.eRanges=BoundaryApplication.Range.build E w) :
    (eraseCurrent env partition capacity old p st tree).work≤11*h+24+
      Mutable.Store.bankLimit C E env.prepared.K w.length+
        (h+1)*Tree.replaceBudget (2*ReplayMaps.count C.stateCount E.stateCount)
          (2*(MaskedClusterStage.dfa C E).stateCount) := by
  apply eraseCurrent_work env partition capacity old p st tree w source removed hv hn hc he
  intro first ho raw hraw
  have hfirst:=((MaskedClusterDescriptor.locate_correct partition capacity old p first
    geometry.oldInvariant geometry.capacity_eq).mp ho).2.1
  exact raw_current_geometry env st partition capacity base old L first anchors entries coherent complete linked
    w fallback geometry hfirst raw hraw

end REWB.MaskedTraversalAggregate.Cells
