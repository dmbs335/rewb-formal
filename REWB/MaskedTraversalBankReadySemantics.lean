import REWB.MaskedTraversalBankReadyCost
import REWB.MaskedClusterMutableBatchCorrect

/-! The automatically compiled reset bank has the literal current-source
cursor semantics. Descriptors, incoming cursors, run IDs and immutable
target-count arrays are all read by the executable preparation. The only
retained-neighbor assumption is its explicit anchor-bound invariant. -/
namespace REWB.MaskedTraversalBankReady
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedRunDiscovery
variable {σ h : Nat}

private theorem any_map {α β : Type} (o : Option α) (f : α→β) (p : β→Bool) :
    (o.map f).any p=o.any (fun x=>p (f x)) := by cases o <;> rfl

theorem compile_reset_current (C E : DFA (Fin σ)) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount) (hK : 0<prepared.K)
    (text : Array (Fin σ)) (fallback : Fin σ) (source target : Array Bool) (removed : List Nat)
    (partition : MaskedClusterLeaders.State h) (capacity L first base : Nat)
    (anchors : Array (Option Nat)) (window : SourceWindow)
    (hi : MaskedClusterLeaders.Invariant L partition) (hcap : capacity=2^h)
    (d : MaskedClusterDescriptor.Descriptor)
    (hd : (MaskedClusterDescriptor.describeLeader partition capacity first).1=some d)
    (hfull : Complete (ArrayText.read text fallback) text.size base L partition.occurrences.entries)
    (hL : 0<L) (hb : AnchorBounds partition capacity text.size L anchors) (ha : readAnchor anchors first L=L)
    (gate inMode outMode : Bool) (i j : Fin (MaskedClusterStage.dfa C E).stateCount) :
    (compile C E book prepared (BoundaryApplication.Range.build C text.toList)
      (BoundaryApplication.Range.build E text.toList) partition capacity first L anchors window
      (MaskedRunCatalog.ofBatch target (MaskedMutableProgression.Batch.prepare text fallback source prepared.K))
      (MaskedSuffixClass.prepare text fallback)
      (MaskedMutableProgression.Batch.run text fallback source prepared.K removed) target).1.any
        (fun entry=>entry.bank.view (code _ gate (ReplayMaps.encode (ReplayMaps.one C.stateCount E.stateCount)))
          (code _ inMode i) (code _ outMode j))=true ↔
      Mutable.Batch.CursorStep C E text.toList d.first d.period d.repetitions L L (d.nextAt text.size)
        (incoming partition capacity first L anchors).cursor (incoming partition capacity first L anchors).enabled
        inMode outMode source removed target (window.gate gate)
        (MaskedClusterStage.decode C E i) (MaskedClusterStage.decode C E j) := by
  let sources:=MaskedMutableProgression.Batch.run text fallback source prepared.K removed
  have hv:=MaskedMutableProgression.Batch.run_valid text fallback source prepared.K hK removed
  have hns : sources.n=text.size := MaskedMutableProgression.Batch.eraseMany_n removed _
  have hmod : sources.modulus=prepared.K := MaskedMutableProgression.Batch.eraseMany_modulus removed _
  have hs:=(MaskedClusterDescriptor.describeLeader_sound partition capacity L first hi hcap d hd).2
  have hg:=MaskedClusterDescriptor.describeLeader_geometry partition capacity L first hi hcap d hd
    (ArrayText.read text fallback) text.size base hfull hL
  have hin:=incoming_bound partition capacity text.size base L first (ArrayText.read text fallback)
    anchors hi hcap hfull hL hb d hd
  by_cases hm : d.repetitions=0
  · have hp:=hg.point hm
    have cert : MaskedLocalAnchor.Certificate (ArrayText.read text.toList.toArray fallback) text.toList.length
        base L partition.occurrences.entries d.first (d.nextAt text.size) d.previous d.following L := by
      have hh:=hg.anchor
      rw [←hp.1] at hh
      simpa only [Array.toArray_toList,Array.length_toList] using hh
    have hsep : d.first<d.nextAt text.size := by rw [hp.1]; exact hg.next_strict
    have hsource : d.first≤sources.n := by
      rw [hns]
      have he:=hg.anchor.lastBound
      omega
    have henter : (incoming partition capacity first L anchors).enabled=true →
        d.first<(incoming partition capacity first L anchors).cursor ∧
        (incoming partition capacity first L anchors).cursor≤d.nextAt text.size := by
      simpa only [hm,if_true] using hin
    have hc:=Mutable.Batch.compileSingleton_current C E book text.toList fallback source removed sources hv
      base L partition.occurrences.entries d.first L (d.nextAt text.size)
      (incoming partition capacity first L anchors).cursor d.previous d.following
      (incoming partition capacity first L anchors).enabled gate inMode outMode target window i j cert
      hsep (by simpa only [Array.length_toList] using hg.next_bound) henter hsource
    rw [compile,prepare_singleton partition capacity first L anchors window _ _ d hd hm]
    simp only [Mutable.Store.compile,hm,if_true,ha,Option.map,Option.any]
    change (Mutable.Batch.compileSingleton C E book (BoundaryApplication.Range.build C text.toList)
      (BoundaryApplication.Range.build E text.toList) sources d.first L L (d.nextAt sources.n)
      (incoming partition capacity first L anchors).cursor (incoming partition capacity first L anchors).enabled
      target window).1.view _ _ _=true ↔ _
    rw [hns,hp.2.1]
    exact hc
  · have hmpos : 0<d.repetitions := by omega
    obtain ⟨R,id,hcfg,hrow,_,hrq,hrlo,hrhi⟩:=prepare_dense_reset text fallback source target prepared.K
      partition capacity L first base anchors window hi hcap d hd hfull hL hmpos ha
    have hrow' : sources.runs[id]?=some R := by
      change (MaskedMutableProgression.Batch.eraseMany removed
        (MaskedMutableProgression.Batch.prepare text fallback source prepared.K)).runs[id]?=some R
      rw [MaskedMutableProgression.Batch.eraseMany_runs]
      exact hrow
    have hend : d.first+d.repetitions*R.period=d.last := by rw [hrq]; exact hg.endpoint.symm
    have cert : MaskedLocalAnchor.Certificate (ArrayText.read text.toList.toArray fallback) text.toList.length
        base L partition.occurrences.entries (d.first+d.repetitions*R.period) (d.nextAt text.size)
        d.previous d.following L := by
      rw [hend]
      simpa only [Array.toArray_toList,Array.length_toList] using hg.anchor
    have hmem : ∀k,k≤d.repetitions → d.first+k*R.period∈partition.occurrences.entries := by
      intro k hk
      rw [hrq]
      exact ((hg.members _).mpr ⟨k,hk,rfl⟩).1
    have hprev : d.previous=some (d.first+(d.repetitions-1)*R.period) := by
      rw [hrq]
      exact (hg.dense hmpos).2.2
    have henter : (incoming partition capacity first L anchors).enabled=true →
        d.first<(incoming partition capacity first L anchors).cursor ∧
        (incoming partition capacity first L anchors).cursor≤d.first+R.period := by
      simpa only [hm,if_false,hrq] using hin
    have hc:=Mutable.Batch.compileRun_current C E book prepared text.toList fallback source removed sources hv
      id R hrow' hmod base L partition.occurrences.entries d.first d.repetitions L (d.nextAt text.size)
      (incoming partition capacity first L anchors).cursor d.previous d.following
      (incoming partition capacity first L anchors).enabled gate inMode outMode target window i j cert hmpos
      (by rw [hrq]; exact (hg.dense hmpos).1) hmem hprev (by rw [hend]; exact hg.next_strict)
      (by simpa only [Array.length_toList] using hg.next_bound) henter hrlo (by rw [hend]; omega)
    have hcover : R.period=d.period ∧ R.lo≤d.first ∧ d.last+L≤R.hi+1 := ⟨hrq,hrlo,by omega⟩
    rw [compile,hcfg]
    change ((Mutable.Store.compile C E book prepared (BoundaryApplication.Range.build C text.toList)
      (BoundaryApplication.Range.build E text.toList) sources target
        ⟨d,L,L,(incoming partition capacity first L anchors).cursor,
          (incoming partition capacity first L anchors).enabled,window,some id,
          (MaskedRunCatalog.entry target prepared.K R).counts⟩).1.map _).any _=true ↔ _
    simp only [Mutable.Store.compile,hm,if_false,hrow',hcover,if_true,true_and,hns,any_map]
    apply hc.trans
    rw [hrq]

end REWB.MaskedTraversalBankReady
