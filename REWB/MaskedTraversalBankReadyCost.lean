import REWB.MaskedTraversalBankIncoming
import REWB.MaskedClusterMutableStoreGeometry

/-! Actual automatic reset costs, including descriptor/previous-neighbor
queries, shared run discovery, direct run-row access, immutable target
count selection, and the finite bank compiler. Shared index construction
is charged by its existing preparation theorems, not repeated per key. -/
namespace REWB.MaskedTraversalBankReady
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedRunDiscovery
variable {α : Type} {σ h h' n : Nat}

theorem prepare_reset_geometry (partition : MaskedClusterLeaders.State h) (capacity n base L first : Nat)
    (f : Nat→α) (anchors : Array (Option Nat)) (window : SourceWindow)
    (catalog : MaskedRunCatalog.Index) (classes : MaskedSuffixClass.Index n h')
    (hi : MaskedClusterLeaders.Invariant L partition) (hc : capacity=2^h)
    (hfull : Complete f n base L partition.occurrences.entries) (hL : 0<L)
    (hb : AnchorBounds partition capacity n L anchors) (ha : readAnchor anchors first L=L)
    (cfg : Mutable.Store.Config)
    (he : (prepare partition capacity first L anchors window catalog classes).1=some cfg) :
    Mutable.Store.Geometry cfg n := by
  have hs:=prepare_descriptor partition capacity first L anchors window catalog classes cfg he
  have hl:=hs.2.1
  have hh : cfg.anchor=L := hs.2.2.1.trans ha
  have hin : cfg.incomingEnabled=true → cfg.descriptor.first<cfg.incoming ∧
      cfg.incoming≤if cfg.descriptor.repetitions=0 then cfg.descriptor.nextAt n else cfg.descriptor.first+cfg.descriptor.period := by
    rw [hs.2.2.2.1,hs.2.2.2.2.1]
    exact incoming_bound partition capacity n base L first f anchors hi hc hfull hL hb cfg.descriptor hs.1
  have hg:=Mutable.Store.describe_reset_geometry partition capacity L first hi hc cfg.descriptor hs.1
    f n base hfull hL cfg.incoming cfg.incomingEnabled cfg.window cfg.runId cfg.targetCounts hin
  have heq : ({cfg with length:=L,anchor:=L} : Mutable.Store.Config)=cfg := by
    cases cfg
    dsimp only at hl hh ⊢
    simp only [hl,hh]
  change Mutable.Store.Geometry {cfg with length:=L,anchor:=L} n at hg
  rw [heq] at hg
  exact hg

theorem prepare_work (text : Array (Fin σ)) (fallback : Fin σ) (source target : Array Bool)
    (K : Nat) (partition : MaskedClusterLeaders.State h) (capacity first L : Nat)
    (anchors : Array (Option Nat)) (window : SourceWindow) :
    (prepare partition capacity first L anchors window
      (MaskedRunCatalog.ofBatch target (MaskedMutableProgression.Batch.prepare text fallback source K))
      (MaskedSuffixClass.prepare text fallback)).2≤85*h+52*MaskedRunCatalog.width text.size+134 := by
  have hd:=MaskedClusterDescriptor.describeLeader_work partition capacity first
  have hi:=incoming_work partition capacity first L anchors
  simp only [prepare]
  cases he : (MaskedClusterDescriptor.describeLeader partition capacity first).1 with
  | none => simp only [he]; omega
  | some d =>
    have hr:=MaskedRunCatalog.descriptorShared_work text fallback source target K d L
    simp only [he]
    omega

theorem compile_reset_work (C E : DFA (Fin σ)) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount) (hK : 0<prepared.K)
    (text : Array (Fin σ)) (fallback : Fin σ) (source target : Array Bool) (removed : List Nat)
    (partition : MaskedClusterLeaders.State h) (capacity L first base : Nat)
    (anchors : Array (Option Nat)) (window : SourceWindow)
    (hi : MaskedClusterLeaders.Invariant L partition) (hcap : capacity=2^h)
    (hfull : Complete (ArrayText.read text fallback) text.size base L partition.occurrences.entries)
    (hL : 0<L) (hb : AnchorBounds partition capacity text.size L anchors) (ha : readAnchor anchors first L=L) :
    (compile C E book prepared (BoundaryApplication.Range.build C text.toList)
      (BoundaryApplication.Range.build E text.toList) partition capacity first L anchors window
      (MaskedRunCatalog.ofBatch target (MaskedMutableProgression.Batch.prepare text fallback source prepared.K))
      (MaskedSuffixClass.prepare text fallback)
      (MaskedMutableProgression.Batch.run text fallback source prepared.K removed) target).2≤
      85*h+52*MaskedRunCatalog.width text.size+137+Mutable.Store.bankLimit C E prepared.K text.size := by
  let catalog:=MaskedRunCatalog.ofBatch target (MaskedMutableProgression.Batch.prepare text fallback source prepared.K)
  let classes:=MaskedSuffixClass.prepare text fallback
  let sources:=MaskedMutableProgression.Batch.run text fallback source prepared.K removed
  have hp : (prepare partition capacity first L anchors window catalog classes).2≤
      85*h+52*MaskedRunCatalog.width text.size+134 :=
    prepare_work text fallback source target prepared.K partition capacity first L anchors window
  change (compile C E book prepared (BoundaryApplication.Range.build C text.toList)
    (BoundaryApplication.Range.build E text.toList) partition capacity first L anchors window catalog classes sources target).2≤_
  simp only [compile]
  cases he : (prepare partition capacity first L anchors window catalog classes).1 with
  | none => simp only [he]; omega
  | some cfg =>
    have hg:=prepare_reset_geometry partition capacity text.size base L first (ArrayText.read text fallback)
      anchors window catalog classes hi hcap hfull hL hb ha cfg he
    have hv:=MaskedMutableProgression.Batch.run_valid text fallback source prepared.K hK removed
    have hn : sources.n=text.toList.length := by
      change (MaskedMutableProgression.Batch.eraseMany removed
        (MaskedMutableProgression.Batch.prepare text fallback source prepared.K)).n=text.toList.length
      rw [MaskedMutableProgression.Batch.eraseMany_n]
      simp only [Array.length_toList]
      rfl
    have hgeom : Mutable.Store.Geometry cfg text.toList.length := by simpa only [Array.length_toList] using hg
    have hw:=Mutable.Store.compile_work C E book prepared text.toList source removed sources hv hn target cfg hgeom
    simp only [Array.length_toList] at hw
    simp only [he]
    omega

theorem write_counts (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (partition : MaskedClusterLeaders.State h) (capacity first current : Nat)
    (anchors : Array (Option Nat)) (window : SourceWindow)
    (catalog : MaskedRunCatalog.Index) (classes : MaskedSuffixClass.Index n h')
    (target : Array Bool) (st : Mutable.Store.State C E) :
    (write C E book prepared ci ei partition capacity first current anchors window catalog classes target st).rebuilds=st.rebuilds+1 ∧
    (write C E book prepared ci ei partition capacity first current anchors window catalog classes target st).writes=st.writes+1 ∧
    (write C E book prepared ci ei partition capacity first current anchors window catalog classes target st).slots.size=st.slots.size := by
  exact ⟨rfl,rfl,by simp only [write,Array.size_setIfInBounds]⟩

end REWB.MaskedTraversalBankReady
