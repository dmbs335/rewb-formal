import REWB.MaskedTraversalBankReady

/-! Dense reset preparation resolves an actual shared run and its exact
original mutable-source row.  Even after an arbitrary erase history,
every actual leader of a positive-length complete class compiles a bank.
Retained-anchor geometry and cursor-block composition are not assumed to
follow merely from this successful compilation theorem. -/
namespace REWB.MaskedTraversalBankReady
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedRunDiscovery
open REWB.RunGeometry
variable {α : Type} {σ h h' n : Nat}

theorem prepare_singleton (partition : MaskedClusterLeaders.State h) (capacity first current : Nat)
    (anchors : Array (Option Nat)) (window : SourceWindow)
    (catalog : MaskedRunCatalog.Index) (classes : MaskedSuffixClass.Index n h')
    (d : MaskedClusterDescriptor.Descriptor)
    (hd : (MaskedClusterDescriptor.describeLeader partition capacity first).1=some d)
    (hm : d.repetitions=0) :
    (prepare partition capacity first current anchors window catalog classes).1=
      some ⟨d,current,readAnchor anchors first current,
        (incoming partition capacity first current anchors).cursor,
        (incoming partition capacity first current anchors).enabled,window,none,#[]⟩ := by
  simp only [prepare,hd,MaskedRunCatalog.descriptorShared,MaskedRunCatalog.descriptor,hm,Nat.lt_irrefl,if_false]
  rfl

theorem prepare_dense_reset (text : Array (Fin σ)) (fallback : Fin σ) (source target : Array Bool)
    (K : Nat) (partition : MaskedClusterLeaders.State h) (capacity L first base : Nat)
    (anchors : Array (Option Nat)) (window : SourceWindow)
    (hi : MaskedClusterLeaders.Invariant L partition) (hcap : capacity=2^h)
    (d : MaskedClusterDescriptor.Descriptor)
    (hd : (MaskedClusterDescriptor.describeLeader partition capacity first).1=some d)
    (hfull : Complete (ArrayText.read text fallback) text.size base L partition.occurrences.entries)
    (hL : 0<L) (hm : 0<d.repetitions) (ha : readAnchor anchors first L=L) :
    ∃R id,(prepare partition capacity first L anchors window
      (MaskedRunCatalog.ofBatch target (MaskedMutableProgression.Batch.prepare text fallback source K))
      (MaskedSuffixClass.prepare text fallback)).1=
      some ⟨d,L,L,(incoming partition capacity first L anchors).cursor,
        (incoming partition capacity first L anchors).enabled,window,some id,
        (MaskedRunCatalog.entry target K R).counts⟩ ∧
      (MaskedMutableProgression.Batch.prepare text fallback source K).runs[id]?=some R ∧
      R.Valid (ArrayText.read text fallback) text.size ∧ R.period=d.period ∧
      R.lo≤d.first ∧ d.last+L≤R.hi := by
  obtain ⟨R,id,hfound,hrow,hvalid,hperiod,hbase,hend⟩:=
    MaskedRunCatalog.descriptor_complete text fallback source target K partition capacity L first base
      hi hcap d hd hfull hL hm
  refine ⟨R,id,?_,hrow,hvalid,hperiod,hbase,hend⟩
  simp only [prepare,hd,hfound,ha]
  rfl

theorem prepare_descriptor (partition : MaskedClusterLeaders.State h) (capacity first current : Nat)
    (anchors : Array (Option Nat)) (window : SourceWindow)
    (catalog : MaskedRunCatalog.Index) (classes : MaskedSuffixClass.Index n h') (cfg : Mutable.Store.Config)
    (he : (prepare partition capacity first current anchors window catalog classes).1=some cfg) :
    (MaskedClusterDescriptor.describeLeader partition capacity first).1=some cfg.descriptor ∧
      cfg.length=current ∧ cfg.anchor=readAnchor anchors first current ∧
      cfg.incoming=(incoming partition capacity first current anchors).cursor ∧
      cfg.incomingEnabled=(incoming partition capacity first current anchors).enabled ∧ cfg.window=window := by
  cases hd : (MaskedClusterDescriptor.describeLeader partition capacity first).1 with
  | none => simp only [prepare,hd,reduceCtorEq] at he
  | some d =>
    simp only [prepare,hd,Option.some.injEq] at he
    subst cfg
    exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem compile_selected (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (partition : MaskedClusterLeaders.State h) (capacity first current : Nat)
    (anchors : Array (Option Nat)) (window : SourceWindow)
    (catalog : MaskedRunCatalog.Index) (classes : MaskedSuffixClass.Index n h')
    (sources : Mutable.Batch.Sources) (target : Array Bool) (entry : Mutable.Store.Entry C E)
    (he : (compile C E book prepared ci ei partition capacity first current anchors window catalog classes sources target).1=some entry) :
    (prepare partition capacity first current anchors window catalog classes).1=some entry.config ∧
      (Mutable.Store.compile C E book prepared ci ei sources target entry.config).1=some entry.bank := by
  cases hp : (prepare partition capacity first current anchors window catalog classes).1 with
  | none => simp only [compile,hp,reduceCtorEq] at he
  | some cfg =>
    simp only [compile,hp] at he
    cases hb : (Mutable.Store.compile C E book prepared ci ei sources target cfg).1 with
    | none =>
      simp only [hb] at he
      change none=some entry at he
      cases he
    | some bank =>
      simp only [hb] at he
      have hentry : (⟨cfg,bank⟩ : Mutable.Store.Entry C E)=entry := Option.some.inj he
      subst entry
      exact ⟨rfl,hb⟩

theorem compile_reset_present (C E : DFA α) (book : ReplayMaps.Prepared C.stateCount E.stateCount)
    (prepared : Prepared C.stateCount E.stateCount) (hK : 0<prepared.K)
    (ci : BoundaryApplication.Range.Index C) (ei : BoundaryApplication.Range.Index E)
    (text : Array (Fin σ)) (fallback : Fin σ) (source target : Array Bool) (removed : List Nat)
    (partition : MaskedClusterLeaders.State h) (capacity L first base : Nat)
    (anchors : Array (Option Nat)) (window : SourceWindow)
    (hi : MaskedClusterLeaders.Invariant L partition) (hcap : capacity=2^h)
    (d : MaskedClusterDescriptor.Descriptor)
    (hd : (MaskedClusterDescriptor.describeLeader partition capacity first).1=some d)
    (hfull : Complete (ArrayText.read text fallback) text.size base L partition.occurrences.entries)
    (hL : 0<L) (ha : readAnchor anchors first L=L) :
    (compile C E book prepared ci ei partition capacity first L anchors window
      (MaskedRunCatalog.ofBatch target (MaskedMutableProgression.Batch.prepare text fallback source prepared.K))
      (MaskedSuffixClass.prepare text fallback)
      (MaskedMutableProgression.Batch.run text fallback source prepared.K removed) target).1.isSome=true := by
  by_cases hm : d.repetitions=0
  · rw [compile,prepare_singleton partition capacity first L anchors window _ _ d hd hm]
    simp only [Mutable.Store.compile,hm,if_true,Option.map_some,Option.isSome_some]
    rfl
  · obtain ⟨R,id,hcfg,hrow,_,hperiod,hbase,hend⟩:=prepare_dense_reset text fallback source target
      prepared.K partition capacity L first base anchors window hi hcap d hd hfull hL (by omega) ha
    let sources:=MaskedMutableProgression.Batch.run text fallback source prepared.K removed
    have hv:=MaskedMutableProgression.Batch.run_valid text fallback source prepared.K hK removed
    have hrow' : sources.runs[id]?=some R := by
      change (MaskedMutableProgression.Batch.eraseMany removed
        (MaskedMutableProgression.Batch.prepare text fallback source prepared.K)).runs[id]?=some R
      rw [MaskedMutableProgression.Batch.eraseMany_runs]
      exact hrow
    obtain ⟨idx,hidx,_⟩:=hv.rows id R hrow'
    have hidx' : sources.indexes[id]?=some idx := hidx
    have hmod : sources.modulus=prepared.K :=
      MaskedMutableProgression.Batch.eraseMany_modulus removed _
    have hcover : R.period=d.period ∧ R.lo≤d.first ∧ d.last+L≤R.hi+1 :=
      ⟨hperiod,hbase,by omega⟩
    rw [compile,hcfg]
    change ((Mutable.Store.compile C E book prepared ci ei sources target
      ⟨d,L,L,(incoming partition capacity first L anchors).cursor,
        (incoming partition capacity first L anchors).enabled,window,some id,
        (MaskedRunCatalog.entry target prepared.K R).counts⟩).1.map _).isSome=true
    simp only [Mutable.Store.compile,hm,if_false,hrow',hcover,if_true,true_and,
      Mutable.Batch.compileRun,hmod,hidx',Option.map,Option.isSome]

end REWB.MaskedTraversalBankReady
