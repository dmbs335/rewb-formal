import REWB.MaskedTraversalExecuteSupport
import REWB.MaskedTraversalPositiveCoverageGeometry

/-! Proof invariants of the actual executor. A suspended frame records
pending geometry and physical candidate/write support, not completeness
of its temporary parent-depth occurrence class. Complete-band metadata
comes independently from the actual suffix plan.
-/
namespace REWB.MaskedTraversalExecute
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedTraversalAggregate
open REWB.MaskedTraversalRepairCoherence REWB.MaskedClusterDescriptor
variable {σ h : Nat} {B C E : DFA (Fin σ)}

structure Static (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool)
    (env : Env B C E text.size (MaskedSuffixClass.height text.size)) : Prop where
  catalog : env.repair.catalog=MaskedRunCatalog.ofBatch env.repair.shared.target
    (MaskedMutableProgression.Batch.prepare text fallback source env.repair.shared.prepared.K)
  classes : env.repair.classes=MaskedSuffixClass.prepare text fallback
  cRanges : env.repair.shared.cRanges=BoundaryApplication.Range.build C text.toList
  eRanges : env.repair.shared.eRanges=BoundaryApplication.Range.build E text.toList
  cut : env.cut=Cut.build B C E text.toList
  window : env.repair.window=⟨true,0,text.size+1⟩

structure Global.Valid (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool)
    (env : Env B C E text.size (MaskedSuffixClass.height text.size)) (global : Global C E) : Prop where
  sources : MaskedMutableProgression.Batch.Valid source global.answers.history global.store.sources
  size : global.store.sources.n=text.size
  modulus : global.store.sources.modulus=env.repair.shared.prepared.K
  runs : global.store.sources.runs=(MaskedMutableProgression.Batch.prepare text fallback source env.repair.shared.prepared.K).runs
  slots : text.size<global.store.slots.size
  anchors : text.size<global.anchors.size
  answers : MaskedTraversalAnswers.Valid text.size
    (fun p=>MaskedProgression.readMask source p=true ∧ Spec.maskedStart B C E text.toList (MaskedProgression.readMask env.repair.shared.target) p)
    global.answers

structure State.Valid (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool)
    (env : Env B C E text.size (MaskedSuffixClass.height text.size))
    (partition : MaskedClusterLeaders.State h) (capacity L : Nat) (st : State C E h) : Prop where
  global : st.global.Valid text fallback source env
  dirty : st.frame.dirty.keys.Valid
  dirtySupport : DirtySupported partition.occurrences.entries st.frame.dirty
  tree : st.frame.tree.Good
  own : MaskedTraversalRetained.Away partition capacity (ArrayText.read text fallback) text.size L st.global.anchors st.frame.dirty.keys.positions
  entries : ∃entries,Cells.Represents st.frame.tree entries ∧
    Pending env.repair partition capacity L st.global.anchors st.frame.dirty st.global.store entries ∧
      Cells.Unclipped text.size entries ∧ Supported partition.occurrences.entries entries

theorem State.Valid.with_stats (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool)
    (env : Env B C E text.size (MaskedSuffixClass.height text.size))
    (partition : MaskedClusterLeaders.State h) (capacity L : Nat) (st : State C E h)
    (hv : st.Valid text fallback source env partition capacity L) (stats : Stats) :
    ({st with global:={st.global with stats:=stats}} : State C E h).Valid text fallback source env partition capacity L := by
  rcases hv with ⟨gv,hd,hs,hg,ha,he⟩
  exact ⟨⟨gv.sources,gv.size,gv.modulus,gv.runs,gv.slots,gv.anchors,gv.answers⟩,hd,hs,hg,ha,he⟩

theorem snapshot (text : Array (Fin σ)) (fallback : Fin σ) (source : Array Bool)
    (env : Env B C E text.size (MaskedSuffixClass.height text.size)) (hs : Static text fallback source env)
    (capacity : Nat) (hc : capacity=2^h) (b : MaskedTraversalEdge.Band h) (st : State C E h)
    (hg : st.global.Valid text fallback source env)
    (hm : MaskedTraversalPositiveCoverage.Metadata text fallback capacity b) :
    Snapshot text fallback source st.global.answers.history env.repair b.snapshot capacity b.hi (representative b) st.global.store :=
  ⟨hs.catalog,hs.classes,hg.sources,hg.size,hg.modulus,hg.runs,hm.valid.invariant,hc,
    hm.complete b.hi hm.valid.bounds (Nat.le_refl _),by have hh:=hm.positive; have hb:=hm.valid.bounds; omega,hg.slots⟩

theorem apply_anchor_size (env : MaskedTraversalRepairCoherence.Env C E n h')
    (partition : MaskedClusterLeaders.State h) (capacity L : Nat) (anchors : Array (Option Nat))
    (dirty : MaskedTraversalDirty.Marked h) (st : Mutable.Store.State C E) (tree : BankTree C E h) :
    (MaskedTraversalRepairCoherence.apply env partition capacity L anchors dirty st tree).anchors.size=anchors.size :=
  MaskedTraversalRepair.anchorsLoop_size L dirty.keys.positions anchors 0

theorem refreshCurrent_size (env : Clip.Env C E) (first old : Nat)
    (st : Mutable.Store.State C E) (tree : BankTree C E h) :
    (refreshCurrent env first old st tree).store.slots.size=st.slots.size := by
  unfold refreshCurrent
  split
  · rfl
  · dsimp only
    split
    · rfl
    · exact Array.size_setIfInBounds

theorem eraseCurrent_size (env : Clip.Env C E) (partition : MaskedClusterLeaders.State h) (capacity old p : Nat)
    (st : Mutable.Store.State C E) (tree : BankTree C E h) :
    (eraseCurrent env partition capacity old p st tree).store.slots.size=st.slots.size := by
  unfold eraseCurrent
  dsimp only
  split
  · rfl
  · exact refreshCurrent_size env _ old _ tree

theorem eraseMany_size (env : Clip.Env C E) (partition : MaskedClusterLeaders.State h) (capacity old : Nat)
    (ps : List Nat) (st : Mutable.Store.State C E) (tree : BankTree C E h) :
    (eraseMany env partition capacity old ps st tree).store.slots.size=st.slots.size := by
  have go : ∀(ps : List Nat) (acc : SourceChange C E h),
      (ps.foldl (eraseStep env partition capacity old) acc).store.slots.size=acc.store.slots.size := by
    intro ps
    induction ps with
    | nil=>intro acc; rfl
    | cons p ps ih=>
      intro acc
      rw [List.foldl_cons,ih]
      exact eraseCurrent_size env partition capacity old p acc.store acc.tree
  exact go ps ⟨st,tree,true,0,0⟩

end REWB.MaskedTraversalExecute
