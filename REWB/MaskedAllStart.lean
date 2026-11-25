import REWB.MaskedTraversalExecuteInvariant
import REWB.MaskedTraversalExecuteRuntime
import REWB.MaskedTraversalInitialCost
import REWB.MaskedRunCatalogCost

/-! Public construction and execution of the actual masked all-start
path. The caller supplies only the three DFAs, text and independent source
and target masks. Empty/periodic initialization, suffix classes, geometric
plan, shared ranges/cut, run catalog, identity template, global store and
anchors are all constructed internally.

The class index's retained suffix preparation is reused by the Driver.
Initialization snapshots are consumed rather than retained beside the
mutable execution state. The counter scope is the existing component
ledger, with fixed-pattern construction calls identified separately.
-/
namespace REWB.MaskedAllStart
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedTraversalAggregate
variable {σ : Nat}

structure Prepared (B C E : DFA (Fin σ)) (n : Nat) where
  env : MaskedTraversalExecute.Env B C E n (MaskedSuffixClass.height n)
  template : Template C E (MaskedSuffixClass.height n)
  geometry : MaskedTraversalDriver.Built (MaskedSuffixClass.height n)
  global : MaskedTraversalExecute.Global C E
  preparationWork : Nat
  initialSourceWork : Nat

def prepare (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) : Prepared B C E text.size :=
  let n:=text.size
  let h:=MaskedSuffixClass.height n
  let prepared:=MaskedCluster.prepare C.stateCount E.stateCount
  let started:=MaskedTraversalInitial.start B C E text fallback source target prepared.K
  let classes:=MaskedSuffixClass.prepare text fallback
  let catalog:=MaskedRunCatalog.ofBatch target started.sources
  let ci:=BoundaryApplication.Range.build C text.toList
  let ei:=BoundaryApplication.Range.build E text.toList
  let cut:=Cut.build B C E text.toList
  let repair : MaskedTraversalRepairCoherence.Env C E n h:=
    ⟨⟨ReplayMaps.prepare C.stateCount E.stateCount,prepared,ci,ei,target⟩,
      ⟨true,0,n+1⟩,catalog,classes⟩
  let env : MaskedTraversalExecute.Env B C E n h:=⟨repair,cut⟩
  let template:=MaskedTraversalAggregate.prepare C E h
  let geometry:=MaskedTraversalDriver.run h classes.suffix.trie.tree
  let global : MaskedTraversalExecute.Global C E:=
    ⟨Array.replicate (n+1) none,Mutable.Store.empty C E started.sources,started.answers,{}⟩
  ⟨env,template,geometry,global,
    started.accountedWork+classes.work+catalog.work+template.work+geometry.work+
      C.stateCount*ci.products+ci.letterCells+E.stateCount*ei.products+ei.letterCells+
      cut.products+20*(n+1)+h+20,
    started.sources.updateWork⟩

structure Result (C E : DFA (Fin σ)) (h : Nat) where
  output : MaskedTraversalExecute.State C E h
  accountedWork : Nat
  fixedPatternBuilds : Nat

def Result.bits {C E : DFA (Fin σ)} {h : Nat} (out : Result C E h) : Array Bool := out.output.global.answers.bits

def solve (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) : Result C E (MaskedSuffixClass.height text.size) :=
  let ⟨env,template,geometry,global,work,initialWork⟩:=prepare B C E text fallback source target
  let out:=MaskedTraversalExecute.plan env template.capacity template geometry.plan global
  ⟨out,work+out.global.stats.work+(out.global.store.sources.updateWork-initialWork),
    out.global.stats.actionBuilds+1⟩

theorem prepare_target (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) : (prepare B C E text fallback source target).env.repair.shared.target=target := rfl

theorem prepare_capacity (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) :
    (prepare B C E text fallback source target).template.capacity=2^(MaskedSuffixClass.height text.size) := rfl

theorem prepare_geometry (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) :
    (prepare B C E text fallback source target).geometry=
      MaskedTraversalDriver.run (MaskedSuffixClass.height text.size) (MaskedRunDiscovery.prepareSuffixes text fallback).trie.tree := rfl

theorem prepare_static (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) :
    MaskedTraversalExecute.Static text fallback source (prepare B C E text fallback source target).env := by
  refine ⟨?_,rfl,rfl,rfl,rfl,rfl⟩
  change MaskedRunCatalog.ofBatch target (MaskedMutableProgression.Batch.eraseMany _ _)=_
  rw [MaskedRunCatalog.ofBatch_eraseMany]
  rfl

theorem prepare_global (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) :
    (prepare B C E text fallback source target).global.Valid text fallback source
      (prepare B C E text fallback source target).env := by
  let K:=MaskedCluster.modulus C.stateCount E.stateCount
  have hK : 0<K:=MaskedCluster.modulus_pos C.stateCount E.stateCount
  refine ⟨MaskedTraversalInitial.start_valid B C E text fallback source target K hK,
    MaskedTraversalInitial.start_n B C E text fallback source target K,
    MaskedTraversalInitial.start_modulus B C E text fallback source target K,
    MaskedTraversalInitial.start_runs B C E text fallback source target K,?_,?_,
    MaskedTraversalInitial.start_answers_valid B C E text fallback source target K⟩
  · change text.size<(Array.replicate ((MaskedTraversalInitial.start B C E text fallback source target K).sources.n+1)
      (none : Option (Mutable.Store.Entry C E))).size
    rw [Array.size_replicate,MaskedTraversalInitial.start_n]
    omega
  · change text.size<(Array.replicate (text.size+1) (none : Option Nat)).size
    rw [Array.size_replicate]
    omega

theorem solve_output (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) :
    (solve B C E text fallback source target).output=
      let p:=prepare B C E text fallback source target
      MaskedTraversalExecute.plan p.env p.template.capacity p.template p.geometry.plan p.global := rfl

end REWB.MaskedAllStart
