import REWB.MaskedAllStart
import REWB.MaskedTraversalDriverCost
import REWB.MaskedSuffixClassCost

/-! All returned preparation counters of the public all-start entry
point, including initialization/source fanout, shared suffix classes,
catalog, identity tree, actual geometric Driver, C/E ranges and the joint
cut index. This inherits the explicitly limited initial periodic ledger;
the complete executed-band and finite-construction charges are separate.
-/
namespace REWB.MaskedAllStart
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedTraversalAggregate
variable {σ : Nat}

def geometryBudget (h n : Nat) : Nat :=
  h+1+(521*h+810)*((n+1)*(n+1).log2+(n+1))+(196*h+354)*(n+1)

def templateBudget (C E : DFA (Fin σ)) (h : Nat) : Nat :=
  2^h*(Tree.joinBudget (2*ReplayMaps.count C.stateCount E.stateCount) (2*(MaskedClusterStage.dfa C E).stateCount)+
    Tree.leafBudget (2*ReplayMaps.count C.stateCount E.stateCount) (2*(MaskedClusterStage.dfa C E).stateCount))+h+1

def preparationBudget (B C E : DFA (Fin σ)) (n : Nat) : Nat :=
  let h:=MaskedSuffixClass.height n
  MaskedTraversalInitial.initialBudget B C E n+
    (32*(σ+2)+830)*(n+1)*((n+1).log2+1)^2+401*(n+1)*((n+1).log2+1)^2+
    templateBudget C E h+geometryBudget h n+
    C.stateCount*((n.log2+1)*n)+n*C.stateCount+
    E.stateCount*((n.log2+1)*n)+n*E.stateCount+(n.log2+1)*n+20*(n+1)+h+20

theorem prepare_work (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) :
    (prepare B C E text fallback source target).preparationWork≤preparationBudget B C E text.size := by
  let K:=MaskedCluster.modulus C.stateCount E.stateCount
  let h:=MaskedSuffixClass.height text.size
  have hi:=MaskedTraversalInitial.start_accountedWork B C E text fallback source target K
    (MaskedCluster.modulus_pos C.stateCount E.stateCount)
  have hs:=MaskedSuffixClass.prepare_work_closed text fallback
  have hcat : (MaskedRunCatalog.ofBatch target (MaskedTraversalInitial.start B C E text fallback source target K).sources).work≤
      401*(text.size+1)*((text.size+1).log2+1)^2 := by
    change (MaskedRunCatalog.ofBatch target (MaskedMutableProgression.Batch.eraseMany _ _)).work≤_
    rw [MaskedRunCatalog.ofBatch_eraseMany]
    exact MaskedRunCatalog.ofBatch_work_closed text fallback source target K
  have ht:=MaskedTraversalAggregate.prepare_work C E h
  have hd:=MaskedTraversalDriver.suffix_work text fallback h (MaskedSuffixClass.height_capacity text.size)
  have hc:=BoundaryApplication.Range.build_products C text.toList
  have he:=BoundaryApplication.Range.build_products E text.toList
  have hcut:=Cut.build_products B C E text.toList
  simp only [Array.length_toList] at hc he hcut
  change (MaskedTraversalInitial.start B C E text fallback source target K).accountedWork+
    (MaskedSuffixClass.prepare text fallback).work+
    (MaskedRunCatalog.ofBatch target (MaskedTraversalInitial.start B C E text fallback source target K).sources).work+
    (MaskedTraversalAggregate.prepare C E h).work+
    (MaskedTraversalDriver.run h (MaskedRunDiscovery.prepareSuffixes text fallback).trie.tree).work+
    C.stateCount*(BoundaryApplication.Range.build C text.toList).products+text.size*C.stateCount+
    E.stateCount*(BoundaryApplication.Range.build E text.toList).products+text.size*E.stateCount+
    (Cut.build B C E text.toList).products+20*(text.size+1)+h+20≤_
  rw [hc,he,hcut]
  dsimp only [preparationBudget,templateBudget,geometryBudget]
  dsimp only [h] at ht hd ⊢
  omega

end REWB.MaskedAllStart
