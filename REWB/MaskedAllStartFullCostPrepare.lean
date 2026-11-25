import REWB.MaskedAllStartFullCostFiniteInitial
import REWB.MaskedAllStartGrowth
import REWB.MaskedFiniteConstruction

/-! Construct the actual all-start environment with measured periodic
initialization, finite Cut construction, fixed-pattern modulus and replay
catalog. The first projection preserves every field of the published
prepared environment. The conservative ledger includes both its existing
counters and the executed replacement work. -/
namespace REWB.MaskedAllStart.FullCost
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedTraversalAggregate
open REWB.ResidualCached.Growth
variable {σ : Nat}

def prepare (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) : PeriodicConstruction.Result (MaskedAllStart.Prepared B C E text.size) :=
  let n:=text.size
  let h:=MaskedSuffixClass.height n
  let ⟨prepared,clusterWork⟩:=PeriodicConstruction.Pattern.prepareCluster C.stateCount E.stateCount
  let ⟨started,startWork⟩:=FiniteInitial.start B C E text fallback source target prepared.K
  let classes:=MaskedSuffixClass.prepare text fallback
  let catalog:=MaskedRunCatalog.ofBatch target started.sources
  let ci:=BoundaryApplication.Range.build C text.toList
  let ei:=BoundaryApplication.Range.build E text.toList
  let ⟨built,cutWork⟩:=PeriodicConstruction.Cut.buildDFA B C E text.toList
  let cut : Cut.Shared B C E:=⟨built.1,text.toList.length,built.2⟩
  let ⟨book,bookWork⟩:=MaskedFiniteConstruction.prepare C.stateCount E.stateCount
  let repair : MaskedTraversalRepairCoherence.Env C E n h:=
    ⟨⟨book,prepared,ci,ei,target⟩,⟨true,0,n+1⟩,catalog,classes⟩
  let env : MaskedTraversalExecute.Env B C E n h:=⟨repair,cut⟩
  let template:=MaskedTraversalAggregate.prepare C E h
  let geometry:=MaskedTraversalDriver.run h classes.suffix.trie.tree
  let global : MaskedTraversalExecute.Global C E:=
    ⟨Array.replicate (n+1) none,Mutable.Store.empty C E started.sources,started.answers,{}⟩
  let out : MaskedAllStart.Prepared B C E n:=
    ⟨env,template,geometry,global,
      started.accountedWork+classes.work+catalog.work+template.work+geometry.work+
        C.stateCount*ci.products+ci.letterCells+E.stateCount*ei.products+ei.letterCells+
        cut.products+20*(n+1)+h+20,
      started.sources.updateWork⟩
  (out,out.preparationWork+startWork+cutWork+clusterWork+bookWork+n+15)

theorem prepare_value (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) :
    (prepare B C E text fallback source target).1=MaskedAllStart.prepare B C E text fallback source target := by
  simp only [prepare,PeriodicConstruction.Pattern.prepareCluster_value,FiniteInitial.start_value,
    PeriodicConstruction.Cut.buildDFA_value,MaskedFiniteConstruction.prepare_value,
    MaskedAllStart.prepare,Cut.build]

theorem prepare_work_eq (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) :
    (prepare B C E text fallback source target).2=
      (MaskedAllStart.prepare B C E text fallback source target).preparationWork+
      (FiniteInitial.start B C E text fallback source target
        (MaskedCluster.modulus C.stateCount E.stateCount)).2+
      (PeriodicConstruction.Cut.buildDFA B C E text.toList).2+
      PeriodicConstruction.Pattern.clusterCost C.stateCount E.stateCount+
      (MaskedFiniteConstruction.prepare C.stateCount E.stateCount).2+text.size+15 := by
  simp only [prepare,PeriodicConstruction.Pattern.prepareCluster_value,FiniteInitial.start_value,
    PeriodicConstruction.Cut.buildDFA_value,MaskedFiniteConstruction.prepare_value,
    PeriodicConstruction.Pattern.prepareCluster_work,MaskedAllStart.prepare,Cut.build] <;> rfl

def preparationBudget (B C E : DFA (Fin σ)) (n : Nat) : Nat :=
  MaskedAllStart.preparationBudget B C E n+FiniteInitial.initialBudget B C E n+
    PeriodicConstruction.Cut.buildDFACost B.stateCount C.stateCount E.stateCount n+
    PeriodicConstruction.Pattern.clusterCost C.stateCount E.stateCount+
    MaskedFiniteConstruction.prepareBudget C.stateCount E.stateCount+n+15

theorem prepare_work (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) :
    (prepare B C E text fallback source target).2≤preparationBudget B C E text.size := by
  have ho:=MaskedAllStart.prepare_work B C E text fallback source target
  have hi:=FiniteInitial.start_work B C E text fallback source target
    (MaskedCluster.modulus C.stateCount E.stateCount) (MaskedCluster.modulus_pos C.stateCount E.stateCount)
  have hc:=PeriodicConstruction.Cut.buildDFA_work B C E text.toList
  have hf:=MaskedFiniteConstruction.prepare_work C.stateCount E.stateCount
  simp only [Array.length_toList] at hc
  rw [prepare_work_eq]
  unfold preparationBudget
  omega

def preparationEnvelope (B C E : DFA (Fin σ)) (n : Nat) : Nat :=
  MaskedAllStart.preparationEnvelope B C E n+FiniteInitial.initialBudget B C E n+
    PeriodicConstruction.Cut.buildDFACost B.stateCount C.stateCount E.stateCount n+
    PeriodicConstruction.Pattern.clusterCost C.stateCount E.stateCount+
    MaskedFiniteConstruction.prepareBudget C.stateCount E.stateCount+n+15

theorem preparation_envelope (B C E : DFA (Fin σ)) (n : Nat) :
    preparationBudget B C E n≤preparationEnvelope B C E n := by
  have hh:=MaskedAllStart.preparation_envelope B C E n
  unfold preparationBudget preparationEnvelope
  omega

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem preparation_profile (B C E : DFA (Fin σ)) :
    ∃coefficient,∀n s,Bound n s (preparationBudget B C E n) 1 0 0 2 coefficient := by
  have envelope : ∃coefficient,∀n s,Bound n s (preparationEnvelope B C E n) 1 0 0 2 coefficient := by
    refine ⟨?C,?proof⟩
    case proof=>
      intro n s
      residual_growth
  obtain ⟨coefficient,hc⟩:=envelope
  exact ⟨coefficient,fun n s=>Nat.le_trans (preparation_envelope B C E n) (hc n s)⟩

theorem prepare_work_closed (B C E : DFA (Fin σ)) :
    ∃coefficient,∀(text : Array (Fin σ)) (fallback : Fin σ) (source target : Array Bool),
      (prepare B C E text fallback source target).2≤coefficient*(text.size+2)*(height text.size)^2 := by
  obtain ⟨coefficient,hc⟩:=preparation_profile B C E
  refine ⟨coefficient,?_⟩
  intro text fallback source target
  have hp:=Nat.le_trans (prepare_work B C E text fallback source target) (hc text.size 1)
  simpa only [Bound,scale,Nat.pow_one,Nat.pow_zero,Nat.mul_one,Nat.mul_assoc] using hp

theorem prepare_tiny (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) :
    PeriodicConstruction.Cut.Tiny (prepare B C E text fallback source target).1.env.cut.tree := by
  rw [prepare_value]
  exact PeriodicConstruction.Cut.dfaBuild_tiny B C E text.toList

theorem prepare_modulus (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) :
    (prepare B C E text fallback source target).1.env.repair.shared.prepared.K=
      MaskedCluster.modulus C.stateCount E.stateCount := by
  rw [prepare_value]
  rfl

end REWB.MaskedAllStart.FullCost
