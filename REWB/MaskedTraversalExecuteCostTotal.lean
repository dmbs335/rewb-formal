import REWB.MaskedTraversalExecuteCostPlan
import REWB.MaskedAllStartCorrect
import REWB.MaskedAllStartCost

/-! Public-solver accounting, with the actual source-fanout trace and the
actual number of new reports. The execution bound has no supplied event,
repair, query or output budget. It includes the complete Execute counter
and the source-update delta used by MaskedAllStart.solve. The preparation
ledger's separately documented finite-construction scope is inherited. -/
namespace REWB.MaskedTraversalExecute.Cost
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedTraversalAggregate
variable {σ : Nat}

theorem eraseMany_update_mono (ps : List Nat) (st : MaskedMutableProgression.Batch.State) :
    st.updateWork≤(MaskedMutableProgression.Batch.eraseMany ps st).updateWork := by
  induction ps generalizing st with
  | nil=>exact Nat.le_refl _
  | cons p ps ih=>
    have next:=ih (MaskedMutableProgression.Batch.eraseSource p st)
    change st.updateWork≤(MaskedMutableProgression.Batch.eraseMany ps (MaskedMutableProgression.Batch.eraseSource p st)).updateWork
    have one : st.updateWork≤(MaskedMutableProgression.Batch.eraseSource p st).updateWork := by
      unfold MaskedMutableProgression.Batch.eraseSource
      simp only
      omega
    exact Nat.le_trans one next

theorem solve_source_trace (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) :
    ∃ps,(MaskedAllStart.solve B C E text fallback source target).output.global.store.sources=
      MaskedMutableProgression.Batch.run text fallback source (MaskedCluster.modulus C.stateCount E.stateCount) ps := by
  have preserved:=MaskedAllStart.solve_preserves B C E text fallback source target
  obtain ⟨ps,erased,_,_⟩:=preserved.2.1.erases
  let initial:=MaskedTraversalInitial.start B C E text fallback source target (MaskedCluster.modulus C.stateCount E.stateCount)
  refine ⟨initial.answers.history++ps,?_⟩
  rw [erased]
  change MaskedMutableProgression.Batch.eraseMany ps
    (MaskedMutableProgression.Batch.run text fallback source (MaskedCluster.modulus C.stateCount E.stateCount) initial.answers.history)=_
  simp only [MaskedMutableProgression.Batch.run,MaskedMutableProgression.Batch.eraseMany,List.foldl_append]

theorem solve_delivered (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) :
    (MaskedAllStart.solve B C E text fallback source target).output.global.store.sources.delivered≤
      6*text.size*(text.size.log2+1) := by
  obtain ⟨ps,trace⟩:=solve_source_trace B C E text fallback source target
  rw [trace]
  exact MaskedMutableProgression.Batch.run_delivered text fallback source _
    (MaskedCluster.modulus_pos C.stateCount E.stateCount) ps

theorem solve_update_mono (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) :
    (MaskedAllStart.prepare B C E text fallback source target).initialSourceWork≤
      (MaskedAllStart.solve B C E text fallback source target).output.global.store.sources.updateWork := by
  obtain ⟨ps,erased,_,_⟩:=(MaskedAllStart.solve_preserves B C E text fallback source target).2.1.erases
  rw [erased]
  exact eraseMany_update_mono ps _

theorem solve_reported (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) :
    (MaskedAllStart.solve B C E text fallback source target).output.global.stats.reported≤text.size+1 := by
  let p:=MaskedAllStart.prepare B C E text fallback source target
  have hh:=plan_reported p.env p.template.capacity p.template p.geometry.plan p.global
  have bound:=MaskedAllStart.solve_count B C E text fallback source target
  change (MaskedAllStart.solve B C E text fallback source target).output.global.stats.reported+p.global.answers.count=
    0+(MaskedAllStart.solve B C E text fallback source target).output.global.answers.count at hh
  omega

def executionBudget (B C E : DFA (Fin σ)) (n : Nat) : Nat :=
  let h:=MaskedSuffixClass.height n
  let K:=MaskedCluster.modulus C.stateCount E.stateCount
  let D:=MaskedTraversalRepairCoherence.repairBudget C E K n h
  let V:=(n+1)*(n+1).log2+(n+1)
  markBudget h D*(5*V)+bandBudget B C E K h n*(4*V+2*(n+1))+18*(n+1)+
    outputBudget B C E K h n*(n+1)+(6*n*(n.log2+1))*MaskedMutableProgression.Batch.rowBudget n

theorem solve_execution_work (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) :
    let prepared:=MaskedAllStart.prepare B C E text fallback source target
    let out:=(MaskedAllStart.solve B C E text fallback source target).output
    out.global.stats.work+(out.global.store.sources.updateWork-prepared.initialSourceWork)≤
      executionBudget B C E text.size := by
  let prepared:=MaskedAllStart.prepare B C E text fallback source target
  let out:=(MaskedAllStart.solve B C E text fallback source target).output
  let h:=MaskedSuffixClass.height text.size
  let K:=MaskedCluster.modulus C.stateCount E.stateCount
  let D:=MaskedTraversalRepairCoherence.repairBudget C E K text.size h
  let R:=MaskedMutableProgression.Batch.rowBudget text.size
  let U:=outputBudget B C E K h text.size
  let V:=(text.size+1)*(text.size+1).log2+(text.size+1)
  have charged:=suffix_charged text fallback source prepared.env (MaskedAllStart.prepare_static B C E text fallback source target)
    prepared.template.capacity (MaskedAllStart.prepare_capacity B C E text fallback source target)
    (MaskedSuffixClass.height_capacity text.size) prepared.global (MaskedAllStart.prepare_global B C E text fallback source target)
  change actualWork out.global+credit R U prepared.global≤actualWork prepared.global+credit R U out.global+
    markBudget h D*(5*V)+bandBudget B C E K h text.size*(4*V+2*(text.size+1))+18*(text.size+1) at charged
  have report:=Nat.mul_le_mul_left U (solve_reported B C E text fallback source target)
  have fanout:=Nat.mul_le_mul_right R (solve_delivered B C E text fallback source target)
  have updates:=solve_update_mono B C E text fallback source target
  have zero : prepared.global.stats.work=0 := rfl
  have first : prepared.global.store.sources.updateWork=prepared.initialSourceWork := rfl
  unfold actualWork credit at charged
  rw [zero,first,Nat.zero_add] at charged
  change out.global.stats.work+(out.global.store.sources.updateWork-prepared.initialSourceWork)≤
    markBudget h D*(5*V)+bandBudget B C E K h text.size*(4*V+2*(text.size+1))+18*(text.size+1)+
      U*(text.size+1)+(6*text.size*(text.size.log2+1))*R
  change U*out.global.stats.reported≤_ at report
  change out.global.store.sources.delivered*R≤_ at fanout
  change prepared.initialSourceWork≤out.global.store.sources.updateWork at updates
  omega

theorem solve_accountedWork (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) :
    (MaskedAllStart.solve B C E text fallback source target).accountedWork≤
      MaskedAllStart.preparationBudget B C E text.size+executionBudget B C E text.size := by
  have initial:=MaskedAllStart.prepare_work B C E text fallback source target
  have executed:=solve_execution_work B C E text fallback source target
  change (MaskedAllStart.prepare B C E text fallback source target).preparationWork+
    (MaskedAllStart.solve B C E text fallback source target).output.global.stats.work+
    ((MaskedAllStart.solve B C E text fallback source target).output.global.store.sources.updateWork-
      (MaskedAllStart.prepare B C E text fallback source target).initialSourceWork)≤_
  dsimp only at executed
  omega

theorem solve_actionBuilds (B C E : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (source target : Array Bool) :
    (MaskedAllStart.solve B C E text fallback source target).fixedPatternBuilds≤
      4*((text.size+1)*(text.size+1).log2+(text.size+1))+2*(text.size+1)+1 := by
  let p:=MaskedAllStart.prepare B C E text fallback source target
  have counted:=plan_actions p.env p.template.capacity p.template p.geometry.plan p.global
  have volume:=suffix_volume text fallback (MaskedSuffixClass.height text.size) (MaskedSuffixClass.height_capacity text.size)
  change (MaskedAllStart.solve B C E text fallback source target).output.global.stats.actionBuilds=
    0+scheduledBands (MaskedTraversalDriver.run (MaskedSuffixClass.height text.size) (MaskedRunDiscovery.prepareSuffixes text fallback).trie.tree).plan at counted
  change (MaskedAllStart.solve B C E text fallback source target).output.global.stats.actionBuilds+1≤_
  dsimp only at volume
  omega

end REWB.MaskedTraversalExecute.Cost
