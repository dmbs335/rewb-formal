import REWB.MaskedTraversalExecuteCostTotal
import REWB.MaskedAllStartGrowth

/-! Fixed-pattern envelopes for the actual public execution counters.
The coefficient is independent of text, masks and grid width. A separate
arbitrary fixed charge can account for each explicitly counted finite
action construction; no length-dependent construction is hidden there.
The remaining finite periodic compiler ledger is inherited from Initial.
-/
namespace REWB.MaskedTraversalExecute.Cost
open REWB.ResidualCached.Growth
open REWB.MaskedCluster REWB.MaskedFiniteAction REWB.MaskedTraversalAggregate
variable {σ : Nat}

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

/-- Replace the one length-dependent maximum in the mutable bank limit
by the sum of its two explicitly counted branches. -/
def bankEnvelope (C E : DFA (Fin σ)) (K n : Nat) : Nat :=
  let levels:=MaskedMutableProgression.height (n+1)
  2*denseRowPrepBudget C E n+2*pointRowPrepBudget C E n+
    (C.stateCount+E.stateCount+16*(n.log2+2)+6)+
    (2*ReplayMaps.count C.stateCount E.stateCount)*
      (C.stateCount+E.stateCount+
        4*((1+C.stateCount+E.stateCount)*((1+C.stateCount+E.stateCount)*
          (Mutable.cellBudget C E K levels+4+(4*levels+26)+1)))+
        (2*(1+C.stateCount+E.stateCount))*((2*(1+C.stateCount+E.stateCount))*11)+7)+
      Mutable.pointBankBudget C E levels+21

theorem bank_envelope (C E : DFA (Fin σ)) (K n : Nat) :
    Mutable.Store.bankLimit C E K n≤bankEnvelope C E K n := by
  have hm : Mutable.rowBudget C E K (MaskedMutableProgression.height (n+1))≤
      Mutable.cellBudget C E K (MaskedMutableProgression.height (n+1))+4+
        (4*MaskedMutableProgression.height (n+1)+26) := by
    unfold Mutable.rowBudget
    exact Nat.max_le.mpr ⟨Nat.le_add_right _ _,Nat.le_add_left _ _⟩
  simp only [Mutable.Store.bankLimit,bankEnvelope,Mutable.denseBankBudget]
  apply Nat.add_le_add_right
  apply Nat.add_le_add_right
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_left
  apply Nat.add_le_add_right
  apply Nat.add_le_add_right
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_left
  apply Nat.mul_le_mul_left
  apply Nat.mul_le_mul_left
  exact Nat.add_le_add_right hm 1

/-- The exact execution formula with its single bank-limit value exposed
as a scalar, for a monotonicity proof rather than a cost premise. -/
def usingBank (B C E : DFA (Fin σ)) (n bank : Nat) : Nat :=
  let h:=MaskedSuffixClass.height n
  let replace:=(h+1)*Tree.replaceBudget (2*ReplayMaps.count C.stateCount E.stateCount)
    (2*(MaskedClusterStage.dfa C E).stateCount)
  let D:=209*h+52*MaskedRunCatalog.width n+313+2*bank+2*MaskedTraversalRepairCoherence.refreshBudget C E h
  let A:=14*h+17+2*(bank+replace+10)+Reporting.regionBudget C E h+
    ReplayMaps.count C.stateCount E.stateCount*(E.stateCount+1)+3+3*(n.log2+2)+
      (MaskedCut.DFAIndex.jointEnum B C E).elems.length*(MaskedCut.DFAIndex.jointEnum B C E).elems.length+11
  let Q:=11*h+25+bank+replace+MaskedMutableProgression.Batch.requestBudget n
  let F:=A+replayBudget C E n+Tree.reindexBudget (2*ReplayMaps.count C.stateCount E.stateCount)
    (2*(MaskedClusterStage.dfa C E).stateCount)+62
  let U:=(2*A+41)*h+Q+6
  let V:=(n+1)*(n+1).log2+(n+1)
  markBudget h D*(5*V)+F*(4*V+2*(n+1))+18*(n+1)+U*(n+1)+
    (6*n*(n.log2+1))*MaskedMutableProgression.Batch.rowBudget n

theorem usingBank_mono (B C E : DFA (Fin σ)) (n a b : Nat) (hab : a≤b) : usingBank B C E n a≤usingBank B C E n b := by
  let h:=MaskedSuffixClass.height n
  let replace:=(h+1)*Tree.replaceBudget (2*ReplayMaps.count C.stateCount E.stateCount)
    (2*(MaskedClusterStage.dfa C E).stateCount)
  let D:=fun bank=>209*h+52*MaskedRunCatalog.width n+313+2*bank+
    2*MaskedTraversalRepairCoherence.refreshBudget C E h
  let A:=fun bank=>14*h+17+2*(bank+replace+10)+Reporting.regionBudget C E h+
    ReplayMaps.count C.stateCount E.stateCount*(E.stateCount+1)+3+3*(n.log2+2)+
      (MaskedCut.DFAIndex.jointEnum B C E).elems.length*(MaskedCut.DFAIndex.jointEnum B C E).elems.length+11
  let Q:=fun bank=>11*h+25+bank+replace+MaskedMutableProgression.Batch.requestBudget n
  let F:=fun bank=>A bank+replayBudget C E n+
    Tree.reindexBudget (2*ReplayMaps.count C.stateCount E.stateCount)
      (2*(MaskedClusterStage.dfa C E).stateCount)+62
  let U:=fun bank=>(2*A bank+41)*h+Q bank+6
  let V:=(n+1)*(n+1).log2+(n+1)
  have hd : D a≤D b := by dsimp only [D]; omega
  have ha : A a≤A b := by dsimp only [A]; omega
  have hq : Q a≤Q b := by dsimp only [Q]; omega
  have hf : F a≤F b := by dsimp only [F]; omega
  have hu : U a≤U b := by
    dsimp only [U]
    exact Nat.add_le_add_right (Nat.add_le_add
      (Nat.mul_le_mul_right h (Nat.add_le_add_right (Nat.mul_le_mul_left 2 ha) 41)) hq) 6
  have hm : markBudget h (D a)≤markBudget h (D b) := by
    dsimp only [markBudget]; omega
  change markBudget h (D a)*(5*V)+F a*(4*V+2*(n+1))+18*(n+1)+U a*(n+1)+
      (6*n*(n.log2+1))*MaskedMutableProgression.Batch.rowBudget n≤
    markBudget h (D b)*(5*V)+F b*(4*V+2*(n+1))+18*(n+1)+U b*(n+1)+
      (6*n*(n.log2+1))*MaskedMutableProgression.Batch.rowBudget n
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add_right
    (Nat.add_le_add (Nat.mul_le_mul_right (5*V) hm)
      (Nat.mul_le_mul_right (4*V+2*(n+1)) hf)) (18*(n+1)))
    (Nat.mul_le_mul_right (n+1) hu)) _

theorem execution_envelope (B C E : DFA (Fin σ)) (n : Nat) :
    executionBudget B C E n≤usingBank B C E n (bankEnvelope C E (MaskedCluster.modulus C.stateCount E.stateCount) n) := by
  exact usingBank_mono B C E n _ _ (bank_envelope C E _ n)

theorem execution_profile (B C E : DFA (Fin σ)) :
    ∃coefficient,∀n s,Bound n s (executionBudget B C E n) 1 0 0 3 coefficient := by
  have envelope : ∃coefficient,∀n s,Bound n s
      (usingBank B C E n (bankEnvelope C E (MaskedCluster.modulus C.stateCount E.stateCount) n)) 1 0 0 3 coefficient := by
    refine ⟨?C,?proof⟩
    case proof=>
      intro n s
      residual_growth
  obtain ⟨coefficient,hc⟩:=envelope
  exact ⟨coefficient,fun n s=>Nat.le_trans (execution_envelope B C E n) (hc n s)⟩

def actionBudget (n : Nat) : Nat := 4*((n+1)*(n+1).log2+(n+1))+2*(n+1)+1

theorem charged_profile (B C E : DFA (Fin σ)) (fixedCharge : Nat) :
    ∃coefficient,∀n s,Bound n s (executionBudget B C E n+fixedCharge*actionBudget n) 1 0 0 3 coefficient := by
  have actions : ∃coefficient,∀n s,Bound n s (fixedCharge*actionBudget n) 1 0 0 1 coefficient := by
    refine ⟨?C,?proof⟩
    case proof=>
      intro n s
      residual_growth
  obtain ⟨ce,he⟩:=execution_profile B C E
  obtain ⟨ca,ha⟩:=actions
  exact ⟨ce+ca,fun n s=>REWB.ResidualCached.Growth.add (he n s) (ha n s)⟩

theorem solve_work_closed (B C E : DFA (Fin σ)) :
    ∃coefficient,∀(text : Array (Fin σ)) (fallback : Fin σ) (source target : Array Bool),
      (MaskedAllStart.solve B C E text fallback source target).accountedWork≤
        coefficient*(text.size+2)*((text.size+2).log2+1)^3 := by
  obtain ⟨cp,hp⟩:=MaskedAllStart.preparation_profile B C E
  obtain ⟨ce,he⟩:=execution_profile B C E
  refine ⟨cp+ce,?_⟩
  intro text fallback source target
  have growth:=REWB.ResidualCached.Growth.add (hp text.size 1) (he text.size 1)
  have actual:=Nat.le_trans (solve_accountedWork B C E text fallback source target) growth
  simpa only [Bound,scale,Nat.max_self,show max 2 3=3 by decide,Nat.pow_one,Nat.pow_zero,Nat.mul_one,height,Nat.mul_assoc] using actual

theorem solve_charged_work_closed (B C E : DFA (Fin σ)) (fixedCharge : Nat) :
    ∃coefficient,∀(text : Array (Fin σ)) (fallback : Fin σ) (source target : Array Bool),
      (MaskedAllStart.solve B C E text fallback source target).accountedWork+
        fixedCharge*(MaskedAllStart.solve B C E text fallback source target).fixedPatternBuilds≤
          coefficient*(text.size+2)*((text.size+2).log2+1)^3 := by
  obtain ⟨cp,hp⟩:=MaskedAllStart.preparation_profile B C E
  obtain ⟨ce,he⟩:=charged_profile B C E fixedCharge
  refine ⟨cp+ce,?_⟩
  intro text fallback source target
  have growth:=REWB.ResidualCached.Growth.add (hp text.size 1) (he text.size 1)
  have actions:=Nat.mul_le_mul_left fixedCharge (solve_actionBuilds B C E text fallback source target)
  have raw:=solve_accountedWork B C E text fallback source target
  have actual : (MaskedAllStart.solve B C E text fallback source target).accountedWork+
      fixedCharge*(MaskedAllStart.solve B C E text fallback source target).fixedPatternBuilds≤
        MaskedAllStart.preparationBudget B C E text.size+(executionBudget B C E text.size+fixedCharge*actionBudget text.size) := by
    dsimp only [actionBudget]
    omega
  have bound:=Nat.le_trans actual growth
  simpa only [Bound,scale,Nat.max_self,show max 2 3=3 by decide,Nat.pow_one,Nat.pow_zero,Nat.mul_one,height,Nat.mul_assoc] using bound

end REWB.MaskedTraversalExecute.Cost
