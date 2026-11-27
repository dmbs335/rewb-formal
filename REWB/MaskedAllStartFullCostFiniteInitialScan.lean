import REWB.MaskedAllStartFullCostInitialScan
import REWB.PeriodicConstructionCutPhase
import REWB.PeriodicConstructionCutBuild

/-! Install finite cut products and tail construction into the actual
periodic source scan. The full old state and counters are preserved. -/
namespace REWB.MaskedAllStart.FullCost.FiniteInitial
open REWB.MaskedPeriodic REWB.MaskedPeriodic.Batch REWB.PeriodicConstruction
open REWB.MaskedCut REWB.MaskedCut.DFAIndex
variable {α : Type}

def one (B C E : DFA α) (prepared : PreparedPattern B.stateCount C.stateCount E.stateCount)
    (idx : Index.Tree (jointEnum B C E)) (n : Nat) (source target : Array Bool)
    (R : RunGeometry.Bounds) (out : Batch.State) : Result Batch.State :=
  let counts:=MaskedProgression.build target R.lo (span R) (prepared.K*R.period)
  let measuredTail:=Cut.prepareTail B C E idx R.hi n
  let tail:=measuredTail.1
  let prep:=counts.slots+counts.arithmetic+tail.products+tail.visits+5
  let ⟨next,work⟩:=Initial.scan
    (fun s=>Cut.query B C E prepared idx tail.map s R.hi R.period counts.counts R.lo)
    source (span R) R.lo {out with preparationWork:=out.preparationWork+prep}
  (next,work+prep+measuredTail.2+8)

theorem one_value (B C E : DFA α) (prepared : PreparedPattern B.stateCount C.stateCount E.stateCount)
    (idx : Index.Tree (jointEnum B C E)) (n : Nat) (source target : Array Bool)
    (R : RunGeometry.Bounds) (out : Batch.State) :
    (one B C E prepared idx n source target R out).1=
      Batch.one B C E prepared idx n source target R out := by
  simp only [one,Initial.scan_value,Cut.query_value,Cut.prepareTail_value,Batch.one,Nat.add_assoc]

def oneLimit (B C E : DFA α) (K n : Nat) : Nat :=
  Cut.queryCoefficient B.stateCount C.stateCount E.stateCount K*(queryLimit B C E n+1)+
    preparationLimit n+Cut.tailCoefficient B.stateCount C.stateCount E.stateCount*(n.log2+4)+25

theorem one_work (B C E : DFA α) (prepared : PreparedPattern B.stateCount C.stateCount E.stateCount)
    (w : Word α) (source target : Array Bool) (R : RunGeometry.Bounds)
    (hn : R.hi≤w.length) (out : Batch.State) :
    (one B C E prepared (DFAIndex.build B C E w).1 w.length source target R out).2≤
      oneLimit B C E prepared.K w.length*span R := by
  let counts:=MaskedProgression.build target R.lo (span R) (prepared.K*R.period)
  let tail:=Text.prepareTail B C E (DFAIndex.build B C E w).1 R.hi w.length
  let ask:=fun s=>Cut.query B C E prepared
    (DFAIndex.build B C E w).1 tail.map s R.hi R.period counts.counts R.lo
  let prep:=counts.slots+counts.arithmetic+tail.products+tail.visits+5
  have tiny:=Cut.dfaBuild_tiny B C E w
  have hb : ∀i,(ask i).2≤Cut.queryCoefficient B.stateCount C.stateCount E.stateCount
      prepared.K*(queryLimit B C E w.length+1) := by
    intro i
    have hc:=Cut.query_work B C E prepared
      (DFAIndex.build B C E w).1 tail.map i R.hi R.period counts.counts R.lo tiny
    have hq:=Batch.query_work B C E prepared w tail.map i R.hi R.period counts.counts R.lo hn
    exact Nat.le_trans hc (Nat.mul_le_mul_left _ (Nat.add_le_add_right hq 1))
  have hs:=Initial.scan_work ask source (span R) R.lo _
    {out with preparationWork:=out.preparationWork+prep} hb
  have hp:=MaskedProgression.build_work target R.lo (span R) (prepared.K*R.period)
  have ht:=Text.prepareTail_bounds B C E w R.hi hn
  change tail.products≤1 ∧ tail.visits≤w.length.log2+2 at ht
  have htail:=Cut.prepareTail_work B C E (DFAIndex.build B C E w).1 R.hi w.length tiny
  have htailBound : (Cut.prepareTail B C E (DFAIndex.build B C E w).1 R.hi w.length).2≤
      Cut.tailCoefficient B.stateCount C.stateCount E.stateCount*(w.length.log2+4) := by
    exact Nat.le_trans htail (Nat.mul_le_mul_left _ (by
      change tail.products+tail.visits+1≤w.length.log2+4
      omega))
  have hspan : 1≤span R := Nat.succ_le_succ (Nat.zero_le _)
  have hprep:=Nat.mul_le_mul_left (w.length.log2+8) hspan
  have hconstant:=Nat.mul_le_mul_left 9 hspan
  have htailSpan:=Nat.mul_le_mul_left
    (Cut.tailCoefficient B.stateCount C.stateCount E.stateCount*(w.length.log2+4)) hspan
  change counts.slots+counts.arithmetic≤13*span R at hp
  unfold one
  simp only [Cut.prepareTail_value]
  change (Initial.scan ask source (span R) R.lo
    {out with preparationWork:=out.preparationWork+prep}).2+prep+
      (Cut.prepareTail B C E (DFAIndex.build B C E w).1 R.hi w.length).2+8≤_
  unfold oneLimit preparationLimit
  dsimp only [prep] at hs ⊢
  simp only [Nat.mul_one,Nat.add_mul] at hs hprep hconstant htailSpan ⊢
  omega

end REWB.MaskedAllStart.FullCost.FiniteInitial
