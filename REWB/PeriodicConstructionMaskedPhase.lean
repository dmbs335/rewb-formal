import REWB.PeriodicConstructionMaskedTuple
import REWB.MaskedPeriodicBatchQueryCost

/-! Actual three-branch query with descriptor, projection and interval
construction included. Shared cut-index products and finite tuple
extraction retain their separate monoid-primitive accounting. This
module closes the formula-construction omission in the query ledger;
it does not silently identify a monoid product with one machine step.
-/
namespace REWB.PeriodicConstruction.Masked
open REWB.PeriodicConstruction REWB.MaskedPeriodic REWB.MaskedFiniteAction.Maps
open REWB.MaskedCut REWB.MaskedCut.DFAIndex
variable {α : Type}

def zeroTuple (B C E : DFA α) : Result (Joint B C E) :=
  let b:=tabulate B.stateCount (fun q=>(q,1))
  let c:=tabulate C.stateCount (fun q=>(q,1))
  let e:=tabulate E.stateCount (fun q=>(q,1))
  ((b.1,c.1,e.1),b.2+c.2+e.2+2)

theorem zeroTuple_value (B C E : DFA α) :
    (zeroTuple B C E).1=wordTuple B C E [] [] [] := by
  simp only [zeroTuple,tabulate_id,wordTuple,identity,wordMap,DFA.run]
  rfl

def zeroTupleCost (b c e : Nat) : Nat := 4*b+4*c+4*e+5

theorem zeroTuple_work (B C E : DFA α) :
    (zeroTuple B C E).2≤zeroTupleCost B.stateCount C.stateCount E.stateCount := by
  have hb:=tabulate_work (fun q : Fin B.stateCount=>(q,1)) 1 (fun _=>Nat.le_refl _)
  have hc:=tabulate_work (fun q : Fin C.stateCount=>(q,1)) 1 (fun _=>Nat.le_refl _)
  have he:=tabulate_work (fun q : Fin E.stateCount=>(q,1)) 1 (fun _=>Nat.le_refl _)
  simp only [Nat.reduceAdd,Nat.mul_comm _ 4] at hb hc he
  unfold zeroTuple zeroTupleCost
  dsimp only
  omega

def phaseQuery (B C E : DFA α) (prepared : PreparedPattern B.stateCount C.stateCount E.stateCount)
    (idx : Index.Tree (jointEnum B C E)) (tail : Map E.stateCount)
    (start eta q N : Nat) (counts : Array Nat) (base s : Nat) : Result IndexedAnswer :=
  let maps:=contexts B C E idx start eta q tail
  match maps.period,maps.after with
  | some period,some after =>
    let empty:=zeroTuple B C E
    let zero:=queryTuple B C E period empty.1 after .zero N counts base q s prepared.K
    let ci:=interiorTuples B C E idx start q
    let ce:=endingTuples B C E idx start eta q
    let interior:=tupleQuery B C E period after .interior N counts base q s prepared.K ci.values
    let ending:=tupleQuery B C E period tail .ending N counts base q s prepared.K ce.values
    (⟨joinAnswers zero.1 (joinAnswers interior.1 ending.1),
      maps.products+ci.products+ce.products,maps.visits+ci.visits+ce.visits⟩,
      empty.2+zero.2+interior.2+ending.2+maps.products+ci.products+ce.products+
        maps.visits+ci.visits+ce.visits+3*E.stateCount+20)
  | _,_ => (⟨⟨false,0,1⟩,maps.products,maps.visits⟩,maps.products+maps.visits+3*E.stateCount+5)

theorem phaseQuery_value (B C E : DFA α) (prepared : PreparedPattern B.stateCount C.stateCount E.stateCount)
    (idx : Index.Tree (jointEnum B C E)) (tail : Map E.stateCount)
    (start eta q N : Nat) (counts : Array Nat) (base s : Nat) :
    (phaseQuery B C E prepared idx tail start eta q N counts base s).1=
      MaskedPeriodic.phaseQuery B C E prepared idx tail start eta q N counts base s := by
  unfold phaseQuery MaskedPeriodic.phaseQuery
  dsimp only
  split <;> simp_all only [queryTuple_value,zeroTuple_value,tupleQuery_value,queryInterior,queryEnding]

def phaseExtra (b c e K : Nat) : Nat :=
  zeroTupleCost b c e+tupleConstructionCost b c e K+
    2*(b^b*(c^c*e^e))*(tupleConstructionCost b c e K+4)+3*e+40

theorem phaseQuery_extra (B C E : DFA α) (prepared : PreparedPattern B.stateCount C.stateCount E.stateCount)
    (idx : Index.Tree (jointEnum B C E)) (tail : Map E.stateCount)
    (start eta q N : Nat) (counts : Array Nat) (base s : Nat) :
    (phaseQuery B C E prepared idx tail start eta q N counts base s).2≤
      Batch.queryCost (MaskedPeriodic.phaseQuery B C E prepared idx tail start eta q N counts base s)+
      phaseExtra B.stateCount C.stateCount E.stateCount prepared.K := by
  unfold phaseQuery MaskedPeriodic.phaseQuery
  dsimp only
  split
  next period after hp ha =>
    have hz:=queryTuple_extra B C E period (zeroTuple B C E).1 after .zero N counts base q s prepared.K
    rw [zeroTuple_value] at hz
    have hzero:=zeroTuple_work B C E
    have hi:=tupleQuery_extra B C E period after .interior N counts base q s prepared.K
      (interiorTuples B C E idx start q).values
    have he:=tupleQuery_extra B C E period tail .ending N counts base q s prepared.K
      (endingTuples B C E idx start eta q).values
    have hli:=Nat.mul_le_mul_right (tupleConstructionCost B.stateCount C.stateCount E.stateCount prepared.K+4)
      (interiorTuples_size B C E idx start q)
    have hle:=Nat.mul_le_mul_right (tupleConstructionCost B.stateCount C.stateCount E.stateCount prepared.K+4)
      (endingTuples_size B C E idx start eta q)
    rw [jointEnum_length] at hli hle
    simp only [hp,ha,zeroTuple_value,Batch.queryCost,joinAnswers,queryInterior,queryEnding,phaseExtra]
    rw [Nat.mul_assoc 2]
    omega
  next hp =>
    simp only [Batch.queryCost,phaseExtra]
    omega

def query (B C E : DFA α) (prepared : PreparedPattern B.stateCount C.stateCount E.stateCount)
    (idx : Index.Tree (jointEnum B C E)) (tail : Map E.stateCount)
    (s R q : Nat) (counts : Array Nat) (base : Nat) : Result IndexedAnswer :=
  if 0<q ∧ s+q≤R then
    let out:=phaseQuery B C E prepared idx tail s ((R-s)%q) q ((R-s)/q) counts base s
    (Text.chargeEndpoints out.1,out.2+9)
  else (⟨⟨false,0,4⟩,0,0⟩,4)

theorem query_value (B C E : DFA α) (prepared : PreparedPattern B.stateCount C.stateCount E.stateCount)
    (idx : Index.Tree (jointEnum B C E)) (tail : Map E.stateCount)
    (s R q : Nat) (counts : Array Nat) (base : Nat) :
    (query B C E prepared idx tail s R q counts base).1=
      Text.query B C E prepared idx tail s R q counts base := by
  unfold query Text.query
  split <;> simp only [phaseQuery_value]

def queryExtra (b c e K : Nat) : Nat := phaseExtra b c e K+2

theorem query_extra (B C E : DFA α) (prepared : PreparedPattern B.stateCount C.stateCount E.stateCount)
    (idx : Index.Tree (jointEnum B C E)) (tail : Map E.stateCount)
    (s R q : Nat) (counts : Array Nat) (base : Nat) :
    (query B C E prepared idx tail s R q counts base).2≤
      Batch.queryCost (Text.query B C E prepared idx tail s R q counts base)+
      queryExtra B.stateCount C.stateCount E.stateCount prepared.K := by
  unfold query Text.query
  split
  · have h:=phaseQuery_extra B C E prepared idx tail s ((R-s)%q) q ((R-s)/q) counts base s
    simp only [Batch.queryCost,Text.chargeEndpoints,queryExtra] at h ⊢
    omega
  · simp only [Batch.queryCost,queryExtra]
    omega

theorem query_inflate (B C E : DFA α) (prepared : PreparedPattern B.stateCount C.stateCount E.stateCount)
    (idx : Index.Tree (jointEnum B C E)) (tail : Map E.stateCount)
    (s R q : Nat) (counts : Array Nat) (base : Nat) :
    (query B C E prepared idx tail s R q counts base).2≤
      (queryExtra B.stateCount C.stateCount E.stateCount prepared.K+1)*
      (Batch.queryCost (Text.query B C E prepared idx tail s R q counts base)+1) :=
  Nat.le_trans (query_extra B C E prepared idx tail s R q counts base) (inflate _ _)

end REWB.PeriodicConstruction.Masked
