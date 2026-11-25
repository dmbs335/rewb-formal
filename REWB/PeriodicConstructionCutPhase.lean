import REWB.PeriodicConstructionCutInputs

/-! The full local periodic query: finite summary algebra, tuple extraction,
orbit construction, projection, interval compilation and target AP reads
all lie on the returned measured path. Prebuilt text and target indexes
remain inputs; their own concrete builders are measured separately. -/
namespace REWB.PeriodicConstruction.Cut
open REWB.MaskedPeriodic REWB.MaskedCut REWB.MaskedCut.DFAIndex REWB.MaskedFiniteAction.Maps
variable {α : Type}

def phaseQuery (B C E : DFA α) (prepared : PreparedPattern B.stateCount C.stateCount E.stateCount)
    (idx : Index.Tree (jointEnum B C E)) (tail : Map E.stateCount)
    (start eta q N : Nat) (counts : Array Nat) (base s : Nat) : Result IndexedAnswer :=
  let maps:=contexts B C E idx start eta q tail
  match maps.1.period,maps.1.after with
  | some period,some after=>
    let empty:=Masked.zeroTuple B C E
    let zero:=Masked.queryTuple B C E period empty.1 after .zero N counts base q s prepared.K
    let ci:=interior B C E idx start q
    let ce:=ending B C E idx start eta q
    let middle:=Masked.tupleQuery B C E period after .interior N counts base q s prepared.K ci.1.values
    let last:=Masked.tupleQuery B C E period tail .ending N counts base q s prepared.K ce.1.values
    (⟨joinAnswers zero.1 (joinAnswers middle.1 last.1),
      maps.1.products+ci.1.products+ce.1.products,maps.1.visits+ci.1.visits+ce.1.visits⟩,
      maps.2+empty.2+zero.2+ci.2+ce.2+middle.2+last.2+20)
  | _,_=>(⟨⟨false,0,1⟩,maps.1.products,maps.1.visits⟩,maps.2+3)

theorem phaseQuery_refine (B C E : DFA α) (prepared : PreparedPattern B.stateCount C.stateCount E.stateCount)
    (idx : Index.Tree (jointEnum B C E)) (tail : Map E.stateCount)
    (start eta q N : Nat) (counts : Array Nat) (base s : Nat) :
    (phaseQuery B C E prepared idx tail start eta q N counts base s).1=
      (Masked.phaseQuery B C E prepared idx tail start eta q N counts base s).1 := by
  cases hp : (MaskedPeriodic.contexts B C E idx start eta q tail).period <;>
    cases ha : (MaskedPeriodic.contexts B C E idx start eta q tail).after <;>
    simp only [phaseQuery,contexts_value,interior_value,ending_value,Masked.phaseQuery,hp,ha]

theorem phaseQuery_value (B C E : DFA α) (prepared : PreparedPattern B.stateCount C.stateCount E.stateCount)
    (idx : Index.Tree (jointEnum B C E)) (tail : Map E.stateCount)
    (start eta q N : Nat) (counts : Array Nat) (base s : Nat) :
    (phaseQuery B C E prepared idx tail start eta q N counts base s).1=
      MaskedPeriodic.phaseQuery B C E prepared idx tail start eta q N counts base s := by
  rw [phaseQuery_refine,Masked.phaseQuery_value]

theorem combineThree (A B C x y z : Nat) :
    A*(x+1)+B*(y+1)+C*(z+1)≤(A+B+C)*(x+y+z+1) := by
  simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one]
  omega

def setupCoefficient (b c e : Nat) : Nat :=
  contextCoefficient b c e+interiorCoefficient b c e+endingCoefficient b c e

theorem phaseQuery_overhead (B C E : DFA α) (prepared : PreparedPattern B.stateCount C.stateCount E.stateCount)
    (idx : Index.Tree (jointEnum B C E)) (tail : Map E.stateCount)
    (start eta q N : Nat) (counts : Array Nat) (base s : Nat) (ht : Tiny idx) :
    (phaseQuery B C E prepared idx tail start eta q N counts base s).2≤
      (Masked.phaseQuery B C E prepared idx tail start eta q N counts base s).2+
      setupCoefficient B.stateCount C.stateCount E.stateCount*
        ((MaskedPeriodic.phaseQuery B C E prepared idx tail start eta q N counts base s).products+
         (MaskedPeriodic.phaseQuery B C E prepared idx tail start eta q N counts base s).visits+1) := by
  have hm:=contexts_work B C E idx start eta q tail ht
  have hi:=interior_work B C E idx start q ht
  have he:=ending_work B C E idx start eta q ht
  have hall:=combineThree (contextCoefficient B.stateCount C.stateCount E.stateCount)
    (interiorCoefficient B.stateCount C.stateCount E.stateCount)
    (endingCoefficient B.stateCount C.stateCount E.stateCount)
    ((MaskedPeriodic.contexts B C E idx start eta q tail).products+
      (MaskedPeriodic.contexts B C E idx start eta q tail).visits)
    ((interiorTuples B C E idx start q).products+(interiorTuples B C E idx start q).visits)
    ((endingTuples B C E idx start eta q).products+(endingTuples B C E idx start eta q).visits)
  have hsum : ∀a b c d e f : Nat,a+b+(c+d)+(e+f)+1=a+c+e+(b+d+f)+1 := by intros; omega
  rw [hsum] at hall
  have hcoeff : contextCoefficient B.stateCount C.stateCount E.stateCount≤
      setupCoefficient B.stateCount C.stateCount E.stateCount := by unfold setupCoefficient; omega
  have hbig:=Nat.mul_le_mul_right
    ((MaskedPeriodic.contexts B C E idx start eta q tail).products+
     (MaskedPeriodic.contexts B C E idx start eta q tail).visits+1) hcoeff
  simp only [setupCoefficient] at hbig
  cases hp : (MaskedPeriodic.contexts B C E idx start eta q tail).period <;>
    cases ha : (MaskedPeriodic.contexts B C E idx start eta q tail).after <;>
    simp only [phaseQuery,Masked.phaseQuery,MaskedPeriodic.phaseQuery,contexts_value,interior_value,
      ending_value,hp,ha,setupCoefficient,queryInterior,queryEnding] <;> omega

def phaseCoefficient (b c e K : Nat) : Nat := setupCoefficient b c e+Masked.phaseExtra b c e K+1

theorem phaseQuery_work (B C E : DFA α) (prepared : PreparedPattern B.stateCount C.stateCount E.stateCount)
    (idx : Index.Tree (jointEnum B C E)) (tail : Map E.stateCount)
    (start eta q N : Nat) (counts : Array Nat) (base s : Nat) (ht : Tiny idx) :
    (phaseQuery B C E prepared idx tail start eta q N counts base s).2≤
      phaseCoefficient B.stateCount C.stateCount E.stateCount prepared.K*
      (Batch.queryCost (MaskedPeriodic.phaseQuery B C E prepared idx tail start eta q N counts base s)+1) := by
  have ho:=phaseQuery_overhead B C E prepared idx tail start eta q N counts base s ht
  have hf:=Masked.phaseQuery_extra B C E prepared idx tail start eta q N counts base s
  have hm:=Nat.mul_le_mul_left (setupCoefficient B.stateCount C.stateCount E.stateCount)
    (show (MaskedPeriodic.phaseQuery B C E prepared idx tail start eta q N counts base s).products+
      (MaskedPeriodic.phaseQuery B C E prepared idx tail start eta q N counts base s).visits+1≤
      Batch.queryCost (MaskedPeriodic.phaseQuery B C E prepared idx tail start eta q N counts base s)+1 by
      unfold Batch.queryCost; omega)
  have ha:=Masked.inflate
    (Batch.queryCost (MaskedPeriodic.phaseQuery B C E prepared idx tail start eta q N counts base s))
    (Masked.phaseExtra B.stateCount C.stateCount E.stateCount prepared.K)
  have hs:=Nat.add_le_add hm ha
  have he : phaseCoefficient B.stateCount C.stateCount E.stateCount prepared.K=
      setupCoefficient B.stateCount C.stateCount E.stateCount+
      (Masked.phaseExtra B.stateCount C.stateCount E.stateCount prepared.K+1) := by
    unfold phaseCoefficient; omega
  rw [he,Nat.add_mul]
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
    (query B C E prepared idx tail s R q counts base).1=Text.query B C E prepared idx tail s R q counts base := by
  simp only [query,Text.query,phaseQuery_value]
  split <;> rfl

def queryCoefficient (b c e K : Nat) : Nat := phaseCoefficient b c e K+9

theorem query_work (B C E : DFA α) (prepared : PreparedPattern B.stateCount C.stateCount E.stateCount)
    (idx : Index.Tree (jointEnum B C E)) (tail : Map E.stateCount)
    (s R q : Nat) (counts : Array Nat) (base : Nat) (ht : Tiny idx) :
    (query B C E prepared idx tail s R q counts base).2≤
      queryCoefficient B.stateCount C.stateCount E.stateCount prepared.K*
      (Batch.queryCost (Text.query B C E prepared idx tail s R q counts base)+1) := by
  unfold query Text.query
  split
  · have hp:=phaseQuery_work B C E prepared idx tail s ((R-s)%q) q ((R-s)/q) counts base s ht
    have hmono:=Nat.mul_le_mul_left (phaseCoefficient B.stateCount C.stateCount E.stateCount prepared.K)
      (show Batch.queryCost (MaskedPeriodic.phaseQuery B C E prepared idx tail s ((R-s)%q) q ((R-s)/q) counts base s)+1≤
        Batch.queryCost (Text.chargeEndpoints (MaskedPeriodic.phaseQuery B C E prepared idx tail s ((R-s)%q) q ((R-s)/q) counts base s))+1 by
        simp only [Batch.queryCost,Text.chargeEndpoints]; omega)
    have ha:=addCharge (phaseCoefficient B.stateCount C.stateCount E.stateCount prepared.K) 9
      (Batch.queryCost (Text.chargeEndpoints (MaskedPeriodic.phaseQuery B C E prepared idx tail s ((R-s)%q) q ((R-s)/q) counts base s)))
    exact Nat.le_trans (by dsimp only; omega) ha
  · simp only [Batch.queryCost,queryCoefficient]
    omega

end REWB.PeriodicConstruction.Cut
