import REWB.PeriodicConstructionCutTuples
import REWB.PeriodicConstructionMaskedPhase

/-! All shared-index inputs of a periodic phase are now produced through
the counted finite algebra. Value equalities preserve the original
context, constrained-cut and tuple result records, including counters. -/
namespace REWB.PeriodicConstruction.Cut
open REWB.MaskedCut REWB.MaskedCut.DFAIndex REWB.MaskedPeriodic REWB.MaskedFiniteAction.Maps
variable {α : Type}

theorem combine (A B C x y : Nat) :
    A*(x+1)+B*(y+1)+C≤(A+B+C)*(x+y+1) := by
  simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one]
  omega

theorem addCharge (A B x : Nat) : A*(x+1)+B≤(A+B)*(x+1) := by
  simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one]
  omega

def constrainedQuery (B C E : DFA α) (idx : Index.Tree (jointEnum B C E))
    (start lower eta q : Nat) : Result (ConstrainedResult B C E) :=
  if lower≤eta then
    let cuts:=queryIndex B C E idx start (start+lower) (start+eta) (start+eta)
    let tail:=queryRange B C E idx (start+eta) (start+q)
    (⟨cuts.1.answer.bind (fun c=>tail.1.answer.map (fun t=>⟨c,t.total⟩)),
      cuts.1.products+tail.1.products,cuts.1.visits+tail.1.visits⟩,cuts.2+tail.2+6)
  else (⟨none,0,0⟩,1)

theorem constrainedQuery_value (B C E : DFA α) (idx : Index.Tree (jointEnum B C E))
    (start lower eta q : Nat) :
    (constrainedQuery B C E idx start lower eta q).1=queryConstrained B C E idx start lower eta q := by
  simp only [constrainedQuery,queryConstrained,queryIndex_value,queryRange_value]
  split <;> rfl

def constrainedCoefficient (b c e : Nat) : Nat := indexCoefficient b c e+rangeCoefficient b c e+6

theorem constrainedQuery_work (B C E : DFA α) (idx : Index.Tree (jointEnum B C E))
    (start lower eta q : Nat) (ht : Tiny idx) :
    (constrainedQuery B C E idx start lower eta q).2≤
      constrainedCoefficient B.stateCount C.stateCount E.stateCount*
      ((queryConstrained B C E idx start lower eta q).products+
       (queryConstrained B C E idx start lower eta q).visits+1) := by
  by_cases h : lower≤eta
  · have hc:=queryIndex_work B C E idx start (start+lower) (start+eta) (start+eta) ht
    have hr:=queryRange_work B C E idx (start+eta) (start+q) ht
    have ha:=combine (indexCoefficient B.stateCount C.stateCount E.stateCount)
      (rangeCoefficient B.stateCount C.stateCount E.stateCount) 6
      ((Index.query (jointOps B C E) (jointEnum B C E) idx start (start+lower) (start+eta) (start+eta)).products+
       (Index.query (jointOps B C E) (jointEnum B C E) idx start (start+lower) (start+eta) (start+eta)).visits)
      ((DyadicIndex.query (ops (jointOps B C E) (jointEnum B C E)) idx (start+eta) (start+q)).products+
       (DyadicIndex.query (ops (jointOps B C E) (jointEnum B C E)) idx (start+eta) (start+q)).visits)
    simp only [constrainedQuery,queryConstrained,h,if_true,constrainedCoefficient]
    have he : ∀a b c d : Nat,a+b+(c+d)+1=a+c+(b+d)+1 := by intros; omega
    rw [he] at ha
    exact Nat.le_trans (by omega) ha
  · simp only [constrainedQuery,queryConstrained,h,if_false,constrainedCoefficient,Nat.zero_add,Nat.mul_one]
    omega

def interior (B C E : DFA α) (idx : Index.Tree (jointEnum B C E)) (start q : Nat) : Result (TupleResult B C E) :=
  if 1<q then
    let cuts:=queryIndex B C E idx start (start+1) (start+q-1) (start+q)
    let tuples:=fullTuples B C E cuts.1.answer
    (⟨tuples.1,cuts.1.products,cuts.1.visits⟩,cuts.2+tuples.2+5)
  else (⟨[],0,0⟩,1)

theorem interior_value (B C E : DFA α) (idx : Index.Tree (jointEnum B C E)) (start q : Nat) :
    (interior B C E idx start q).1=interiorTuples B C E idx start q := by
  simp only [interior,interiorTuples,queryIndex_value,fullTuples_value]
  split <;> rfl

def interiorCoefficient (b c e : Nat) : Nat := indexCoefficient b c e+tupleCost b c e+5

theorem interior_work (B C E : DFA α) (idx : Index.Tree (jointEnum B C E)) (start q : Nat)
    (ht : Tiny idx) : (interior B C E idx start q).2≤
      interiorCoefficient B.stateCount C.stateCount E.stateCount*
      ((interiorTuples B C E idx start q).products+(interiorTuples B C E idx start q).visits+1) := by
  by_cases h : 1<q
  · have hi:=queryIndex_work B C E idx start (start+1) (start+q-1) (start+q) ht
    have he:=fullTuples_work B C E (queryIndex B C E idx start (start+1) (start+q-1) (start+q)).1.answer
    have ha:=addCharge (indexCoefficient B.stateCount C.stateCount E.stateCount)
      (tupleCost B.stateCount C.stateCount E.stateCount+5)
      ((Index.query (jointOps B C E) (jointEnum B C E) idx start (start+1) (start+q-1) (start+q)).products+
       (Index.query (jointOps B C E) (jointEnum B C E) idx start (start+1) (start+q-1) (start+q)).visits)
    simp only [interior,interiorTuples,h,if_true,interiorCoefficient,Nat.add_assoc] at ha ⊢
    simp only [Nat.add_assoc] at hi
    exact Nat.le_trans (by omega) ha
  · simp only [interior,interiorTuples,h,if_false,interiorCoefficient,Nat.zero_add,Nat.mul_one]
    omega

def ending (B C E : DFA α) (idx : Index.Tree (jointEnum B C E)) (start eta q : Nat) : Result (TupleResult B C E) :=
  let cuts:=constrainedQuery B C E idx start 1 eta q
  match cuts.1.answer with
  | none=>(⟨[],cuts.1.products,cuts.1.visits⟩,cuts.2+2)
  | some out=>
    let tuples:=constrainedTuples B C E out
    (⟨tuples.1,cuts.1.products,cuts.1.visits⟩,cuts.2+tuples.2+3)

theorem ending_value (B C E : DFA α) (idx : Index.Tree (jointEnum B C E)) (start eta q : Nat) :
    (ending B C E idx start eta q).1=endingTuples B C E idx start eta q := by
  simp only [ending,constrainedQuery_value,endingTuples]
  cases h : (queryConstrained B C E idx start 1 eta q).answer <;>
    simp only [h,constrainedTuples_value,Option.map,Option.getD_none,Option.getD_some]

def endingCoefficient (b c e : Nat) : Nat := constrainedCoefficient b c e+tupleCost b c e+3

theorem ending_work (B C E : DFA α) (idx : Index.Tree (jointEnum B C E)) (start eta q : Nat)
    (ht : Tiny idx) : (ending B C E idx start eta q).2≤
      endingCoefficient B.stateCount C.stateCount E.stateCount*
      ((endingTuples B C E idx start eta q).products+(endingTuples B C E idx start eta q).visits+1) := by
  have hc:=constrainedQuery_work B C E idx start 1 eta q ht
  have ha:=addCharge (constrainedCoefficient B.stateCount C.stateCount E.stateCount)
    (tupleCost B.stateCount C.stateCount E.stateCount+3)
    ((queryConstrained B C E idx start 1 eta q).products+(queryConstrained B C E idx start 1 eta q).visits)
  simp only [ending,endingTuples,endingCoefficient,Nat.add_assoc] at ha ⊢
  simp only [Nat.add_assoc] at hc
  split
  · exact Nat.le_trans (by omega) ha
  · rename_i out hout
    have he:=constrainedTuples_work B C E out
    exact Nat.le_trans (by omega) ha

def contexts (B C E : DFA α) (idx : Index.Tree (jointEnum B C E))
    (start eta q : Nat) (tail : Map E.stateCount) : Result (ContextResult B C E) :=
  let whole:=queryRange B C E idx start (start+q)
  let fragment:=queryRange B C E idx start (start+eta)
  let after:=match fragment.1.answer with
    | none=>(none,1)
    | some part=>let out:=compose part.total.2.2 tail; (some out.1,out.2+1)
  (⟨whole.1.answer.map Summary.total,after.1,
    whole.1.products+fragment.1.products,whole.1.visits+fragment.1.visits⟩,
    whole.2+fragment.2+after.2+6)

theorem contexts_value (B C E : DFA α) (idx : Index.Tree (jointEnum B C E))
    (start eta q : Nat) (tail : Map E.stateCount) :
    (contexts B C E idx start eta q tail).1=MaskedPeriodic.contexts B C E idx start eta q tail := by
  simp only [contexts,queryRange_value,MaskedPeriodic.contexts]
  cases h : (DyadicIndex.query (ops (jointOps B C E) (jointEnum B C E)) idx start (start+eta)).answer <;>
    simp only [h,compose_value,Option.map]

def contextCoefficient (b c e : Nat) : Nat := 2*rangeCoefficient b c e+6*e+8

theorem contexts_work (B C E : DFA α) (idx : Index.Tree (jointEnum B C E))
    (start eta q : Nat) (tail : Map E.stateCount) (ht : Tiny idx) :
    (contexts B C E idx start eta q tail).2≤contextCoefficient B.stateCount C.stateCount E.stateCount*
      ((MaskedPeriodic.contexts B C E idx start eta q tail).products+
       (MaskedPeriodic.contexts B C E idx start eta q tail).visits+1) := by
  have hw:=queryRange_work B C E idx start (start+q) ht
  have hf:=queryRange_work B C E idx start (start+eta) ht
  have ha:=combine (rangeCoefficient B.stateCount C.stateCount E.stateCount)
    (rangeCoefficient B.stateCount C.stateCount E.stateCount) (6*E.stateCount+8)
    ((DyadicIndex.query (ops (jointOps B C E) (jointEnum B C E)) idx start (start+q)).products+
     (DyadicIndex.query (ops (jointOps B C E) (jointEnum B C E)) idx start (start+q)).visits)
    ((DyadicIndex.query (ops (jointOps B C E) (jointEnum B C E)) idx start (start+eta)).products+
     (DyadicIndex.query (ops (jointOps B C E) (jointEnum B C E)) idx start (start+eta)).visits)
  have he : ∀a b c d : Nat,a+b+(c+d)+1=a+c+(b+d)+1 := by intros; omega
  rw [he] at ha
  have hh : ∀x : Nat,x+x+(6*E.stateCount+8)=2*x+6*E.stateCount+8 := by intro x; omega
  rw [hh] at ha
  simp only [contexts,MaskedPeriodic.contexts,contextCoefficient]
  split
  · dsimp only
    exact Nat.le_trans (by omega) ha
  · rename_i part hpart
    have hp:=compose_work part.total.2.2 tail
    dsimp only
    exact Nat.le_trans (by omega) ha

def prepareTail (B C E : DFA α) (idx : Index.Tree (jointEnum B C E)) (R n : Nat) : Result (Text.TailContext E.stateCount) :=
  let out:=queryRange B C E idx R n
  let id:=identity E.stateCount
  (⟨(out.1.answer.map (fun s=>s.total.2.2)).getD id.1,out.1.products,out.1.visits⟩,out.2+id.2+4)

theorem prepareTail_value (B C E : DFA α) (idx : Index.Tree (jointEnum B C E)) (R n : Nat) :
    (prepareTail B C E idx R n).1=Text.prepareTail B C E idx R n := by
  simp only [prepareTail,queryRange_value,identity_value,Text.prepareTail]

def tailCoefficient (b c e : Nat) : Nat := rangeCoefficient b c e+4*e+5

theorem prepareTail_work (B C E : DFA α) (idx : Index.Tree (jointEnum B C E)) (R n : Nat)
    (ht : Tiny idx) : (prepareTail B C E idx R n).2≤tailCoefficient B.stateCount C.stateCount E.stateCount*
      ((Text.prepareTail B C E idx R n).products+(Text.prepareTail B C E idx R n).visits+1) := by
  have hq:=queryRange_work B C E idx R n ht
  have hi:=identity_work E.stateCount
  have ha:=addCharge (rangeCoefficient B.stateCount C.stateCount E.stateCount) (4*E.stateCount+5)
    ((Text.prepareTail B C E idx R n).products+(Text.prepareTail B C E idx R n).visits)
  simp only [prepareTail,Text.prepareTail,tailCoefficient,Nat.add_assoc] at ha ⊢
  simp only [Nat.add_assoc] at hq
  exact Nat.le_trans (by omega) ha

end REWB.PeriodicConstruction.Cut
