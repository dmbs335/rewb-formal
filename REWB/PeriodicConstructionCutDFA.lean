import REWB.PeriodicConstructionCutSummary
import REWB.PeriodicConstructionMaskedOrbit
import REWB.MaskedFiniteConstruction

/-! The concrete DFA-map instance of the counted cut algebra. Transformations
are materialized vectors. Equality is charged for both full vector lengths,
as in `MaskedFiniteConstruction`, rather than treated as a unit comparison.
The joint enumeration is constructed by the counted finite list loops. -/
namespace REWB.PeriodicConstruction.Cut
open REWB.MaskedCut.DFAIndex REWB.MaskedFiniteAction
variable {α : Type}

def identity (m : Nat) : Result (Maps.Map m) := Masked.tabulate m (fun i=>(i,1))

theorem identity_value (m : Nat) : (identity m).1=Maps.identity m := by
  apply Vector.ext
  intro i hi
  change (identity m).1.get ⟨i,hi⟩=(Maps.identity m).get ⟨i,hi⟩
  simp only [identity,Masked.tabulate_get,Maps.identity,BoundaryIndex.Table.get_ofFn,id_eq]

theorem identity_work (m : Nat) : (identity m).2≤4*m+1 := by
  simpa only [identity,Nat.mul_comm] using Masked.tabulate_work (fun i=>(i,1)) 1 (fun _=>Nat.le_refl _)

def compose {m : Nat} (a b : Maps.Map m) : Result (Maps.Map m) :=
  Masked.tabulate m (fun q=>(b.get (a.get q),3))

theorem compose_value {m : Nat} (a b : Maps.Map m) : (compose a b).1=Maps.mul a b := by
  apply Vector.ext
  intro i hi
  change (compose a b).1.get ⟨i,hi⟩=(Maps.mul a b).get ⟨i,hi⟩
  simp only [compose,Masked.tabulate_get,Maps.mul_get]

theorem compose_work {m : Nat} (a b : Maps.Map m) : (compose a b).2≤6*m+1 := by
  simpa only [compose,Nat.mul_comm] using
    Masked.tabulate_work (fun q=>(b.get (a.get q),3)) 3 (fun _=>Nat.le_refl _)

def jointOne (B C E : DFA α) : Result (Joint B C E) :=
  let b:=identity B.stateCount
  let c:=identity C.stateCount
  let e:=identity E.stateCount
  ((b.1,c.1,e.1),b.2+c.2+e.2+2)

def jointMul (B C E : DFA α) (x y : Joint B C E) : Result (Joint B C E) :=
  let b:=compose x.1 y.1
  let c:=compose x.2.1 y.2.1
  let e:=compose x.2.2 y.2.2
  ((b.1,c.1,e.1),b.2+c.2+e.2+2)

def equalityCost (b c e : Nat) : Nat := 2*b+2*c+2*e+7

def jointEqual (B C E : DFA α) (x y : Joint B C E) : Result Bool :=
  (decide (x=y),equalityCost B.stateCount C.stateCount E.stateCount)

def primitives (B C E : DFA α) : Primitives (jointOps B C E) where
  unit:=jointOne B C E
  multiply:=jointMul B C E
  equal:=jointEqual B C E
  unit_value:=by simp only [jointOne,identity_value,jointOps,prodOps,mapOps]
  multiply_value:=by intro x y; simp only [jointMul,compose_value,jointOps,prodOps,mapOps]
  equal_value:=by intro x y; rfl

def primitiveCost (b c e : Nat) : Nat := 8*b+8*c+8*e+20

theorem primitives_unit (B C E : DFA α) :
    (primitives B C E).unit.2≤primitiveCost B.stateCount C.stateCount E.stateCount := by
  have hb:=identity_work B.stateCount
  have hc:=identity_work C.stateCount
  have he:=identity_work E.stateCount
  dsimp only [primitives,jointOne,primitiveCost]
  omega

theorem primitives_mul (B C E : DFA α) (x y : Joint B C E) :
    ((primitives B C E).multiply x y).2≤primitiveCost B.stateCount C.stateCount E.stateCount := by
  have hb:=compose_work x.1 y.1
  have hc:=compose_work x.2.1 y.2.1
  have he:=compose_work x.2.2 y.2.2
  dsimp only [primitives,jointMul,primitiveCost]
  omega

theorem primitives_equal (B C E : DFA α) (x y : Joint B C E) :
    ((primitives B C E).equal x y).2≤primitiveCost B.stateCount C.stateCount E.stateCount := by
  dsimp only [primitives,jointEqual,equalityCost,primitiveCost]
  omega

def enumeration (b c e : Nat) : Result (List (Maps.Map b×Maps.Map c×Maps.Map e)) :=
  let left:=MaskedFiniteConstruction.vectors b b
  let right:=MaskedFiniteConstruction.enumeration c e
  let out:=CountedProjection.flatMap
    (fun x=>CountedProjection.map (fun y=>((x,y),1)) right.1) left.1
  (out.1,left.2+right.2+out.2+2)

theorem enumeration_value (B C E : DFA α) :
    (enumeration B.stateCount C.stateCount E.stateCount).1=(jointEnum B C E).elems := by
  simp only [enumeration,CountedProjection.flatMap_value,CountedProjection.map_value,
    MaskedFiniteConstruction.vectors_value,MaskedFiniteConstruction.enumeration_value,
    jointEnum,prodEnum,mapEnum,Maps.allMaps,MaskedCluster.ReplayMaps.enumeration]

structure Environment (B C E : DFA α) where
  kernel : Primitives (jointOps B C E)
  catalog : Universe (jointEnum B C E)

def prepare (B C E : DFA α) : Result (Environment B C E) :=
  let values:=enumeration B.stateCount C.stateCount E.stateCount
  let k:=primitives B C E
  (⟨k,⟨values.1,enumeration_value B C E⟩⟩,values.2+k.unit.2+2)

def prepareCost (b c e : Nat) : Nat := (enumeration b c e).2+primitiveCost b c e+2

theorem prepare_work (B C E : DFA α) :
    (prepare B C E).2≤prepareCost B.stateCount C.stateCount E.stateCount := by
  have h:=primitives_unit B C E
  dsimp only [prepare,prepareCost]
  omega

def cardinality (b c e : Nat) : Nat := b^b*(c^c*e^e)

theorem enum_cardinality (B C E : DFA α) :
    (jointEnum B C E).elems.length=cardinality B.stateCount C.stateCount E.stateCount :=
  jointEnum_length B C E

def letter (B C E : DFA α) (x : α) : Result (Joint B C E) :=
  let b:=Masked.tabulate B.stateCount (fun q=>(B.step q x,2))
  let c:=Masked.tabulate C.stateCount (fun q=>(C.step q x,2))
  let e:=Masked.tabulate E.stateCount (fun q=>(E.step q x,2))
  ((b.1,c.1,e.1),b.2+c.2+e.2+2)

theorem letter_value (B C E : DFA α) (x : α) :
    (letter B C E x).1=jointWord B C E [x] := by
  have hx (d : DFA α) : (Masked.tabulate d.stateCount (fun q=>(d.step q x,2))).1=Maps.wordMap d [x] := by
    apply Vector.ext
    intro i hi
    change (Masked.tabulate d.stateCount (fun q=>(d.step q x,2))).1.get ⟨i,hi⟩=
      (Maps.wordMap d [x]).get ⟨i,hi⟩
    simp only [Masked.tabulate_get,Maps.wordMap_get,DFA.run]
  simp only [letter,jointWord,hx]

theorem letter_work (B C E : DFA α) (x : α) :
    (letter B C E x).2≤primitiveCost B.stateCount C.stateCount E.stateCount := by
  have hb:=Masked.tabulate_work (fun q=>(B.step q x,2)) 2 (fun _=>Nat.le_refl _)
  have hc:=Masked.tabulate_work (fun q=>(C.step q x,2)) 2 (fun _=>Nat.le_refl _)
  have he:=Masked.tabulate_work (fun q=>(E.step q x,2)) 2 (fun _=>Nat.le_refl _)
  dsimp only [letter,primitiveCost]
  omega

def letters (B C E : DFA α) (w : Word α) : Result (List (Joint B C E)) :=
  CountedProjection.map (letter B C E) w

theorem letters_value (B C E : DFA α) (w : Word α) :
    (letters B C E w).1=MaskedCut.DFAIndex.letters B C E w := by
  simp only [letters,CountedProjection.map_value,letter_value,MaskedCut.DFAIndex.letters]

theorem letters_work (B C E : DFA α) (w : Word α) :
    (letters B C E w).2≤w.length*(primitiveCost B.stateCount C.stateCount E.stateCount+1)+1 :=
  map_bound _ _ _ (fun x _=>letter_work B C E x)

end REWB.PeriodicConstruction.Cut
