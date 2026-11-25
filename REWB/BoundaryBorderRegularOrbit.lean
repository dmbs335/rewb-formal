import REWB.MaskedClusterOrbit

/-! Measured finite-orbit compilation for boundary regular constraints.
Transitions and accepting bits are materialized vectors. Every cycle
comparison, transition probe, acceptance probe and list construction is
counted. All loops depend on the finite state count, never on a text
period or the candidate repetition count. -/
namespace REWB.BoundaryBorder.Regular
open REWB.MaskedPeriodic REWB.MaskedFiniteAction.Maps
variable {m : Nat}

structure Orbit (m : Nat) where
  step : Map m
  initial : Fin m
  final : Vector Bool m

def Orbit.data (o : Orbit m) : OrbitData m := ⟨o.step,o.initial,o.final.get⟩

namespace Counted
open REWB.FiniteOrbit REWB.FiniteRelation

def iterate (o : Orbit m) : Nat→Fin m×Nat
  | 0 => (o.initial,1)
  | k+1 => let r:=iterate o k; (o.step.get r.1,r.2+2)

theorem iterate_value (o : Orbit m) (k : Nat) :
    (iterate o k).1=orbit o.step.get o.initial k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [iterate,ih,orbit]

theorem iterate_work (o : Orbit m) (k : Nat) : (iterate o k).2=2*k+1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [iterate,ih]; omega

def test (o : Orbit m) (k : Nat) : Bool×Nat :=
  let r:=iterate o k
  (o.final.get r.1,r.2+2)

theorem test_value (o : Orbit m) (k : Nat) : (test o k).1=o.data.test k := by
  simp only [test,iterate_value,Orbit.data,OrbitData.test]

theorem test_work (o : Orbit m) (k : Nat) : (test o k).2=2*k+3 := by
  simp only [test,iterate_work]

def valid (o : Orbit m) (p : Nat×Nat) : Bool×Nat :=
  let a:=iterate o p.1
  let b:=iterate o p.2
  (decide (p.1<p.2) && decide (a.1=b.1),a.2+b.2+3)

theorem valid_value (o : Orbit m) (p : Nat×Nat) :
    (valid o p).1=FiniteOrbit.valid o.step.get o.initial p := by
  simp only [valid,iterate_value,FiniteOrbit.valid]

theorem valid_work (o : Orbit m) (p : Nat×Nat) :
    (valid o p).2=2*p.1+2*p.2+5 := by simp only [valid,iterate_work]; omega

def first (test : X→Bool×Nat) : List X→Option X×Nat
  | [] => (none,1)
  | x::xs =>
    let a:=test x
    if a.1 then (some x,a.2+1)
    else let b:=first test xs; (b.1,a.2+b.2+1)

theorem first_value (test : X→Bool×Nat) (xs : List X) :
    (first test xs).1=FiniteOrbit.first (fun x=>(test x).1) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [first,FiniteOrbit.first]; split <;> simp only [ih]

theorem first_work (test : X→Bool×Nat) (xs : List X) (C : Nat)
    (hc : ∀x,x∈xs→(test x).2≤C) : (first test xs).2≤xs.length*(C+1)+1 := by
  induction xs with
  | nil => simp [first]
  | cons x xs ih =>
    have hx:=hc x List.mem_cons_self
    have ht:=ih (fun y hy=>hc y (List.mem_cons_of_mem _ hy))
    simp only [first,List.length_cons,Nat.add_mul,Nat.one_mul]
    split <;> dsimp only <;> omega

def filter (test : X→Bool×Nat) : List X→List X×Nat
  | [] => ([],1)
  | x::xs =>
    let a:=test x
    let b:=filter test xs
    (if a.1 then x::b.1 else b.1,a.2+b.2+2)

theorem filter_value (test : X→Bool×Nat) (xs : List X) :
    (filter test xs).1=xs.filter (fun x=>(test x).1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [filter,ih,List.filter_cons]

theorem filter_work (test : X→Bool×Nat) (xs : List X) (C : Nat)
    (hc : ∀x,x∈xs→(test x).2≤C) : (filter test xs).2≤xs.length*(C+2)+1 := by
  induction xs with
  | nil => simp [filter]
  | cons x xs ih =>
    have hx:=hc x List.mem_cons_self
    have ht:=ih (fun y hy=>hc y (List.mem_cons_of_mem _ hy))
    simp only [filter,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

def pairs (m : Nat) : List (Nat×Nat)×Nat :=
  let rs:=CountedProjection.range (m+1)
  let out:=CountedProjection.flatMap
    (fun i=>CountedProjection.map (fun j=>((i,j),1)) rs.1) rs.1
  (out.1,rs.2+out.2+1)

theorem pairs_value (m : Nat) : (pairs m).1=FiniteOrbit.pairs m := by
  simp only [pairs,CountedProjection.range_value,CountedProjection.flatMap_value,
    CountedProjection.map_value,FiniteOrbit.pairs]

theorem pairs_length (m : Nat) : (pairs m).1.length=(m+1)*(m+1) := by
  rw [pairs_value,FiniteOrbit.pairs]
  have hh (xs : List Nat) :
      (xs.flatMap (fun i=>(List.range (m+1)).map (fun j=>(i,j)))).length=xs.length*(m+1) := by
    induction xs with
    | nil => simp
    | cons x xs ih => simp only [List.flatMap_cons,List.length_append,List.length_map,
        List.length_range,ih,List.length_cons,Nat.add_mul,Nat.one_mul]; omega
  rw [hh,List.length_range]

theorem pairs_work (m : Nat) :
    (pairs m).2=(m+1)*(3*(m+1)+3)+2*(m+1)+3 := by
  unfold pairs
  dsimp only
  rw [CountedProjection.flatMap_steps_constant _ _ (2*(m+1)+1) (m+1)]
  · simp only [CountedProjection.range,CountedProjection.rangeFrom_steps,
      CountedProjection.rangeFrom_value,List.length_range']
    rw [show 2*(m+1)+1+(m+1)+2=3*(m+1)+3 by omega]
    omega
  · intro i _
    simp only [CountedProjection.map_plain_steps,CountedProjection.range_value,List.length_range]
    omega
  · intro i _
    simp only [CountedProjection.map_value,CountedProjection.range_value,List.length_map,List.length_range]

def findCycle (o : Orbit m) : Option (Nat×Nat)×Nat :=
  let ps:=pairs m
  let out:=first (valid o) ps.1
  (out.1,ps.2+out.2+1)

theorem findCycle_value (o : Orbit m) :
    (findCycle o).1=FiniteOrbit.findCycle (finEnum m) o.step.get o.initial := by
  simp only [findCycle,first_value,pairs_value,valid_value,FiniteOrbit.findCycle,
    finEnum,List.length_ofFn]

def cycleBudget (m : Nat) : Nat :=
  (m+1)*(3*(m+1)+3)+2*(m+1)+3+((m+1)*(m+1))*(4*m+6)+2

theorem findCycle_work (o : Orbit m) : (findCycle o).2≤cycleBudget m := by
  have hf:=first_work (valid o) (pairs m).1 (4*m+5) (by
    intro p hp
    rw [pairs_value] at hp
    have hb:=(FiniteOrbit.pairs_mem m p.1 p.2).mp hp
    rw [valid_work]
    omega)
  rw [pairs_length] at hf
  change (first (valid o) (pairs m).1).2≤((m+1)*(m+1))*(4*m+6)+1 at hf
  simp only [findCycle,pairs_work,cycleBudget]
  omega

def describe (o : Orbit m) (i j : Nat) : Descriptor×Nat :=
  let is:=CountedProjection.range i
  let js:=CountedProjection.range (j-i)
  let a:=filter (test o) is.1
  let b:=filter (fun r=>let out:=test o (i+r); (out.1,out.2+1)) js.1
  (⟨i,j-i,a.1,b.1⟩,is.2+js.2+a.2+b.2+4)

theorem describe_value (o : Orbit m) (i j : Nat) :
    (describe o i j).1=FiniteOrbit.describe o.step.get o.initial o.final.get i j := by
  simp only [describe,filter_value,CountedProjection.range_value,test_value,
    Orbit.data,OrbitData.test,FiniteOrbit.describe]

theorem describe_work (o : Orbit m) (i j : Nat) (hij : i<j) (hj : j≤m) :
    (describe o i j).2≤m*(2*m+6)+2*m+8 := by
  have ha:=filter_work (test o) (CountedProjection.range i).1 (2*m+3) (by
    intro k hk
    rw [CountedProjection.range_value,List.mem_range] at hk
    rw [test_work]
    omega)
  have hb:=filter_work (fun r=>let out:=test o (i+r); (out.1,out.2+1))
    (CountedProjection.range (j-i)).1 (2*m+4) (by
      intro k hk
      rw [CountedProjection.range_value,List.mem_range] at hk
      simp only [test_work]
      omega)
  simp only [CountedProjection.range_value,List.length_range] at ha hb
  change (filter (test o) (List.range i)).2≤i*(2*m+5)+1 at ha
  change (filter (fun r=>((test o (i+r)).1,(test o (i+r)).2+1)) (List.range (j-i))).2≤
    (j-i)*(2*m+6)+1 at hb
  have hma:=Nat.mul_le_mul_left i (by omega : 2*m+5≤2*m+6)
  have hm:=Nat.mul_le_mul_right (2*m+6) hj
  have he : i*(2*m+6)+(j-i)*(2*m+6)=j*(2*m+6) := by
    rw [←Nat.add_mul,Nat.add_sub_of_le (Nat.le_of_lt hij)]
  simp only [describe,CountedProjection.range_value]
  rw [show (CountedProjection.range i).2=2*i+1 from CountedProjection.rangeFrom_steps 0 i,
    show (CountedProjection.range (j-i)).2=2*(j-i)+1 from CountedProjection.rangeFrom_steps 0 (j-i)]
  change 2*i+1+(2*(j-i)+1)+(filter (test o) (List.range i)).2+
    (filter (fun r=>((test o (i+r)).1,(test o (i+r)).2+1)) (List.range (j-i))).2+4≤_
  omega

def compress (o : Orbit m) : Descriptor×Nat :=
  let found:=findCycle o
  match found.1 with
  | none => (⟨0,1,[],[]⟩,found.2+1)
  | some (i,j) => let out:=describe o i j; (out.1,found.2+out.2+1)

theorem compress_value (o : Orbit m) : (compress o).1=o.data.descriptor := by
  unfold compress OrbitData.descriptor FiniteOrbit.compress
  dsimp only [Orbit.data]
  rw [findCycle_value]
  cases hf : FiniteOrbit.findCycle (finEnum m) o.step.get o.initial with
  | none => rfl
  | some p => exact describe_value o p.1 p.2

def orbitBudget (m : Nat) : Nat := cycleBudget m+m*(2*m+6)+2*m+9

theorem compress_work (o : Orbit m) : (compress o).2≤orbitBudget m := by
  obtain ⟨i,j,hf,hij,hj,_⟩:=FiniteOrbit.findCycle_spec (finEnum m) o.step.get o.initial
  simp only [finEnum,List.length_ofFn] at hj
  have he : (findCycle o).1=some (i,j) := (findCycle_value o).trans hf
  have hfind:=findCycle_work o
  have hd:=describe_work o i j hij hj
  simp only [compress,he,orbitBudget]
  omega

end Counted
end REWB.BoundaryBorder.Regular
