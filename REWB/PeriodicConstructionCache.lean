import REWB.PeriodicConstructionWindows
import REWB.PeriodicCache

/-! Materialized periodic DFA caches with structural-operation accounting.
The old transition-only counter is retained inside the returned value.
The additional counter includes symbol reads, list cells, scalar arithmetic,
finite state iteration, and list-to-array materialization. A symbol read
and DFA transition are scalar primitives; allocation/GC and bit costs are
outside this model. Public callers use a shifted materialized-text reader. -/
namespace REWB.PeriodicConstruction.Cache

variable {α X Y : Type}

/-- Materialization charges one input visit and one output write per cell.
The produced array supplies its cached size, so accounting adds no list scan. -/
def array (xs : List X) : Result (Array X) :=
  let out:=xs.toArray
  (out,2*out.size+1)

theorem array_value (xs : List X) : (array xs).1=xs.toArray := rfl

theorem array_work (xs : List X) : (array xs).2=2*xs.length+1 := by
  simp [array]

def word (s : Nat→α) (a : Nat) : Nat→Result (Word α)
  | 0=>([],1)
  | q+1=>
    let tail:=word s (a+1) q
    (s a::tail.1,tail.2+4)

theorem word_value (s : Nat→α) (a q : Nat) :
    (word s a q).1=Periodic.segment s a q := by
  induction q generalizing a with
  | zero=>rfl
  | succ q ih=>simp only [word,Periodic.segment,ih]

theorem word_work (s : Nat→α) (a q : Nat) :
    (word s a q).2=4*q+1 := by
  induction q generalizing a with
  | zero=>rfl
  | succ q ih=>simp only [word,ih,Nat.mul_add,Nat.mul_one]; omega

/-- The inner counter is exactly the original number of DFA transitions. -/
def prefix (d : DFA α) : Fin d.stateCount→Word α→Result (List (Fin d.stateCount)×Nat)
  | v,[]=>(([v],0),2)
  | v,c::cs=>
    let tail:=prefix d (d.step v c) cs
    ((v::tail.1.1,tail.1.2+1),tail.2+8)

theorem prefix_value (d : DFA α) (v : Fin d.stateCount) (w : Word α) :
    (prefix d v w).1=IntervalDFA.countedPrefix d v w := by
  induction w generalizing v with
  | nil=>rfl
  | cons c cs ih=>simp only [prefix,IntervalDFA.countedPrefix,ih]

theorem prefix_length (d : DFA α) (v : Fin d.stateCount) (w : Word α) :
    (prefix d v w).1.1.length=w.length+1 := by
  induction w generalizing v with
  | nil=>rfl
  | cons c cs ih=>simp only [prefix,List.length_cons,ih]

def prefixCost (n : Nat) : Nat := 8*n+2

theorem prefix_work (d : DFA α) (v : Fin d.stateCount) (w : Word α) :
    (prefix d v w).2=prefixCost w.length := by
  induction w generalizing v with
  | nil=>rfl
  | cons c cs ih=>
    simp only [prefix,ih,prefixCost,List.length_cons,Nat.mul_add,Nat.mul_one] <;> omega

/-- A single pass preserves the legacy sum while accumulating real
construction work from each executed callback. -/
def collect (f : X→Result (Y×Nat)) : List X→Result (List Y×Nat)
  | []=>(([],0),1)
  | x::xs=>
    let a:=f x
    let b:=collect f xs
    ((a.1.1::b.1.1,a.1.2+b.1.2),a.2+b.2+3)

theorem collect_value (f : X→Result (Y×Nat)) (xs : List X) :
    (collect f xs).1=PeriodicCache.countedMap (fun x=>(f x).1) xs := by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>simp only [collect,PeriodicCache.countedMap,ih]

theorem collect_length (f : X→Result (Y×Nat)) (xs : List X) :
    (collect f xs).1.1.length=xs.length := by
  rw [collect_value,PeriodicCache.countedMap_values,List.length_map]

theorem collect_work (f : X→Result (Y×Nat)) (xs : List X) (C : Nat)
    (h : ∀x,(f x).2=C) : (collect f xs).2=xs.length*(C+3)+1 := by
  induction xs with
  | nil=>simp [collect]
  | cons x xs ih=>
    simp only [collect,h,ih,List.length_cons,Nat.add_mul,Nat.one_mul] <;> omega

theorem range_work (n : Nat) : (CountedProjection.range n).2=2*n+1 :=
  CountedProjection.rangeFrom_steps 0 n

def stateRow (d : DFA α) (w : Word α) (i : Nat) :
    Result (PeriodicCache.StateRow d×Nat) :=
  let states:=prefix d (PeriodicCache.state d i) w
  let out:=array states.1.1
  ((out.1,states.1.2),states.2+out.2+4)

theorem stateRow_value (d : DFA α) (w : Word α) (i : Nat) :
    (stateRow d w i).1=
      let states:=IntervalDFA.countedPrefix d (PeriodicCache.state d i) w
      (states.1.toArray,states.2) := by
  simp only [stateRow,array_value,prefix_value]

def rowCost (n : Nat) : Nat := prefixCost n+(2*(n+1)+1)+4

theorem stateRow_work (d : DFA α) (w : Word α) (i : Nat) :
    (stateRow d w i).2=rowCost w.length := by
  simp only [stateRow,prefix_work,array_work,prefix_length,rowCost]

def phase (d : DFA α) (s : Nat→α) (q a : Nat) :
    Result (PeriodicCache.PhaseRow d×Nat) :=
  let w:=word s a q
  let domain:=CountedProjection.range d.stateCount
  let rows:=collect (stateRow d w.1) domain.1
  let out:=array rows.1.1
  ((out.1,rows.1.2),w.2+domain.2+rows.2+out.2+4)

theorem phase_value (d : DFA α) (s : Nat→α) (q a : Nat) :
    (phase d s q a).1=PeriodicCache.buildPhase d s q a := by
  simp only [phase,array_value,collect_value,word_value,CountedProjection.range_value,
    stateRow_value,PeriodicCache.buildPhase]

def phaseCost (m q : Nat) : Nat :=
  (4*q+1)+(2*m+1)+(m*(rowCost q+3)+1)+(2*m+1)+4

theorem phase_work (d : DFA α) (s : Nat→α) (q a : Nat) :
    (phase d s q a).2=phaseCost d.stateCount q := by
  have hc:=collect_work (stateRow d (Periodic.segment s a q))
    (List.range d.stateCount) (rowCost q) (by
      intro i
      rw [stateRow_work,Periodic.segment_length])
  rw [List.length_range] at hc
  simp only [phase,word_value,word_work,CountedProjection.range_value,range_work,
    array_work,collect_length,List.length_range,phaseCost]
  rw [hc]

def transitions (d : DFA α) (s : Nat→α) (q : Nat) :
    Result (PeriodicCache.Table d×Nat) :=
  let domain:=CountedProjection.range q
  let rows:=collect (phase d s q) domain.1
  let out:=array rows.1.1
  ((out.1,rows.1.2),domain.2+rows.2+out.2+3)

theorem transitions_value (d : DFA α) (s : Nat→α) (q : Nat) :
    (transitions d s q).1=PeriodicCache.build d s q := by
  simp only [transitions,array_value,collect_value,CountedProjection.range_value,
    phase_value,PeriodicCache.build]

def transitionsCost (m q : Nat) : Nat :=
  (2*q+1)+(q*(phaseCost m q+3)+1)+(2*q+1)+3

theorem transitions_work (d : DFA α) (s : Nat→α) (q : Nat) :
    (transitions d s q).2=transitionsCost d.stateCount q := by
  have hc:=collect_work (phase d s q) (List.range q)
    (phaseCost d.stateCount q) (phase_work d s q)
  rw [List.length_range] at hc
  simp only [transitions,CountedProjection.range_value,range_work,array_work,
    collect_length,List.length_range,transitionsCost]
  rw [hc]

end REWB.PeriodicConstruction.Cache
