import REWB.PeriodicConstructionWindows
import REWB.PeriodicCache

/-! Instrumented finite-orbit descriptor construction. The search uses
the same bounded witness order as `FiniteOrbit.compress`; each tested
orbit, accepted-count filter and list allocation is executed once by
the measured implementation. The finite state count is a cached input,
not obtained by scanning a state enumeration in every phase. -/
namespace REWB.PeriodicConstruction.Orbit
open REWB.PeriodicConstruction
variable {S : Type}

def orbit (step : S→Result S) (q : S) : Nat→Result S
  | 0 => (q,1)
  | k+1 =>
    let a:=orbit step q k
    let b:=step a.1
    (b.1,a.2+b.2+1)

theorem orbit_value (step : S→Result S) (q : S) (k : Nat) :
    (orbit step q k).1=FiniteOrbit.orbit (fun v=>(step v).1) q k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [orbit,FiniteOrbit.orbit,ih]

theorem orbit_work (step : S→Result S) (q : S) (k C : Nat)
    (h : ∀v,(step v).2≤C) : (orbit step q k).2≤k*(C+1)+1 := by
  induction k with
  | zero => simp [orbit]
  | succ k ih =>
    have hs:=h (orbit step q k).1
    simp only [orbit,Nat.add_mul,Nat.one_mul]
    omega

def valid [DecidableEq S] (step : S→Result S) (q : S) (p : Nat×Nat) : Result Bool :=
  if p.1<p.2 then
    let a:=orbit step q p.1
    let b:=orbit step q p.2
    (decide (a.1=b.1),a.2+b.2+2)
  else (false,1)

theorem valid_value [DecidableEq S] (step : S→Result S) (q : S) (p : Nat×Nat) :
    (valid step q p).1=FiniteOrbit.valid (fun v=>(step v).1) q p := by
  unfold valid FiniteOrbit.valid
  split <;> simp_all only [orbit_value,decide_true,decide_false,Bool.true_and,Bool.false_and]

def validBudget (N C : Nat) : Nat := 2*(N*(C+1)+1)+2

theorem valid_work [DecidableEq S] (step : S→Result S) (q : S) (p : Nat×Nat)
    (N C : Nat) (hs : ∀v,(step v).2≤C) (ha : p.1≤N) (hb : p.2≤N) :
    (valid step q p).2≤validBudget N C := by
  have h1:=Nat.le_trans (orbit_work step q p.1 C hs)
    (Nat.add_le_add_right (Nat.mul_le_mul_right (C+1) ha) 1)
  have h2:=Nat.le_trans (orbit_work step q p.2 C hs)
    (Nat.add_le_add_right (Nat.mul_le_mul_right (C+1) hb) 1)
  unfold valid validBudget
  split <;> dsimp only <;> omega

def first (test : α→Result Bool) : List α→Result (Option α)
  | [] => (none,1)
  | x::xs =>
    let t:=test x
    if t.1 then (some x,t.2+1)
    else let r:=first test xs; (r.1,t.2+r.2+1)

theorem first_value (test : α→Result Bool) (xs : List α) :
    (first test xs).1=FiniteOrbit.first (fun x=>(test x).1) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [first,FiniteOrbit.first]
    split <;> simp only [ih]

theorem first_work (test : α→Result Bool) (xs : List α) (C : Nat)
    (h : ∀x,x∈xs→(test x).2≤C) :
    (first test xs).2≤xs.length*(C+1)+1 := by
  induction xs with
  | nil => simp [first]
  | cons x xs ih =>
    have hx:=h x List.mem_cons_self
    have ht:=ih (fun y hy=>h y (List.mem_cons_of_mem x hy))
    simp only [first,List.length_cons,Nat.add_mul,Nat.one_mul]
    split <;> dsimp only <;> omega

def pairs (N : Nat) : Result (List (Nat×Nat)) :=
  let rs:=CountedProjection.range (N+1)
  let out:=CountedProjection.flatMap
    (fun i=>CountedProjection.map (fun j=>((i,j),1)) rs.1) rs.1
  (out.1,rs.2+out.2+1)

theorem pairs_value (N : Nat) : (pairs N).1=FiniteOrbit.pairs N := by
  simp only [pairs,CountedProjection.flatMap_value,CountedProjection.map_value,
    CountedProjection.range_value,FiniteOrbit.pairs]

theorem pairs_length (N : Nat) : (pairs N).1.length=(N+1)*(N+1) := by
  rw [pairs_value]
  unfold FiniteOrbit.pairs
  rw [List.length_flatMap]
  simp only [List.length_map,List.length_range,List.map_const',List.sum_replicate_nat]

def pairsBudget (N : Nat) : Nat := 2*(N+1)+1+(N+1)*(3*(N+1)+3)+2

theorem pairs_work (N : Nat) : (pairs N).2=pairsBudget N := by
  unfold pairs
  dsimp only
  rw [CountedProjection.flatMap_steps_constant _ _ (2*(N+1)+1) (N+1)]
  · rw [CountedProjection.range_value,List.length_range]
    have hr : (CountedProjection.range (N+1)).2=2*(N+1)+1 :=
      CountedProjection.rangeFrom_steps 0 (N+1)
    rw [hr]
    unfold pairsBudget
    rw [show 2*(N+1)+1+(N+1)+2=3*(N+1)+3 by omega]
    omega
  · intro i _
    rw [CountedProjection.map_plain_steps,CountedProjection.range_value,List.length_range]
    omega
  · intro i _
    rw [CountedProjection.map_value,List.length_map,CountedProjection.range_value,List.length_range]

def findCycle [DecidableEq S] (N : Nat) (step : S→Result S) (q : S) : Result (Option (Nat×Nat)) :=
  let ps:=pairs N
  let out:=first (valid step q) ps.1
  (out.1,ps.2+out.2+1)

theorem findCycle_value [DecidableEq S] (N : Nat) (step : S→Result S) (q : S) :
    (findCycle N step q).1=FiniteOrbit.first
      (FiniteOrbit.valid (fun v=>(step v).1) q) (FiniteOrbit.pairs N) := by
  simp only [findCycle,first_value,valid_value,pairs_value]

def findBudget (N C : Nat) : Nat :=
  pairsBudget N+(N+1)*(N+1)*(validBudget N C+1)+2

theorem findCycle_work [DecidableEq S] (N C : Nat) (step : S→Result S) (q : S)
    (hs : ∀v,(step v).2≤C) : (findCycle N step q).2≤findBudget N C := by
  have h:=first_work (valid step q) (pairs N).1 (validBudget N C) (by
    intro p hp
    rw [pairs_value] at hp
    have hb:=FiniteOrbit.pairs_mem N p.1 p.2 |>.mp hp
    exact valid_work step q p N C hs hb.1 hb.2)
  rw [pairs_length] at h
  unfold findCycle findBudget
  dsimp only
  rw [pairs_work]
  omega

theorem findCycle_bounds [DecidableEq S] (N : Nat) (step : S→Result S) (q : S)
    (p : Nat×Nat) (hp : (findCycle N step q).1=some p) : p.1≤N ∧ p.2≤N := by
  rw [findCycle_value] at hp
  have hm:=(FiniteOrbit.first_sound _ _ p hp).1
  exact (FiniteOrbit.pairs_mem N p.1 p.2).mp hm

def filter (test : α→Result Bool) : List α→Result (List α)
  | [] => ([],1)
  | x::xs =>
    let a:=test x
    let b:=filter test xs
    (if a.1 then x::b.1 else b.1,a.2+b.2+2)

theorem filter_value (test : α→Result Bool) (xs : List α) :
    (filter test xs).1=xs.filter (fun x=>(test x).1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [filter,List.filter_cons,ih]

theorem filter_work (test : α→Result Bool) (xs : List α) (C : Nat)
    (h : ∀x,x∈xs→(test x).2≤C) :
    (filter test xs).2≤xs.length*(C+2)+1 := by
  induction xs with
  | nil => simp [filter]
  | cons x xs ih =>
    have hx:=h x List.mem_cons_self
    have ht:=ih (fun y hy=>h y (List.mem_cons_of_mem x hy))
    simp only [filter,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

def accepted (step : S→Result S) (q : S) (accept : S→Result Bool) (k : Nat) : Result Bool :=
  let a:=orbit step q k
  let b:=accept a.1
  (b.1,a.2+b.2+1)

theorem accepted_value (step : S→Result S) (q : S) (accept : S→Result Bool) (k : Nat) :
    (accepted step q accept k).1=(accept (FiniteOrbit.orbit (fun v=>(step v).1) q k)).1 := by
  simp only [accepted,orbit_value]

theorem accepted_work (step : S→Result S) (q : S) (accept : S→Result Bool)
    (k N C : Nat) (hk : k≤N) (hs : ∀v,(step v).2≤C) (ha : ∀v,(accept v).2≤C) :
    (accepted step q accept k).2≤N*(C+1)+C+2 := by
  have ho:=Nat.le_trans (orbit_work step q k C hs)
    (Nat.add_le_add_right (Nat.mul_le_mul_right (C+1) hk) 1)
  have hf:=ha (orbit step q k).1
  unfold accepted
  dsimp only
  omega

def describe (step : S→Result S) (q : S) (accept : S→Result Bool) (i j : Nat) :
    Result FiniteOrbit.Descriptor :=
  let a:=CountedProjection.range i
  let b:=CountedProjection.range (j-i)
  let x:=filter (accepted step q accept) a.1
  let y:=filter (fun r=>accepted step q accept (i+r)) b.1
  (⟨i,j-i,x.1,y.1⟩,a.2+b.2+x.2+y.2+3)

theorem describe_value (step : S→Result S) (q : S) (accept : S→Result Bool) (i j : Nat) :
    (describe step q accept i j).1=
      FiniteOrbit.describe (fun v=>(step v).1) q (fun v=>(accept v).1) i j := by
  simp only [describe,filter_value,CountedProjection.range_value,accepted_value,FiniteOrbit.describe]

def describeBudget (N C : Nat) : Nat := 4*N+2*(N*(N*(C+1)+C+4))+7

theorem describe_work (step : S→Result S) (q : S) (accept : S→Result Bool)
    (i j N C : Nat) (hi : i≤N) (hj : j≤N)
    (hs : ∀v,(step v).2≤C) (ha : ∀v,(accept v).2≤C) :
    (describe step q accept i j).2≤describeBudget N C := by
  have h1:=filter_work (accepted step q accept) (CountedProjection.range i).1
    (N*(C+1)+C+2) (by
      intro k hk
      rw [CountedProjection.range_value,List.mem_range] at hk
      exact accepted_work step q accept k N C (by omega) hs ha)
  have h2:=filter_work (fun r=>accepted step q accept (i+r))
    (CountedProjection.range (j-i)).1 (N*(C+1)+C+2) (by
      intro r hr
      rw [CountedProjection.range_value,List.mem_range] at hr
      exact accepted_work step q accept (i+r) N C (by omega) hs ha)
  simp only [CountedProjection.range_value,List.length_range] at h1 h2
  have ha':=Nat.mul_le_mul_right (N*(C+1)+C+2+2) hi
  have hb':=Nat.mul_le_mul_right (N*(C+1)+C+2+2) (show j-i≤N by omega)
  have hr1 : (CountedProjection.range i).2=2*i+1 := CountedProjection.rangeFrom_steps 0 i
  have hr2 : (CountedProjection.range (j-i)).2=2*(j-i)+1 := CountedProjection.rangeFrom_steps 0 (j-i)
  unfold describe describeBudget
  dsimp only
  rw [hr1,hr2,CountedProjection.range_value,CountedProjection.range_value]
  simp only [Nat.add_assoc,Nat.reduceAdd] at h1 h2 ha' hb' ⊢
  omega

def compress [DecidableEq S] (N : Nat) (step : S→Result S) (q : S) (accept : S→Result Bool) :
    Result (Option FiniteOrbit.Descriptor) :=
  let found:=findCycle N step q
  match found.1 with
  | none => (none,found.2+1)
  | some (i,j) =>
    let d:=describe step q accept i j
    (some d.1,found.2+d.2+1)

theorem compress_value [DecidableEq S] (e : FiniteRelation.Enumeration S)
    (step : S→Result S) (q : S) (accept : S→Result Bool) :
    (compress e.elems.length step q accept).1=
      FiniteOrbit.compress e (fun v=>(step v).1) q (fun v=>(accept v).1) := by
  unfold compress FiniteOrbit.compress FiniteOrbit.findCycle
  dsimp only
  rw [findCycle_value]
  cases h : FiniteOrbit.first (FiniteOrbit.valid (fun v=>(step v).1) q)
      (FiniteOrbit.pairs e.elems.length) with
  | none => rfl
  | some p => simp only [describe_value,Option.map]

def compressBudget (N C : Nat) : Nat := findBudget N C+describeBudget N C+1

theorem compress_work [DecidableEq S] (N C : Nat) (step : S→Result S) (q : S)
    (accept : S→Result Bool) (hs : ∀v,(step v).2≤C) (ha : ∀v,(accept v).2≤C) :
    (compress N step q accept).2≤compressBudget N C := by
  have hf:=findCycle_work N C step q hs
  unfold compress compressBudget
  dsimp only
  cases hp : (findCycle N step q).1 with
  | none => dsimp only; omega
  | some p =>
    have hb:=findCycle_bounds N step q p hp
    have hd:=describe_work step q accept p.1 p.2 N C hb.1 hb.2 hs ha
    dsimp only
    omega

theorem compress_lengths [DecidableEq S] (N : Nat) (step : S→Result S) (q : S)
    (accept : S→Result Bool) (D : FiniteOrbit.Descriptor)
    (hD : (compress N step q accept).1=some D) :
    D.initialCounts.length≤N ∧ D.residues.length≤N := by
  cases hf : (findCycle N step q).1 with
  | none =>
    simp only [compress,hf] at hD
    cases hD
  | some p =>
    have hb:=findCycle_bounds N step q p hf
    have he : (describe step q accept p.1 p.2).1=D := by
      simpa only [compress,hf,Option.some.injEq] using hD
    rw [←he,describe_value]
    simp only [FiniteOrbit.describe]
    exact ⟨Nat.le_trans (List.length_filter_le _ _) (by simpa using hb.1),
      Nat.le_trans (List.length_filter_le _ _) (by simp only [List.length_range]; omega)⟩

end REWB.PeriodicConstruction.Orbit
