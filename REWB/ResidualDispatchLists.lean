import REWB.ResidualRunWindows
import REWB.ResidualStripScheduleCost

/-! Counted construction of low-start and large-period selector rows.
Both traversals consume one retained generated run list. Every range,
mapped tuple, copied output cell and fixed arithmetic step is charged;
the proof-side reference schedules are not executed by these functions. -/
namespace REWB.ResidualDispatch
open REWB.RunGeometry REWB.GlobalCoverage
abbrev Row := Bounds×(Nat×Nat)

def lowRow (x : Bounds×Nat) : Row := (x.1,(x.2,x.1.period))

def lowOne (D : Nat) (R : Bounds) : List Row×Nat :=
  let starts:=CountedProjection.range (RunBudget.mass R+D)
  let rows:=CountedProjection.map (fun i=>((R,(R.lo+i,R.period)),3)) starts.1
  (rows.1,starts.2+rows.2+3)

theorem lowOne_value (D : Nat) (R : Bounds) :
    (lowOne D R).1=((lowStarts R D).map (fun p=>(R,p))).map lowRow := by
  simp only [lowOne,CountedProjection.map_value,CountedProjection.range_value,
    lowStarts,List.map_map,Function.comp_def,lowRow]

theorem lowOne_length (D : Nat) (R : Bounds) : (lowOne D R).1.length=RunBudget.mass R+D := by
  simp only [lowOne,CountedProjection.map_value,CountedProjection.range_value,List.length_map,List.length_range]

theorem lowOne_work (D : Nat) (R : Bounds) : (lowOne D R).2=6*(RunBudget.mass R+D)+5 := by
  simp only [lowOne,CountedProjection.map_plain_steps,CountedProjection.range,CountedProjection.rangeFrom_steps,
    CountedProjection.rangeFrom_value,List.length_range']
  omega

def lowRows (D : Nat) (Rs : List Bounds) : List Row×Nat := CountedProjection.flatMap (lowOne D) Rs

theorem lowRows_value (D : Nat) (Rs : List Bounds) :
    (lowRows D Rs).1=(lowSchedule D Rs).map lowRow := by
  induction Rs with
  | nil => rfl
  | cons R Rs ih =>
    simp only [lowRows,CountedProjection.flatMap,CountedProjection.append_value,
      lowSchedule,List.map_append]
    change (lowOne D R).1++(lowRows D Rs).1=_
    rw [lowOne_value,ih]

theorem lowRows_work (D : Nat) (Rs : List Bounds) :
    (lowRows D Rs).2≤14*(lowSchedule D Rs).length+1 := by
  induction Rs with
  | nil => exact Nat.le_refl _
  | cons R Rs ih =>
    have hp : 1≤RunBudget.mass R+D := by unfold RunBudget.mass; omega
    simp only [lowRows,CountedProjection.flatMap,CountedProjection.append_steps]
    change (lowOne D R).2+(lowRows D Rs).2+((lowOne D R).1.length+1)+1≤_
    rw [lowOne_work,lowOne_length]
    simp only [lowSchedule,List.length_append,List.length_map,lowStarts_length,Nat.mul_add]
    omega

def largeAt (R : Bounds) (j : Nat) : List Row×Nat :=
  let d:=(j+1)*R.period
  let starts:=CountedProjection.range (R.hi-R.lo+1)
  let rows:=CountedProjection.map (fun i=>((R,(R.lo+i,d)),2)) starts.1
  (rows.1,starts.2+rows.2+5)

theorem largeAt_value (R : Bounds) (j : Nat) :
    (largeAt R j).1=(List.range (R.hi-R.lo+1)).map (fun i=>(R,(R.lo+i,(j+1)*R.period))) := by
  simp only [largeAt,CountedProjection.map_value,CountedProjection.range_value]

theorem largeAt_length (R : Bounds) (j : Nat) : (largeAt R j).1.length=R.hi-R.lo+1 := by
  rw [largeAt_value,List.length_map,List.length_range]

theorem largeAt_work (R : Bounds) (j : Nat) : (largeAt R j).2=5*(R.hi-R.lo+1)+7 := by
  simp only [largeAt,CountedProjection.map_plain_steps,CountedProjection.range,
    CountedProjection.rangeFrom_steps,CountedProjection.rangeFrom_value,List.length_range']
  omega

def largeOne (R : Bounds) : List Row×Nat :=
  let multiples:=CountedProjection.range ((R.hi-R.lo)/R.period)
  let rows:=CountedProjection.flatMap (largeAt R) multiples.1
  (rows.1,multiples.2+rows.2+3)

theorem largeOne_value (R : Bounds) :
    (largeOne R).1=(largePairs R).map (fun pd=>(R,pd)) := by
  simp only [largeOne,CountedProjection.flatMap_value,CountedProjection.range_value,
    largePairs,List.map_flatMap,List.map_map,Function.comp_def,largeAt_value]

theorem largeOne_length (R : Bounds) : (largeOne R).1.length=(largePairs R).length := by
  rw [largeOne_value,List.length_map]

theorem largeOne_work (R : Bounds) : (largeOne R).2≤17*(largePairs R).length+5 := by
  have hh:=CountedProjection.flatMap_steps_constant (largeAt R)
    (List.range ((R.hi-R.lo)/R.period)) (5*(R.hi-R.lo+1)+7) (R.hi-R.lo+1)
    (fun j _=>largeAt_work R j) (fun j _=>largeAt_length R j)
  have hp:=Nat.mul_le_mul_left ((R.hi-R.lo)/R.period) (show 1≤R.hi-R.lo+1 by omega)
  simp only [Nat.mul_one] at hp
  simp only [largeOne,CountedProjection.range_value]
  simp only [CountedProjection.range,CountedProjection.rangeFrom_steps]
  rw [hh,List.length_range,largePairs_length]
  have calcBound (v z : Nat) (hz : z≤z*v) :
      2*z+1+(z*(5*v+7+v+2)+1)+3≤17*(z*v)+5 := by
    rw [show 5*v+7+v+2=6*v+9 by omega,Nat.mul_add,
      show z*(6*v)=6*(z*v) by ac_rfl,Nat.mul_comm z 9]
    omega
  exact calcBound _ _ hp

def largeChosen (Q : Nat) (R : Bounds) : List Row×Nat :=
  if Q<R.period ∧ 3*R.period≤R.hi-R.lo then
    let out:=largeOne R
    (out.1,out.2+5)
  else ([],5)

def largeRows (Q : Nat) (Rs : List Bounds) : List Row×Nat := CountedProjection.flatMap (largeChosen Q) Rs

theorem largeRows_value (Q : Nat) (Rs : List Bounds) :
    (largeRows Q Rs).1=largeSchedule (Rs.filter (fun R=>decide (Q<R.period ∧ 3*R.period≤R.hi-R.lo))) := by
  induction Rs with
  | nil => rfl
  | cons R Rs ih =>
    simp only [largeRows,CountedProjection.flatMap,CountedProjection.append_value,
      List.filter_cons]
    change (largeChosen Q R).1++(largeRows Q Rs).1=_
    rw [ih]
    unfold largeChosen
    split
    next h => simp only [decide_eq_true h,if_true,largeOne_value,largeSchedule]
    next h => simp only [decide_eq_false h,Bool.false_eq_true,if_false,List.nil_append]

theorem largeRows_work (Q : Nat) (Rs : List Bounds) :
    (largeRows Q Rs).2≤18*(largeRows Q Rs).1.length+12*Rs.length+1 := by
  induction Rs with
  | nil => exact Nat.le_refl _
  | cons R Rs ih =>
    simp only [largeRows,CountedProjection.flatMap,CountedProjection.append_steps,CountedProjection.append_value,
      List.length_append,List.length_cons,Nat.mul_add,Nat.mul_succ]
    change (largeChosen Q R).2+(largeRows Q Rs).2+((largeChosen Q R).1.length+1)+1≤
      18*(largeChosen Q R).1.length+18*(largeRows Q Rs).1.length+12*Rs.length+12+1
    unfold largeChosen
    split
    · have hh:=largeOne_work R
      simp only [largeOne_length]
      omega
    · simp only [List.length_nil,Nat.mul_zero]
      omega

end REWB.ResidualDispatch
