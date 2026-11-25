import REWB.SmallPeriodRuns
import REWB.CountedProjection

/-! Construction-counted small-period run enumeration. The first
projection retains both the original run list and comparison counter.
The second projection charges the executed list/range/array/append
traversals, branch tests, bounded field accesses and arithmetic. Character
access and equality are primitive operations, as for a materialized
finite-alphabet text; this is not a bit-complexity claim. -/
namespace REWB.PeriodicConstruction.Runs
open REWB.Periodic REWB.RunGeometry REWB.RunExtension

def arrayLoop : List Nat→Array Nat→Nat→Array Nat×Nat
  | [],out,work=>(out,work+1)
  | x::xs,out,work=>arrayLoop xs (out.push x) (work+4)

theorem arrayLoop_list (xs : List Nat) (out : Array Nat) (work : Nat) :
    (arrayLoop xs out work).1.toList=out.toList++xs := by
  induction xs generalizing out work with
  | nil=>simp [arrayLoop]
  | cons x xs ih=>
    rw [arrayLoop,ih]
    simp [List.append_assoc]

theorem arrayLoop_work (xs : List Nat) (out : Array Nat) (work : Nat) :
    (arrayLoop xs out work).2=work+4*xs.length+1 := by
  induction xs generalizing out work with
  | nil=>simp [arrayLoop]
  | cons x xs ih=>
    rw [arrayLoop,ih]
    simp only [List.length_cons,Nat.mul_add,Nat.mul_one]
    omega

def materialize (xs : List Nat) : Array Nat×Nat:=arrayLoop xs #[] 0

theorem materialize_value (xs : List Nat) : (materialize xs).1=xs.toArray := by
  apply Array.toList_inj.mp
  simp [materialize,arrayLoop_list]

theorem materialize_work (xs : List Nat) : (materialize xs).2=4*xs.length+1 := by
  simp only [materialize,arrayLoop_work,Nat.zero_add]

variable {α : Type} [DecidableEq α]

def ends (f : Nat→α) (p : Nat) : Nat→Nat→(List Nat×Nat)×Nat
  | a,0=>(([a],0),2)
  | a,k+1=>
    let ⟨⟨tail,comparisons⟩,work⟩:=ends f p (a+1) k
    (((if f a=f (a+p) then tail.headD (a+1) else a)::tail,comparisons+1),work+9)

theorem ends_value (f : Nat→α) (p a k : Nat) :
    (ends f p a k).1=SmallPeriodRuns.ends f p a k := by
  induction k generalizing a with
  | zero=>rfl
  | succ k ih=>simp only [ends,SmallPeriodRuns.ends,ih]

theorem ends_length (f : Nat→α) (p a k : Nat) : (ends f p a k).1.1.length=k+1 := by
  induction k generalizing a with
  | zero=>rfl
  | succ k ih=>simp only [ends,List.length_cons,ih]

theorem ends_work (f : Nat→α) (p a k : Nat) : (ends f p a k).2=9*k+2 := by
  induction k generalizing a with
  | zero=>rfl
  | succ k ih=>simp only [ends,ih,Nat.mul_add,Nat.mul_one]; omega

def allCounted (test : Nat→(Bool×Nat)×Nat) : List Nat→(Bool×Nat)×Nat
  | []=>((true,0),1)
  | x::xs=>
    let ⟨⟨a,ac⟩,aw⟩:=test x
    let ⟨⟨b,bc⟩,bw⟩:=allCounted test xs
    ((a && b,ac+bc),aw+bw+4)

theorem allCounted_value (test : Nat→(Bool×Nat)×Nat) (xs : List Nat) :
    (allCounted test xs).1=SmallPeriodRuns.allCounted (fun x=>(test x).1) xs := by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>simp only [allCounted,SmallPeriodRuns.allCounted,ih]

theorem allCounted_work (test : Nat→(Bool×Nat)×Nat) (xs : List Nat) (bound : Nat)
    (ht : ∀x,x∈xs→(test x).2≤bound) :
    (allCounted test xs).2≤xs.length*(bound+4)+1 := by
  induction xs with
  | nil=>simp [allCounted]
  | cons x xs ih=>
    have hh:=ht x List.mem_cons_self
    have hh':=ih (fun y hy=>ht y (List.mem_cons_of_mem x hy))
    simp only [allCounted,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

def period (f : Nat→α) (i L p : Nat) : (Bool×Nat)×Nat :=
  let positions:=CountedProjection.range (L-p)
  let ⟨answer,work⟩:=allCounted (fun j=>((decide (f (i+j)=f (i+j+p)),1),6)) positions.1
  (answer,2*positions.2+work+3)

theorem period_value (f : Nat→α) (i L p : Nat) :
    (period f i L p).1=SmallPeriodRuns.period f i L p := by
  simp only [period,allCounted_value,CountedProjection.range_value,SmallPeriodRuns.period]

def shorter (f : Nat→α) (i p q : Nat) : (Bool×Nat)×Nat :=
  if q=0 then ((true,0),2)
  else
    let ⟨answer,work⟩:=period f i (2*p) q
    ((!answer.1,answer.2),work+3)

theorem shorter_value (f : Nat→α) (i p q : Nat) :
    (shorter f i p q).1=
      (if q=0 then (true,0) else
        let answer:=SmallPeriodRuns.period f i (2*p) q
        (!answer.1,answer.2)) := by
  unfold shorter
  split <;> simp only [period_value]

def square (f : Nat→α) (n i p : Nat) : (Bool×Nat)×Nat :=
  let ⟨a,aw⟩:=period f i (2*p) p
  let periods:=CountedProjection.range p
  let ⟨b,bw⟩:=allCounted (shorter f i p) periods.1
  ((decide (0<p ∧ i+2*p≤n) && a.1 && b.1,a.2+b.2),
    aw+2*periods.2+bw+10)

theorem square_value (f : Nat→α) (n i p : Nat) :
    (square f n i p).1=SmallPeriodRuns.square f n i p := by
  simp only [square,period_value,allCounted_value,shorter_value,
    CountedProjection.range_value,SmallPeriodRuns.square]

def isLeft (f : Nat→α) (p i : Nat) : Bool×Nat :=
  (decide (i=0 ∨ f (i-1)≠f (i-1+p)),8)

def endAt (T : Array Nat) (i : Nat) : Nat×Nat:=(T[i]?.getD i,3)

def candidate (f : Nat→α) (n p : Nat) (T : Array Nat) (i : Nat) : (Option Bounds×Nat)×Nat :=
  let left:=isLeft f p i
  if left.1 then
    let ⟨answer,work⟩:=square f n i p
    if answer.1 then
      let endpoint:=endAt T i
      ((some ⟨i,endpoint.1+p,p⟩,answer.2+1),left.2+work+endpoint.2+8)
    else ((none,answer.2+1),left.2+work+4)
  else ((none,1),left.2+2)

theorem candidate_value (f : Nat→α) (n p : Nat) (T : Array Nat) (i : Nat) :
    (candidate f n p T i).1=SmallPeriodRuns.candidate f n p T i := by
  simp only [candidate,isLeft,square_value,endAt,SmallPeriodRuns.candidate,
    SmallPeriodRuns.isLeft,SmallPeriodRuns.endAt]
  split <;> (try split) <;> rfl

def collect (f : Nat→α) (n p : Nat) (T : Array Nat) : List Nat→(List Bounds×Nat)×Nat
  | []=>(([],0),1)
  | i::is=>
    let ⟨a,aw⟩:=candidate f n p T i
    let ⟨b,bw⟩:=collect f n p T is
    ((match a.1 with | none=>b.1 | some R=>R::b.1,a.2+b.2),aw+bw+4)

theorem collect_value (f : Nat→α) (n p : Nat) (T : Array Nat) (xs : List Nat) :
    (collect f n p T xs).1=SmallPeriodRuns.collect f n p T xs := by
  induction xs with
  | nil=>rfl
  | cons i is ih=>simp only [collect,SmallPeriodRuns.collect,candidate_value,ih]

theorem collect_length (f : Nat→α) (n p : Nat) (T : Array Nat) (xs : List Nat) :
    (collect f n p T xs).1.1.length≤xs.length := by
  induction xs with
  | nil=>exact Nat.le_refl _
  | cons i is ih=>
    simp only [collect,List.length_cons]
    cases (candidate f n p T i).1.1 <;> simp only [List.length_cons] <;> omega

def forPeriod (f : Nat→α) (n p : Nat) : (List Bounds×Nat)×Nat :=
  let ⟨table,tableWork⟩:=ends f p 0 (n-p)
  let cells:=materialize table.1
  let positions:=CountedProjection.range (n+1)
  let ⟨found,foundWork⟩:=collect f n p cells.1 positions.1
  ((found.1,table.2+found.2),tableWork+cells.2+2*positions.2+foundWork+8)

theorem forPeriod_value (f : Nat→α) (n p : Nat) :
    (forPeriod f n p).1=SmallPeriodRuns.forPeriod f n p := by
  simp only [forPeriod,ends_value,materialize_value,CountedProjection.range_value,
    collect_value,SmallPeriodRuns.forPeriod]

theorem forPeriod_length (f : Nat→α) (n p : Nat) : (forPeriod f n p).1.1.length≤n+1 := by
  have hh:=collect_length f n p (materialize (ends f p 0 (n-p)).1.1).1
    (CountedProjection.range (n+1)).1
  simpa only [forPeriod,CountedProjection.range_value,List.length_range] using hh

def enumerate (f : Nat→α) (n : Nat) : Nat→(List Bounds×Nat)×Nat
  | 0=>(([],0),1)
  | Q+1=>
    let ⟨here,hereWork⟩:=forPeriod f n (Q+1)
    let ⟨prior,priorWork⟩:=enumerate f n Q
    let joined:=CountedProjection.append here.1 prior.1
    ((joined.1,here.2+prior.2),hereWork+priorWork+3*joined.2+4)

theorem enumerate_value (f : Nat→α) (n Q : Nat) :
    (enumerate f n Q).1=SmallPeriodRuns.enumerate f n Q := by
  induction Q with
  | zero=>rfl
  | succ Q ih=>
    simp only [enumerate,forPeriod_value,ih,CountedProjection.append_value,SmallPeriodRuns.enumerate]

theorem enumerate_length (f : Nat→α) (n Q : Nat) :
    (enumerate f n Q).1.1.length≤Q*(n+1) := by
  induction Q with
  | zero=>exact Nat.le_refl _
  | succ Q ih=>
    have hh:=forPeriod_length f n (Q+1)
    simp only [enumerate,CountedProjection.append_value,List.length_append,Nat.add_mul,Nat.one_mul]
    omega

def cubicFilter : List Bounds→List Bounds×Nat
  | []=>([],1)
  | R::Rs=>
    let rest:=cubicFilter Rs
    ((if decide (3*R.period≤R.hi-R.lo) then R::rest.1 else rest.1),rest.2+9)

theorem cubicFilter_value (runs : List Bounds) :
    (cubicFilter runs).1=runs.filter (fun R=>decide (3*R.period≤R.hi-R.lo)) := by
  induction runs with
  | nil=>rfl
  | cons R Rs ih=>simp only [cubicFilter,List.filter_cons,ih]

theorem cubicFilter_work (runs : List Bounds) : (cubicFilter runs).2=9*runs.length+1 := by
  induction runs with
  | nil=>rfl
  | cons R Rs ih=>
    simp only [cubicFilter,ih,List.length_cons,Nat.mul_add,Nat.mul_one]
    omega

/-- The old comparison field is retained together with the filtered
list, so a caller can construct the complete original solver result
without executing the unfiltered enumerator a second time. -/
def cubic (f : Nat→α) (n Q : Nat) : (List Bounds×Nat)×Nat :=
  let ⟨all,allWork⟩:=enumerate f n Q
  let kept:=cubicFilter all.1
  ((kept.1,all.2),allWork+kept.2+2)

theorem cubic_value (f : Nat→α) (n Q : Nat) :
    (cubic f n Q).1=(SmallPeriodRuns.cubic f n Q,(SmallPeriodRuns.enumerate f n Q).2) := by
  simp only [cubic,enumerate_value,cubicFilter_value,SmallPeriodRuns.cubic]

theorem enumerate_comparisons (f : Nat→α) (n Q : Nat) :
    (enumerate f n Q).1.2≤Q*(n+(n+1)*(2*Q*(Q+1)+1)) := by
  rw [enumerate_value]
  exact SmallPeriodRuns.enumerate_cost f n Q

end REWB.PeriodicConstruction.Runs
