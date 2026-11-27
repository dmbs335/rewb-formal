import REWB.PeriodicActualP2Cost
import REWB.PeriodicConstructionCacheCost
import REWB.PeriodicConstructionRunsCost

/-! Concrete primitive refinement of the actual P2 pipeline. Each
context, periodic cache and run enumeration is produced by its measured
builder exactly once. The first projection preserves the complete old
Bool/work result, not just the answer. The second explicitly combines
the measured construction with the existing ledger; duplicated old
transition charges are a safe overcount, never a second computation. -/
namespace REWB.PeriodicActual.FullCost.P2
open REWB.Periodic REWB.RunGeometry REWB.PeriodicConstruction
variable {α : Type}

def run [DecidableEq α] (P : SevenDFA α) (f : Nat→α)
    (I : BoundaryContexts.Index P) (R : Bounds) : (Bool×Nat)×Nat :=
  let cache:=Cache.prepareAt P (shift f R.lo) R.period I R.lo R.hi
  let choices:=Choices.p2 R.period
  let out:=PeriodicActual.P2.phases P (R.hi-R.lo) R.period cache.1.1 choices.1
  let old:=(out.1,cache.1.2+choices.2+out.2+10)
  (old,old.2+cache.2+6)

theorem run_value [DecidableEq α] (P : SevenDFA α) (f : Nat→α)
    (I : BoundaryContexts.Index P) (R : Bounds) :
    (run P f I R).1=PeriodicActual.P2.run P f I R := by
  simp only [run,Cache.prepareAt_value,PeriodicActual.P2.run]

def runFactor (P : SevenDFA α) : Nat := Cache.prepareCoefficient P+8

theorem runFactor_ge (P : SevenDFA α) : 8≤runFactor P := by
  unfold runFactor
  omega

theorem run_work [DecidableEq α] (P : SevenDFA α) (f : Nat→α)
    (I : BoundaryContexts.Index P) (R : Bounds) :
    (run P f I R).2≤runFactor P*(PeriodicActual.P2.run P f I R).2 := by
  let old:=PeriodicActual.P2.run P f I R
  have hb : (BoundaryContexts.countedPrepareAt P (shift f R.lo) R.period I R.lo R.hi).2+1≤old.2 := by
    dsimp only [old,PeriodicActual.P2.run]
    omega
  have hp : 1≤old.2 := by omega
  have hc:=Nat.le_trans (Cache.prepareAt_work_le_old P (shift f R.lo) R.period I R.lo R.hi)
    (Nat.mul_le_mul_left (Cache.prepareCoefficient P) hb)
  unfold run
  simp only [Cache.prepareAt_value]
  change old.2+(Cache.prepareAt P (shift f R.lo) R.period I R.lo R.hi).2+6≤
    runFactor P*old.2
  rw [runFactor,Nat.add_mul]
  omega

def runs [DecidableEq α] (P : SevenDFA α) (f : Nat→α)
    (I : BoundaryContexts.Index P) : List Bounds→(Bool×Nat)×Nat
  | []=>((false,1),8)
  | R::Rs=>
    let this:=run P f I R
    let rest:=runs P f I Rs
    ((this.1.1 || rest.1.1,this.1.2+rest.1.2+2),this.2+rest.2+8)

theorem runs_value [DecidableEq α] (P : SevenDFA α) (f : Nat→α)
    (I : BoundaryContexts.Index P) (Rs : List Bounds) :
    (runs P f I Rs).1=PeriodicActual.P2.runs P f I Rs := by
  induction Rs with
  | nil=>rfl
  | cons R Rs ih=>simp only [runs,PeriodicActual.P2.runs,run_value,ih]

theorem runs_work [DecidableEq α] (P : SevenDFA α) (f : Nat→α)
    (I : BoundaryContexts.Index P) (Rs : List Bounds) :
    (runs P f I Rs).2≤runFactor P*(PeriodicActual.P2.runs P f I Rs).2 := by
  induction Rs with
  | nil=>simpa only [runs,PeriodicActual.P2.runs,Nat.mul_one] using runFactor_ge P
  | cons R Rs ih=>
    have hh:=run_work P f I R
    have hk:=runFactor_ge P
    simp only [runs,PeriodicActual.P2.runs,Nat.mul_add]
    omega

def solve [DecidableEq α] (P : SevenDFA α) (f : Nat→α) (n Q : Nat) : (Bool×Nat)×Nat :=
  let text:=PeriodicActual.P2.segment f 0 n
  let contexts:=Cache.contexts P text.1
  let enumerated:=Runs.enumerate f n Q
  let cubic:=Orbit.filter (fun R : Bounds=>(decide (3*R.period≤R.hi-R.lo),3)) enumerated.1.1
  let out:=runs P f contexts.1.1 cubic.1
  let old:=(out.1.1,text.2+contexts.1.2+enumerated.1.2+cubic.2+out.1.2+8)
  (old,old.2+contexts.2+enumerated.2+out.2+8)

theorem solve_value [DecidableEq α] (P : SevenDFA α) (f : Nat→α) (n Q : Nat) :
    (solve P f n Q).1=PeriodicActual.P2.solve P f n Q := by
  simp only [solve,Cache.contexts_value,Runs.enumerate_value,runs_value,PeriodicActual.P2.solve]

theorem solve_answer [DecidableEq α] (P : SevenDFA α) (f : Nat→α) (n Q : Nat) :
    (solve P f n Q).1.1=(SmallPeriodP2.solve P f n Q).accepted := by
  rw [solve_value]
  exact PeriodicActual.P2.solve_value P f n Q

def solveFactor (P : SevenDFA α) : Nat := runFactor P+66

theorem solve_work [DecidableEq α] (P : SevenDFA α) (f : Nat→α) (n Q : Nat) :
    (solve P f n Q).2≤solveFactor P*(PeriodicActual.P2.solve P f n Q).2+
      (Runs.enumerate f n Q).2 := by
  let text:=PeriodicActual.P2.segment f 0 n
  let old:=PeriodicActual.P2.solve P f n Q
  let cubic:=Orbit.filter (fun R : Bounds=>(decide (3*R.period≤R.hi-R.lo),3))
    (SmallPeriodRuns.enumerate f n Q).1
  let out:=PeriodicActual.P2.runs P f (BoundaryContexts.build P text.1).1 cubic.1
  have hcontext : (BoundaryContexts.build P text.1).2≤old.2 := by
    dsimp only [old,PeriodicActual.P2.solve,text]
    omega
  have hout : out.2≤old.2 := by
    dsimp only [old,PeriodicActual.P2.solve,out,text,cubic]
    omega
  have hpos : 8≤old.2 := by
    dsimp only [old,PeriodicActual.P2.solve]
    omega
  have hc:=Nat.le_trans (Cache.contexts_work_le_old P text.1)
    (Nat.mul_le_mul_left 64 hcontext)
  have hr:=Nat.le_trans (runs_work P f (BoundaryContexts.build P text.1).1 cubic.1)
    (Nat.mul_le_mul_left (runFactor P) hout)
  unfold solve
  simp only [Cache.contexts_value,Runs.enumerate_value,runs_value]
  change old.2+(Cache.contexts P text.1).2+(Runs.enumerate f n Q).2+
    (runs P f (BoundaryContexts.build P text.1).1 cubic.1).2+8≤
    solveFactor P*old.2+(Runs.enumerate f n Q).2
  rw [solveFactor,Nat.add_mul]
  omega

end REWB.PeriodicActual.FullCost.P2
