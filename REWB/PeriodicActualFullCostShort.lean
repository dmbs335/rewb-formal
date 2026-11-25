import REWB.PeriodicActualShort
import REWB.PeriodicActualFullCostP2

/-! Short P1 targets use one actual measured cache per run, while the
frozen target formula and exponent decisions are executed once per
scheduled choice. The whole old event/work pair is retained. This layer
does not claim to reduce the constant cost of five-variable projection. -/
namespace REWB.PeriodicActual.FullCost.Short
open REWB.Periodic REWB.RunGeometry REWB.PeriodicConstruction
variable {σ : Nat}

def run (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (I : BoundaryContexts.Index P)
    (e : Bounds×Array Nat) : (List TimedJoin.TimedEntry×Nat)×Nat :=
  let cache:=Cache.prepareAt P (shift f e.1.lo) e.1.period I e.1.lo e.1.hi
  let choices:=Choices.targets e.1.period (e.1.hi-e.1.lo)
  let out:=CountedProjection.flatMap (fun z : Nat×P1PhaseFamily.Three=>
    PeriodicActual.Short.choice P (e.1.hi-e.1.lo) e.1.period e.1.lo z.1 z.2 cache.1.1 e.2) choices.1
  let old:=(out.1,cache.1.2+choices.2+out.2+10)
  (old,old.2+cache.2+6)

theorem run_value (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (I : BoundaryContexts.Index P)
    (e : Bounds×Array Nat) :
    (run P f I e).1=PeriodicActual.Short.run P f I e := by
  simp only [run,Cache.prepareAt_value,PeriodicActual.Short.run]

theorem run_work (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (I : BoundaryContexts.Index P)
    (e : Bounds×Array Nat) :
    (run P f I e).2≤P2.runFactor P*(PeriodicActual.Short.run P f I e).2 := by
  let old:=PeriodicActual.Short.run P f I e
  have hb : (BoundaryContexts.countedPrepareAt P (shift f e.1.lo) e.1.period I e.1.lo e.1.hi).2+1≤old.2 := by
    dsimp only [old,PeriodicActual.Short.run]
    omega
  have hp : 1≤old.2 := by omega
  have hc:=Nat.le_trans (Cache.prepareAt_work_le_old P (shift f e.1.lo) e.1.period I e.1.lo e.1.hi)
    (Nat.mul_le_mul_left (Cache.prepareCoefficient P) hb)
  unfold run
  simp only [Cache.prepareAt_value]
  change old.2+(Cache.prepareAt P (shift f e.1.lo) e.1.period I e.1.lo e.1.hi).2+6≤
    P2.runFactor P*old.2
  rw [P2.runFactor,Nat.add_mul]
  omega

def runs (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (I : BoundaryContexts.Index P) :
    List (Bounds×Array Nat)→(List TimedJoin.TimedEntry×Nat)×Nat
  | []=>(([],1),8)
  | e::es=>
    let this:=run P f I e
    let rest:=runs P f I es
    let out:=CountedProjection.append this.1.1 rest.1.1
    ((out.1,this.1.2+rest.1.2+out.2+3),this.2+rest.2+out.2+9)

theorem runs_value (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (I : BoundaryContexts.Index P)
    (es : List (Bounds×Array Nat)) :
    (runs P f I es).1=PeriodicActual.Short.runs P f I es := by
  induction es with
  | nil=>rfl
  | cons e es ih=>simp only [runs,PeriodicActual.Short.runs,run_value,ih]

theorem runs_work (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (I : BoundaryContexts.Index P)
    (es : List (Bounds×Array Nat)) :
    (runs P f I es).2≤P2.runFactor P*(PeriodicActual.Short.runs P f I es).2 := by
  induction es with
  | nil=>simpa only [runs,PeriodicActual.Short.runs,Nat.mul_one] using P2.runFactor_ge P
  | cons e es ih=>
    have hh:=run_work P f I e
    have hk : 3≤P2.runFactor P := by have h:=P2.runFactor_ge P; omega
    have h1 : 1≤P2.runFactor P := by omega
    have ha:=Nat.mul_le_mul_right
      (CountedProjection.append (PeriodicActual.Short.run P f I e).1
        (PeriodicActual.Short.runs P f I es).1).2 h1
    have hc:=Nat.mul_le_mul_right 3 hk
    simp only [Nat.one_mul] at ha
    simp only [runs,PeriodicActual.Short.runs,run_value,runs_value,Nat.mul_add]
    omega

end REWB.PeriodicActual.FullCost.Short
