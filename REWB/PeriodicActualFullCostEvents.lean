import REWB.PeriodicActualEvents
import REWB.PeriodicActualFullCostP2

/-! Long P1 events with the actual measured periodic cache. Source and
target formulas, phase order, append order and the entire old Batch are
preserved. The new counter pays for the executed cache and pair/list
assembly. No legacy event generator is rerun to recover its counters. -/
namespace REWB.PeriodicActual.FullCost.Events
open REWB.Periodic REWB.RunGeometry REWB.PeriodicConstruction
variable {σ : Nat}

def run (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (I : BoundaryContexts.Index P)
    (Q next : Nat) (e : Bounds×Array Nat) : PeriodicActual.Events.Batch×Nat :=
  let cache:=Cache.prepareAt P (shift f e.1.lo) e.1.period I e.1.lo e.1.hi
  let sourceChoices:=Choices.sources e.1.period (e.1.hi-e.1.lo)
  let targetChoices:=Choices.targets e.1.period (e.1.hi-e.1.lo)
  let sources:=CountedProjection.map
    (PeriodicActual.Events.source P Q next e.1 e.2 cache.1.1) sourceChoices.1
  let targets:=CountedProjection.map
    (PeriodicActual.Events.target P Q next e.1 e.2 cache.1.1) targetChoices.1
  let old : PeriodicActual.Events.Batch :=
    ⟨sources.1,targets.1,cache.1.2+sourceChoices.2+targetChoices.2+sources.2+targets.2+10⟩
  (old,old.work+cache.2+6)

theorem run_value (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (I : BoundaryContexts.Index P)
    (Q next : Nat) (e : Bounds×Array Nat) :
    (run P f I Q next e).1=PeriodicActual.Events.run P f I Q next e := by
  simp only [run,Cache.prepareAt_value,PeriodicActual.Events.run]

theorem run_work (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (I : BoundaryContexts.Index P)
    (Q next : Nat) (e : Bounds×Array Nat) :
    (run P f I Q next e).2≤P2.runFactor P*(PeriodicActual.Events.run P f I Q next e).work := by
  let old:=PeriodicActual.Events.run P f I Q next e
  have hb : (BoundaryContexts.countedPrepareAt P (shift f e.1.lo) e.1.period I e.1.lo e.1.hi).2+1≤old.work := by
    dsimp only [old,PeriodicActual.Events.run]
    omega
  have hp : 1≤old.work := by omega
  have hc:=Nat.le_trans (Cache.prepareAt_work_le_old P (shift f e.1.lo) e.1.period I e.1.lo e.1.hi)
    (Nat.mul_le_mul_left (Cache.prepareCoefficient P) hb)
  unfold run
  simp only [Cache.prepareAt_value]
  change old.work+(Cache.prepareAt P (shift f e.1.lo) e.1.period I e.1.lo e.1.hi).2+6≤
    P2.runFactor P*old.work
  rw [P2.runFactor,Nat.add_mul]
  omega

def runs (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (I : BoundaryContexts.Index P)
    (Q next : Nat) : List (Bounds×Array Nat)→PeriodicActual.Events.Batch×Nat
  | []=>({},8)
  | e::es=>
    let this:=run P f I Q next e
    let rest:=runs P f I Q next es
    let sources:=CountedProjection.append this.1.sources rest.1.sources
    let targets:=CountedProjection.append this.1.targets rest.1.targets
    (⟨sources.1,targets.1,this.1.work+rest.1.work+sources.2+targets.2+6⟩,
      this.2+rest.2+sources.2+targets.2+12)

theorem runs_value (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (I : BoundaryContexts.Index P)
    (Q next : Nat) (es : List (Bounds×Array Nat)) :
    (runs P f I Q next es).1=PeriodicActual.Events.runs P f I Q next es := by
  induction es with
  | nil=>rfl
  | cons e es ih=>simp only [runs,PeriodicActual.Events.runs,run_value,ih]

theorem runs_work (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (I : BoundaryContexts.Index P)
    (Q next : Nat) (es : List (Bounds×Array Nat)) :
    (runs P f I Q next es).2≤P2.runFactor P*(PeriodicActual.Events.runs P f I Q next es).work := by
  induction es with
  | nil=>simpa only [runs,PeriodicActual.Events.runs,Nat.mul_one] using P2.runFactor_ge P
  | cons e es ih=>
    have hh:=run_work P f I Q next e
    have hk : 2≤P2.runFactor P := by have h:=P2.runFactor_ge P; omega
    have h1 : 1≤P2.runFactor P := by omega
    have hs:=Nat.mul_le_mul_right
      (CountedProjection.append (PeriodicActual.Events.run P f I Q next e).sources
        (PeriodicActual.Events.runs P f I Q next es).sources).2 h1
    have ht:=Nat.mul_le_mul_right
      (CountedProjection.append (PeriodicActual.Events.run P f I Q next e).targets
        (PeriodicActual.Events.runs P f I Q next es).targets).2 h1
    have hc:=Nat.mul_le_mul_right 6 hk
    simp only [Nat.one_mul] at hs ht
    simp only [runs,PeriodicActual.Events.runs,run_value,runs_value,Nat.mul_add]
    omega

end REWB.PeriodicActual.FullCost.Events
