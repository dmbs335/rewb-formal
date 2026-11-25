import REWB.PeriodicActualFullCostEvents
import REWB.PeriodicActualFullCostShort
import REWB.PeriodicActualFullCostP2Cost
import REWB.PeriodicActualPrepareCost
import REWB.PeriodicConstructionKeysCost

/-! Actual P1 preparations with measured exterior contexts, run discovery,
cache builders, exact key words and rank arrays. Each primitive executes
once. The complete frozen Prepared payload is reconstructed from these
results, and the second projection adds their construction counters.
The added counters intentionally overcount legacy transition charges. -/
namespace REWB.PeriodicActual.FullCost
open REWB.Periodic REWB.RunGeometry REWB.PeriodicConstruction
variable {σ : Nat}

namespace Long

def prepare (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    PeriodicActual.Prepared (Fin σ)×Nat :=
  let text:=PeriodicActual.P2.segment f 0 n
  let contexts:=Cache.contexts P text.1
  let enumerated:=Runs.enumerate f n Q
  let cubic:=Orbit.filter (fun R : Bounds=>(decide (3*R.period≤R.hi-R.lo),3)) enumerated.1.1
  let keys:=Keys.Rotation.tables ExactKeys.initial f cubic.1
  let events:=Events.runs P f contexts.1.1 Q keys.1.registry.next keys.1.tables
  let modulus:=ActualModulus.build events.1.sources events.1.targets
  let old : PeriodicActual.Prepared (Fin σ) :=
    ⟨text.1,events.1.sources,events.1.targets,modulus.1,
      text.2+contexts.1.2+enumerated.1.2+cubic.2+keys.1.work+events.1.work+modulus.2+20⟩
  (old,old.work+contexts.2+enumerated.2+keys.2+events.2+10)

theorem prepare_value (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (prepare P f n Q).1=PeriodicActual.Long.prepare P f n Q := by
  simp only [prepare,Cache.contexts_value,Runs.enumerate_value,
    Keys.Rotation.tables_value,Events.runs_value,PeriodicActual.Long.prepare]

theorem prepare_work (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (prepare P f n Q).2≤P2.solveFactor P*(PeriodicActual.Long.prepare P f n Q).work+
      (Runs.enumerate f n Q).2+
      (Keys.Rotation.tables ExactKeys.initial f (SmallPeriodRuns.cubic f n Q)).2 := by
  let text:=PeriodicActual.P2.segment f 0 n
  let old:=PeriodicActual.Long.prepare P f n Q
  let cubic:=Orbit.filter (fun R : Bounds=>(decide (3*R.period≤R.hi-R.lo),3))
    (SmallPeriodRuns.enumerate f n Q).1
  let keys:=ExactKeys.buildRunTables ExactKeys.initial f cubic.1
  let events:=PeriodicActual.Events.runs P f (BoundaryContexts.build P text.1).1 Q
    keys.registry.next keys.tables
  have hcontext : (BoundaryContexts.build P text.1).2≤old.work := by
    dsimp only [old,PeriodicActual.Long.prepare,text]
    omega
  have hevents : events.work≤old.work := by
    dsimp only [old,PeriodicActual.Long.prepare,events,text,cubic,keys]
    omega
  have hpos : 10≤old.work := by
    dsimp only [old,PeriodicActual.Long.prepare]
    omega
  have hc:=Nat.le_trans (Cache.contexts_work_le_old P text.1)
    (Nat.mul_le_mul_left 64 hcontext)
  have he:=Nat.le_trans (Events.runs_work P f (BoundaryContexts.build P text.1).1 Q
    keys.registry.next keys.tables) (Nat.mul_le_mul_left (P2.runFactor P) hevents)
  have hcube : cubic.1=SmallPeriodRuns.cubic f n Q := Orbit.filter_value _ _
  unfold prepare
  simp only [Cache.contexts_value,Runs.enumerate_value,Keys.Rotation.tables_value,Events.runs_value]
  rw [←hcube]
  change old.work+(Cache.contexts P text.1).2+(Runs.enumerate f n Q).2+
    (Keys.Rotation.tables ExactKeys.initial f cubic.1).2+
    (Events.runs P f (BoundaryContexts.build P text.1).1 Q keys.registry.next keys.tables).2+10≤
    P2.solveFactor P*old.work+(Runs.enumerate f n Q).2+
    (Keys.Rotation.tables ExactKeys.initial f cubic.1).2
  rw [P2.solveFactor,Nat.add_mul]
  omega

end Long

namespace Short

def prepare (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    PeriodicActual.Prepared (Fin σ)×Nat :=
  let text:=PeriodicActual.P2.segment f 0 n
  let contexts:=Cache.contexts P text.1
  let enumerated:=Runs.enumerate f n Q
  let cubic:=Orbit.filter (fun R : Bounds=>(decide (3*R.period≤R.hi-R.lo),3)) enumerated.1.1
  let choices:=PeriodicActual.Short.sourceChoices n (3*Q)
  let sk:=PeriodicActual.Short.sourceKeys ExactKeys.initial f choices.1
  let tk:=Keys.Short.tables sk.1.registry f cubic.1
  let src:=PeriodicActual.Short.sources P contexts.1.1 sk.1.entries
  let tgt:=runs P f contexts.1.1 tk.1.tables
  let old : PeriodicActual.Prepared (Fin σ) :=
    ⟨text.1,src.1,tgt.1.1,1,
      text.2+contexts.1.2+enumerated.1.2+cubic.2+choices.2+sk.1.work+sk.2+
        tk.1.work+src.2+tgt.1.2+20⟩
  (old,old.work+contexts.2+enumerated.2+tk.2+tgt.2+10)

theorem prepare_value (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (prepare P f n Q).1=PeriodicActual.Short.prepare P f n Q := by
  simp only [prepare,Cache.contexts_value,Runs.enumerate_value,
    Keys.Short.tables_value,runs_value,PeriodicActual.Short.prepare]

theorem prepare_work (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) :
    (prepare P f n Q).2≤P2.solveFactor P*(PeriodicActual.Short.prepare P f n Q).work+
      (Runs.enumerate f n Q).2+
      (Keys.Short.tables
        (PeriodicActual.Short.sourceKeys ExactKeys.initial f
          (PeriodicActual.Short.sourceChoices n (3*Q)).1).1.registry
        f (SmallPeriodRuns.cubic f n Q)).2 := by
  let text:=PeriodicActual.P2.segment f 0 n
  let old:=PeriodicActual.Short.prepare P f n Q
  let cubic:=Orbit.filter (fun R : Bounds=>(decide (3*R.period≤R.hi-R.lo),3))
    (SmallPeriodRuns.enumerate f n Q).1
  let sk:=PeriodicActual.Short.sourceKeys ExactKeys.initial f
    (PeriodicActual.Short.sourceChoices n (3*Q)).1
  let tk:=P1ShortKeys.buildRunTables sk.1.registry f cubic.1
  let tgt:=PeriodicActual.Short.runs P f (BoundaryContexts.build P text.1).1 tk.tables
  have hcontext : (BoundaryContexts.build P text.1).2≤old.work := by
    dsimp only [old,PeriodicActual.Short.prepare,text]
    omega
  have htgt : tgt.2≤old.work := by
    dsimp only [old,PeriodicActual.Short.prepare,tgt,text,cubic,sk,tk]
    omega
  have hpos : 10≤old.work := by
    dsimp only [old,PeriodicActual.Short.prepare]
    omega
  have hc:=Nat.le_trans (Cache.contexts_work_le_old P text.1)
    (Nat.mul_le_mul_left 64 hcontext)
  have ht:=Nat.le_trans (runs_work P f (BoundaryContexts.build P text.1).1 tk.tables)
    (Nat.mul_le_mul_left (P2.runFactor P) htgt)
  have hcube : cubic.1=SmallPeriodRuns.cubic f n Q := Orbit.filter_value _ _
  unfold prepare
  simp only [Cache.contexts_value,Runs.enumerate_value,Keys.Short.tables_value,runs_value]
  rw [←hcube]
  change old.work+(Cache.contexts P text.1).2+(Runs.enumerate f n Q).2+
    (Keys.Short.tables sk.1.registry f cubic.1).2+
    (runs P f (BoundaryContexts.build P text.1).1 tk.tables).2+10≤
    P2.solveFactor P*old.work+(Runs.enumerate f n Q).2+
    (Keys.Short.tables sk.1.registry f cubic.1).2
  rw [P2.solveFactor,Nat.add_mul]
  omega

end Short
end REWB.PeriodicActual.FullCost
