import REWB.PeriodicConstructionKeysCost

/-! Actual key constructors versus the independent legacy constructors.
Only scalar polynomial bounds are evaluated here; no finite coefficient
families or projected formulas are enumerated. -/
namespace REWB.PeriodicConstruction.Keys.Audit

def check (p : Bool) (s : String) : IO Unit :=
  unless p do throw (IO.userError s)

def reader (kind : Nat) : Nat→Fin 2 :=
  fun i=>if kind=0 ∨ (i/kind)%2=0 then 0 else 1

def checkIntern (f : Nat→Fin 2) (q : Nat) : IO Nat := do
  let rotation:=Rotation.intern ExactKeys.initial f q
  let oldRotation:=ExactKeys.internRotations ExactKeys.initial f q
  check (rotation.1.ranks=oldRotation.ranks &&
    rotation.1.work=oldRotation.work &&
    rotation.1.registry.next=oldRotation.registry.next) "rotation result mismatch"
  check (rotation.2=oldRotation.work+4*q^2+9*q+17) "rotation construction work"
  let words:=Short.words f q
  check (words.1=P1ShortKeys.words f q) "short word list/order mismatch"
  check (words.2≤160*q^3+160*q^2+10) "short word construction bound"
  let short:=Short.intern rotation.1.registry f q
  let oldShort:=P1ShortKeys.internShorts oldRotation.registry f q
  check (short.1.ranks=oldShort.ranks && short.1.work=oldShort.work &&
    short.1.registry.next=oldShort.registry.next) "short result mismatch"
  check (short.2≤oldShort.work+200*(q^3+q^2+1)) "short construction work"
  for w in ExactKeys.rotations f q++words.1 do
    check (ExactKeys.lookup short.1.registry.tree w=
      ExactKeys.lookup oldShort.registry.tree w) "final registry mismatch"
  return q+words.1.length

def checkTables (f : Nat→Fin 2) (n Q : Nat) : IO Nat := do
  let runs:=SmallPeriodRuns.cubic f n Q
  let rotation:=Rotation.tables ExactKeys.initial f runs
  let oldRotation:=ExactKeys.buildRunTables ExactKeys.initial f runs
  check (rotation.1.work=oldRotation.work &&
    rotation.1.registry.next=oldRotation.registry.next &&
    rotation.1.tables.length=oldRotation.tables.length) "rotation tables counters"
  for (actual,expected) in rotation.1.tables.zip oldRotation.tables do
    check (actual.1.lo=expected.1.lo && actual.1.hi=expected.1.hi &&
      actual.1.period=expected.1.period && actual.2=expected.2) "rotation table value/order"
  let short:=Short.tables rotation.1.registry f runs
  let oldShort:=P1ShortKeys.buildRunTables oldRotation.registry f runs
  check (short.1.work=oldShort.work && short.1.registry.next=oldShort.registry.next &&
    short.1.tables.length=oldShort.tables.length) "short tables counters"
  for (actual,expected) in short.1.tables.zip oldShort.tables do
    check (actual.1.lo=expected.1.lo && actual.1.hi=expected.1.hi &&
      actual.1.period=expected.1.period && actual.2=expected.2) "short table value/order"
    for w in P1ShortKeys.words (Periodic.shift f actual.1.lo) actual.1.period do
      check (ExactKeys.lookup short.1.registry.tree w=
        ExactKeys.lookup oldShort.registry.tree w) "shared registry final exact key"
  check (rotation.2>0 && short.2>0) "missing actual construction counters"
  return runs.length

def main : IO Unit := do
  let begin←IO.monoMsNow
  let mut keys:=0
  let mut runs:=0
  for kind in List.range 4 do
    let f:=reader kind
    for q in List.range 6 do keys:=keys+(←checkIntern f q)
    for n in [0,3,8,17] do
      for Q in List.range 4 do runs:=runs+(←checkTables f n Q)
  let finish←IO.monoMsNow
  IO.println s!"actual key construction: intern fixtures=24, run-table fixtures=64, keys={keys}, runs={runs}, mismatches=0, elapsed={finish-begin} ms"

end REWB.PeriodicConstruction.Keys.Audit

def main : IO Unit := REWB.PeriodicConstruction.Keys.Audit.main
