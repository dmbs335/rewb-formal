import REWB.MaskedTraversalPeriodicCoverageRegression

/-! Cross-check original positive cuts against actual class owners and
the actual all-source periodic producer. Only this audit scans lengths
and positions; the coverage bridge itself adds no runtime operation. -/
namespace REWB.MaskedTraversalPeriodicCoverage.Audit
open REWB.Spec REWB.MaskedClusterDescriptor REWB.MaskedProgression

abbrev all : DFA (Fin 2) := ⟨1,0,fun _ _=>0,fun _=>true⟩
abbrev odd : DFA (Fin 2) := ⟨2,0,fun q _=>if q==0 then 1 else 0,fun q=>q==1⟩
abbrev eps : DFA (Fin 2) := ⟨2,0,fun _ _=>1,fun q=>q==0⟩

def accepted (A : DFA α) (w : Word α) : Bool := A.final (A.run A.initial w)
def check (b : Bool) (message : String) : IO Unit := unless b do throw (IO.userError message)
def binary (n code : Nat) : Array (Fin 2) :=
  Array.ofFn fun i : Fin n=>⟨(code/2^i.val)%2,Nat.mod_lt _ (by decide)⟩

structure Stats where
  cases : Nat := 0
  classes : Nat := 0
  positive : Nat := 0
  sameOwner : Nat := 0
  remaining : Nat := 0
  deriving Repr

def fixture (B C E : DFA (Fin 2)) (text : Array (Fin 2)) (salt : Nat) : IO Stats := do
  let n:=text.size
  let w:=text.toList
  let height:=(n+1).log2+1
  let capacity:=2^height
  let source:=Array.ofFn fun p : Fin (n+1)=>decide ((p.val+salt)%3≠1)
  let target:=Array.ofFn fun p : Fin (n+1)=>decide ((p.val+salt)%3≠2)
  let removed:=(List.range (n+1)).filter fun p=>decide ((p+salt)%7=3)
  let result:=MaskedPeriodic.Batch.solve B C E text 0 source target
  let runs:=(MaskedOrdered.Owner.enumerateAuto text 0).runs
  let mut stats:Stats:={cases:=1}
  for L in List.range (n+1) do
    if L>0 then
      for p in List.range (n+1) do
        if p+L≤n then
          let xs:=(List.range (n+1)).filter fun x=>decide (x+L≤n) &&
            (slice w x (x+L)==slice w p (p+L))
          let partition:=(MaskedClusterLeaders.execute height L
            (xs.reverse.map MaskedClusterLeaders.Operation.insert)).state
          let some first:=(locate partition capacity p).1 | throw (IO.userError "source absent from its actual class")
          let some d:=(describeLeader partition capacity first).1 | throw (IO.userError "source owner descriptor missing")
          stats:={stats with classes:=stats.classes+1}
          for j in xs do
            if MaskedCluster.Mutable.Batch.currentBit source removed p && readMask target j &&
                decide (p+L≤j ∧ j+L≤n) && accepted B (slice w p (p+L)) &&
                accepted C (slice w (p+L) j) && accepted E (slice w (j+L) n) then
              stats:={stats with positive:=stats.positive+1}
              let second:=(locate partition capacity j).1
              let same:=second==some first
              if same then
                check (d.repetitions>0 && 2*d.period≤L) "same owner failed dense geometry"
                check (runs.any fun R=>R.period==d.period && decide (R.lo≤p ∧ j+L≤R.hi) &&
                  decide ((j-p)%R.period=0)) "same-owner original pair absent from actual enumerated runs"
                check (readMask result.output.hits p) "same-owner original witness missed by actual periodic solver"
                stats:={stats with sameOwner:=stats.sameOwner+1}
              if !readMask result.output.hits p then
                check (!same) "unreported positive witness retained equal owners"
                stats:={stats with remaining:=stats.remaining+1}
  return stats

def plus (a b : Stats) : Stats :=
  ⟨a.cases+b.cases,a.classes+b.classes,a.positive+b.positive,a.sameOwner+b.sameOwner,a.remaining+b.remaining⟩

def run : IO Unit := do
  let begin←IO.monoMsNow
  let mut stats:Stats:={}
  for n in List.range 7 do
    for code in List.range (2^n) do
      stats:=plus stats (←fixture all all all (binary n code) code)
  IO.println s!"periodicCoverageBinary {repr stats}"
  (←IO.getStdout).flush
  for text in [#[0,1,0,1,0,1,0,1,0,1,0,1],#[0,0,1,0,0,1,0,0,1,0,0,1,0,0,1]] do
    stats:=plus stats (←fixture odd all all text 0)
    stats:=plus stats (←fixture all all eps text 1)
  stats:=plus stats (←fixture all all all (Array.replicate 48 0) 0)
  check (stats.sameOwner>0 && stats.remaining>0) "periodic/cross split branches missing"
  let finish←IO.monoMsNow
  IO.println s!"periodicCoverageComplete {repr stats} mismatches=0 elapsed={finish-begin}ms"

end REWB.MaskedTraversalPeriodicCoverage.Audit

def main : IO Unit := REWB.MaskedTraversalPeriodicCoverage.Audit.run
