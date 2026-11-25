import REWB.RankIndexRuns
import REWB.ArrayText
import REWB.RunDedup

/-! Optional executable sampled-run and divisor-selector regression.
Run after `lake build REWB.RankIndexRuns`:
`lake env lean --run audits/lean_run_index_smoke.lean`
The independent exhaustive run enumerator is used only on tiny words. -/
open REWB REWB.Periodic

def bit (x : Nat) : Fin 2 := ⟨x%2,Nat.mod_lt x (by decide)⟩

def main : IO Unit := do
  let mut words:=0
  let mut schedules:=0
  for n in List.range 7 do
    for mask in List.range (2^n) do
      let w:=(List.range n).map (fun i=>bit (mask/2^i))
      let text:=w.toArray
      let f:=ArrayText.read text (bit 0)
      let reference:=RunExtension.enumerate f n
      for s0 in List.range (n+1) do
        let s:=s0+1
        let got:=RankIndexRuns.generate f n s
        let dedup:=RunDedup.run n got.runs
        if dedup.runs.length != dedup.runs.eraseDups.length then
          throw (IO.userError s!"duplicate run retained n={n}, mask={mask}, stride={s}")
        if dedup.work > (26*((n+1).log2+1)+5)*got.runs.length then
          throw (IO.userError s!"dedup counter bound failed n={n}, stride={s}")
        for R in got.runs do
          if !(reference.contains R) then
            throw (IO.userError s!"unsound run n={n}, mask={mask}, stride={s}, run={repr R}")
          if !(dedup.runs.contains R) then
            throw (IO.userError s!"dedup lost run n={n}, mask={mask}, stride={s}, run={repr R}")
        for R in dedup.runs do
          if !(got.runs.contains R) then
            throw (IO.userError s!"dedup introduced run n={n}, mask={mask}, stride={s}, run={repr R}")
        for R in reference do
          if s≤R.hi-R.lo-R.period && !(got.runs.contains R) then
            throw (IO.userError s!"missing run n={n}, mask={mask}, stride={s}, run={repr R}")
        if s==1 && dedup.runs.length != reference.length then
          throw (IO.userError s!"complete deduplicated run set differs from reference n={n}, mask={mask}")
        let H:=n.log2+1
        let A:=n/s+1
        if got.queryWork > A*((26*H+2)*(n+1)) || got.periodWork > A*((n*H)*(13*H+6)) then
          throw (IO.userError s!"counter bound failed n={n}, stride={s}")
        schedules:=schedules+1
      words:=words+1
  IO.println s!"exhaustive binary words={words}, sampled schedules={schedules}, soundness/coverage/dedup/reference/counter checks passed"
  let n:=12
  let f:=fun i=>bit i
  let idx:=LCEIndex.prepare f n
  let ds:=(RankIndexDivisors.buckets n).1
  let selected:=RankIndexPeriod.fromStrip idx ds n 0 8 4
  if selected.1 != (⟨0,12,2⟩ : RunGeometry.Bounds) then
    throw (IO.userError s!"least-period selector failed: {repr selected.1}")
  IO.println s!"displacement=4, selected run={repr selected.1}, selector work={selected.2}"
  let largeN:=256
  let generated:=RankIndexRuns.generate (fun _=>bit 0) largeN 8
  let dedup:=RunDedup.run largeN generated.runs
  if !(generated.runs.contains ⟨0,largeN,1⟩) then
    throw (IO.userError "large unary run missing")
  IO.println s!"unary n={largeN}, stride=8, probes={generated.probes}, raw runs={generated.runs.length}"
  IO.println s!"queryWork={generated.queryWork}, periodWork={generated.periodWork}, preparation={generated.preparation}, divisorWork={generated.divisorWork}"
  if dedup.runs != [⟨0,largeN,1⟩] then
    throw (IO.userError s!"large unary dedup mismatch: {repr dedup.runs}")
  if dedup.work > (26*((largeN+1).log2+1)+5)*generated.runs.length then
    throw (IO.userError "large unary dedup counter bound failed")
  IO.println s!"deduplicated runs={dedup.runs.length}, dedup work={dedup.work}"
