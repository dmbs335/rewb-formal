import REWB.ResidualStripScheduleRegression

open REWB REWB.IndexedGrid REWB.ResidualStripSchedule

private def require (ok : Bool) (msg : String) : IO Unit :=
  unless ok do throw (IO.userError msg)

/-- Audit only: scan characters separately for every displacement. -/
private def referenceStrips (text : Array (Fin 2)) : Array Strip := Id.run do
  let n:=text.size
  let mut out:=#[]
  for d in [1:n+1] do
    let mut i:=0
    while i+d<n do
      if text[i]! = text[i+d]! then
        let lo:=i
        i:=i+1
        while i+d<n && text[i]! = text[i+d]! do
          i:=i+1
        out:=out.push ⟨lo,i,d⟩
      else
        i:=i+1
  return out

/-- Audit only: test the complete global cut grid, then compare with the
actual per-strip arithmetic ranges. -/
private def referenceJobs (n D L : Nat) (Rs : Array Strip) : Array Job := Id.run do
  let mut out:=#[]
  for R in Rs do
    if R.hi-R.lo≤R.distance then
      out:=out.push (direct R)
    else
      for a in [0:n/D+1] do
        let left:=max R.lo (a*D-R.distance)
        let right:=min R.hi (a*D)
        if left<right && L≤right-left then
          out:=out.push ⟨R,some a,left,right⟩
  return out

private def sameItems [BEq α] (xs : List α) (ys : Array α) : Bool :=
  xs.length==ys.size && xs.all (fun x=>ys.contains x) && ys.all (fun y=>xs.contains y)

private def equalSlice (text : Array (Fin 2)) (p e k : Nat) : Bool :=
  text.extract p e == text.extract k (k+(e-p))

structure Stats where
  texts : Nat := 0
  schedules : Nat := 0
  strips : Nat := 0
  jobs : Nat := 0
  copies : Nat := 0
  explicitCuts : Nat := 0
  maxJobs : Nat := 0
  maxWork : Nat := 0

private def check (text : Array (Fin 2)) (reference : Array Strip) (s L D : Nat)
    (exhaustive : Bool) (stats : Stats) : IO Stats := do
  let n:=text.size
  let result:=prepare (ArrayText.read text 0) n s L D
  let wanted:=reference.filter (fun R=>L≤R.hi-R.lo)
  let jobs:=referenceJobs n D L wanted
  require (sameItems result.strips.strips wanted) s!"strip mismatch n={n} s={s} L={L} D={D}"
  require (result.strips.count==wanted.size) "cached strip count"
  require (sameItems result.batch.jobs jobs) s!"job mismatch n={n} s={s} L={L} D={D}"
  require (result.batch.queries==jobs.size) "cached query count"
  require (result.strips.count≤n*n/L) "long-strip packing"
  require (result.batch.queries≤2*n*n/D+3*(n*n/L)) "query packing"
  require (result.work≤scheduleBudget 2 n s L D) "whole preparation work"
  require (result.batch.work≤13*(2*n*n/D)+38*(n*n/L)+1) "cut construction work"
  for W in result.batch.jobs do
    require (W.left<W.right && W.right+W.distance≤n && W.right≤W.left+W.distance) "bad window bounds"
    require (L≤W.right-W.left && equalSlice text W.left W.right (W.left+W.distance)) "bad window equality"
  let mut out:={stats with
    schedules:=stats.schedules+1
    strips:=stats.strips+wanted.size
    jobs:=stats.jobs+jobs.size
    maxJobs:=max stats.maxJobs jobs.size
    maxWork:=max stats.maxWork result.work}
  if exhaustive then
    for p in [0:n+1] do
      for e in [p+1:n+1] do
        for k in [e:n+1] do
          if L≤e-p && k+(e-p)≤n && equalSlice text p e k then
            let distance:=k-p
            let separated:=reference.any (fun R=>R.distance==distance && R.lo≤p && e≤R.hi && R.hi-R.lo≤distance)
            let covered:=result.batch.jobs.any (fun W=>W.distance==distance && W.left≤p && e≤W.right)
            if separated || e+D≤k then
              require covered s!"copy coverage n={n} s={s} L={L} D={D} p={p} e={e} k={k}"
              out:={out with copies:=out.copies+1}
            for a in [0:n/D+1] do
              if e≤a*D && a*D≤k then
                require covered s!"stored cut coverage n={n} D={D} p={p} e={e} k={k} a={a}"
                out:={out with explicitCuts:=out.explicitCuts+1}
  return out

def main : IO Unit := do
  let mut stats:Stats:={}
  for n in [0:7] do
    for code in [0:2^n] do
      let text:=Array.ofFn (n:=n) (fun i=>(⟨code/(2^i.val)%2,by omega⟩ : Fin 2))
      let reference:=referenceStrips text
      stats:={stats with texts:=stats.texts+1}
      for s in [1,2,3] do
        for L in [s,s+1,n+s+1] do
          for D in [1,2,n+2] do
            stats←check text reference s L D true stats
    IO.println s!"stripScheduleLength n={n} texts={stats.texts} schedules={stats.schedules} jobs={stats.jobs}"
  require (stats.copies>0 && stats.explicitCuts>0 && stats.jobs>0) "vacuous audit"
  IO.println s!"stripScheduleTotal texts={stats.texts} schedules={stats.schedules} strips={stats.strips} jobs={stats.jobs} copies={stats.copies} storedCuts={stats.explicitCuts} maxJobs={stats.maxJobs} maxWork={stats.maxWork} exactTriples=true"
  for (n,period,s,L,D) in [(1024,1,16,32,128),(513,3,17,33,1000)] do
    let text:=Array.ofFn (n:=n) (fun i=>(⟨(i.val%period)%2,by omega⟩ : Fin 2))
    let reference:=referenceStrips text
    let deep←check text reference s L D false {}
    let result:=prepare (ArrayText.read text 0) n s L D
    IO.println s!"stripScheduleDeep n={n} period={period} s={s} L={L} D={D} strips={deep.strips} jobs={deep.jobs} cutProbes={result.batch.probes} work={result.work} cachedCounts=true"
