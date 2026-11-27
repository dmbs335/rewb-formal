import REWB.MaskedClusterDescriptorRegression

/-! Descriptor runtime audit. Reference leaders test every earlier
occurrence directly; reference components are sliced from independently
updated sorted lists. Only this audit performs such scans. -/
open REWB REWB.MaskedClusterLeaders REWB.MaskedClusterDescriptor

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def leaders (xs : List Nat) (length : Nat) : List Nat :=
  xs.filter (fun p=>xs.all (fun q=>q≥p || length<2*(p-q)))

private def reference (xs ls : List Nat) (first : Nat) : Option Descriptor :=
  if !ls.contains first then none else
    let next:=ls.find? (first<·)
    let members:=xs.filter (fun p=>first≤p && (next.map (fun q=>decide (p<q))).getD true)
    match members.getLast? with
    | none => none
    | some last =>
      let second:=members[1]?.getD first
      let q:=if first<last then second-first else 1
      let previous:=if first<last then members.reverse[1]? else none
      let following:=next.bind (fun p=>xs.find? (p<·))
      some ⟨first,last,q,(last-first)/q,next,previous,following⟩

private def owner (xs ls : List Nat) (p : Nat) : Option Nat :=
  if xs.contains p then (ls.filter (·≤p)).getLast? else none

private def refInsert (xs : List Nat) (p : Nat) : List Nat :=
  if xs.contains p then xs else (p::xs).mergeSort (·≤·)

private structure Stats where
  traces : Nat := 0
  states : Nat := 0
  queries : Nat := 0
  maxLocate : Nat := 0
  maxLeader : Nat := 0
  maxDescribe : Nat := 0

private def check {h : Nat} (capacity bound : Nat) (out : Execution h) (xs : List Nat)
    (stats : Stats) : IO Stats := do
  let ls:=leaders xs out.length
  require (out.state.occurrences.entries==xs) "occurrence reference"
  require (out.state.leaders.entries==ls) "leader reference"
  let mut stats:={stats with states:=stats.states+1}
  for p in List.range (bound+2)++[capacity,capacity+1,1000000007] do
    let found:=locate out.state capacity p
    let first:=owner xs ls p
    require (found.1==first) s!"locate L={out.length} xs={xs} p={p} got={found.1} want={first}"
    require (found.2≤11*h+9) "locate work"
    let leader:=describeLeader out.state capacity p
    let leaderRef:=reference xs ls p
    require (leader.1==leaderRef)
      s!"describeLeader L={out.length} xs={xs} p={p} got={repr leader.1} want={repr leaderRef}"
    require (leader.2≤39*h+39) "leader work"
    let got:=describe out.state capacity p
    let want:=first.bind (reference xs ls)
    require (got.1==want) s!"describe L={out.length} xs={xs} p={p} got={repr got.1} want={repr want}"
    require (got.2≤50*h+50) "describe work"
    stats:={stats with
      queries:=stats.queries+3
      maxLocate:=max stats.maxLocate found.2
      maxLeader:=max stats.maxLeader leader.2
      maxDescribe:=max stats.maxDescribe got.2}
  pure stats

private def trace (h capacity bound initialLength : Nat) (ops : List Operation) (stats : Stats) : IO Stats := do
  let mut out:=initial h initialLength
  let mut xs : List Nat:=[]
  let mut length:=initialLength
  let mut stats:={stats with traces:=stats.traces+1}
  stats←check capacity bound out xs stats
  for op in ops do
    match op with
    | .insert p => if p<capacity then xs:=refInsert xs p
    | .lower fresh => if fresh≤length then length:=fresh
    out:=step capacity op out
    require (out.length==length) "retained length"
    stats←check capacity bound out xs stats
  let exact:=execute h initialLength ops
  require (exact.state.occurrences.entries==out.state.occurrences.entries &&
    exact.state.leaders.entries==out.state.leaders.entries && exact.work==out.work) "execute path"
  require (out.work≤h+1+(305*h+416)*ops.length) "trace bound"
  pure stats

private def deep : IO Unit := do
  let h:=20
  let capacity:=2^h
  let xs:=(List.range 1024).map (2*·)
  let order:=(xs.filter (fun p=>p%4=0))++(xs.filter (fun p=>p%4=2))
  let before:=execute h 4096 (order.map Operation.insert)
  let after:=step capacity (.lower 3) before
  let wanted : Descriptor:=⟨0,2046,2,1023,none,some 2044,none⟩
  require ((describe before.state capacity 1024).1==some wanted) "deep dense descriptor"
  let mut maxWork:=0
  for p in xs do
    let next:=if p<2046 then some (p+2) else none
    let following:=if p<2044 then some (p+4) else none
    let singleton : Descriptor:=⟨p,p,1,0,next,none,following⟩
    let got:=describe after.state capacity p
    require (got.1==some singleton) "deep split descriptor"
    require (got.2≤50*h+50) "deep descriptor counter"
    require ((locate after.state capacity p).1==some p) "deep split locator"
    require ((describe before.state capacity p).1==some wanted) "deep retained descriptor"
    maxWork:=max maxWork got.2
  require ((locate after.state capacity capacity).1==none) "deep capacity guard"
  IO.println s!"descriptorDeep occurrences={xs.length} height={h} densePeriod=2 denseRepetitions=1023 splitLeaders={after.state.leaders.count} popped={after.popped} maxDescribeWork={maxWork} persistence=true"

def main : IO Unit := do
  let mut stats : Stats:={}
  for bits in [:256] do
    let xs:=(List.range 8).filter (fun p=>(bits/2^p)%2==1)
    let orders:=[xs,xs.reverse,(xs.filter (fun p=>p%2=0))++(xs.filter (fun p=>p%2=1))]
    for order in orders do
      let ops:=order.map Operation.insert++[.insert 0,.insert 32,.lower 8,.lower 4,.lower 3,
        .insert 3,.lower 1,.lower 0,.lower 7]
      stats←trace 5 32 9 16 ops stats
  stats←trace 6 64 64 16
    ([40,0,63,12,2,50,21,4,10,20,22].map Operation.insert++
      [.lower 8,.lower 4,.lower 3,.lower 2,.lower 1,.lower 0,.insert 64,.insert 1000000007]) stats
  stats←trace 4 16 12 4 ([6,2,0,4].map Operation.insert++[.lower 3,.lower 0]) stats
  IO.println s!"descriptorTraces={stats.traces} states={stats.states} queries={stats.queries} maxLocateWork={stats.maxLocate} maxLeaderWork={stats.maxLeader} maxDescribeWork={stats.maxDescribe} allFields=true absentEndpoints=true thresholdSplits=true"
  deep
