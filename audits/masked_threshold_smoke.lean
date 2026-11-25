import REWB.MaskedThresholdRegression

open REWB.MaskedThresholdQueue
open REWB.MaskedThresholdEvents
open REWB.MaskedEventBudget (Threshold)

def sameEntries (xs ys : List (Entry Nat)) : Bool :=
  xs.length==ys.length && xs.all (fun e=>ys.contains e)

def queueOf (h : Nat) (keys : List Nat) : Tree Nat×Nat := Id.run do
  let mut q : Tree Nat:=.empty
  let mut work:=0
  for (key,id) in keys.zipIdx do
    let step:=insert h (2^h) 0 ⟨key,id⟩ q
    q:=step.1
    work:=work+step.2
  return (q,work)

def checkQueue (keys : List Nat) : IO Nat := do
  -- Entries have a unique payload, even when the threshold key repeats.
  let expected:=keys.zipIdx.map fun (key,id)=>({key:=key,value:=id} : Entry Nat)
  let built:=queueOf 3 keys
  unless sameEntries (entries built.1) expected && count built.1=keys.length do
    throw (IO.userError "queue insertion lost a duplicate-key record")
  let mut checks:=0
  for threshold in [0:10] do
    let out:=drain 3 threshold built.1
    unless sameEntries out.due (expected.filter (fun e=>decide (threshold≤e.key))) &&
        sameEntries (entries out.rest) (expected.filter (fun e=>decide (e.key<threshold))) do
      throw (IO.userError s!"threshold partition mismatch keys={keys} threshold={threshold}")
    unless decide ((out.due.map Entry.key).Pairwise (fun a b=>b≤a)) do
      throw (IO.userError "thresholds were not returned in descending order")
    unless out.popped=out.due.length && out.work≤42*(out.popped+1) do
      throw (IO.userError "threshold drain ledger exceeded proved output bound")
    let later:=drain 3 0 out.rest
    unless out.popped+later.popped=keys.length && count later.rest=0 do
      throw (IO.userError "a threshold was lost or replayed")
    checks:=checks+1
  return checks

def digitKeys (length code : Nat) : List Nat :=
  (List.range length).map fun i=>(code/4^i)%4

def main : IO Unit := do
  let mut checks:=0
  for n in [0:5] do
    for code in [0:4^n] do
      checks:=checks+(←checkQueue (digitKeys n code))
  let mut t : REWB.MaskedOrdered.Tree 5:=.empty
  let mut q : Queue:=.empty
  let mut generated:=0
  let mut work:=0
  for p in [0,16,8,4,12,2,6,10,14,2] do
    let out:=add 5 32 p t q
    t:=out.insertion.tree
    q:=out.queue
    generated:=generated+out.generated
    work:=work+out.work
  let mut popped:=0
  let mut live:=0
  for L in [32,16,8,4,2,1,0] do
    let old:=q
    let out:=shorten 6 L t 32 q
    for e in out.live do
      unless (check t 32 e.value).1 && decide (L≤e.key) do
        throw (IO.userError "stale threshold reached live repair output")
    let expectedLive:=(entries old).filter fun e=>decide (L≤e.key) && (check t 32 e.value).1
    unless out.live.length=expectedLive.length && out.live.all expectedLive.contains do
      throw (IO.userError "live threshold filter disagrees with explicit queue scan")
    q:=out.pending
    popped:=popped+out.popped
    live:=live+out.live.length
    work:=work+out.work
  unless generated=popped && count q=0 do
    throw (IO.userError "actual insertion/shortening conservation failed")
  let n:=20000
  let large:=queueOf 20 ((List.range n).map fun i=>(i*7919)%1048576)
  let out:=drain 20 0 large.1
  unless out.popped=n && count out.rest=0 && out.work≤212*(n+1) do
    throw (IO.userError "large tail-recursive queue drain failed")
  IO.println s!"threshold partitions={checks} duplicate-key and later-drain checks passed"
  IO.println s!"actual insertion generations={generated} consumed={popped} live={live} cancelled={popped-live} work={work}"
  IO.println s!"large queue records={n} height=20 insertWork={large.2} drainWork={out.work}"
  IO.println "This verifies queue generation/draining/validation; compressed-edge query order and cluster repairs remain separate."
