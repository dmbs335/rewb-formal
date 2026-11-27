import REWB.MaskedClusterLeaderRegression

open REWB.MaskedClusterLeaders REWB.MaskedEventBudget

def checkStep (op : Operation) (out : Execution 4) (expected : List Nat) (length : Nat) :
    IO (Execution 4×List Nat×Nat) := do
  let next:=step 16 op out
  let xs:=match op with
    | .insert p=>if p<16 then (List.range 16).filter (fun q=>q==p || expected.contains q) else expected
    | .lower _=>expected
  let fresh:=match op with
    | .insert _=>length
    | .lower l=>min l length
  let leaders:=xs.filter fun p=>xs.all fun q=>decide (p≤q ∨ fresh<2*(p-q))
  unless next.length=fresh && next.state.occurrences.entries==xs && next.state.leaders.entries==leaders do
    throw (IO.userError s!"leader stream mismatch op={repr op} expected={leaders} actual={next.state.leaders.entries}")
  let pending:=REWB.MaskedThresholdQueue.entries next.state.queue
  for e in edges xs do
    for event in thresholds e do
      if event.level<fresh then
        unless pending.contains (REWB.MaskedThresholdEvents.pack event) do
          throw (IO.userError "future live threshold was lost")
  unless next.generated=next.popped+REWB.MaskedThresholdQueue.count next.state.queue &&
      next.generated≤4*next.insertions &&
      next.work≤5+(129*4+152)*next.steps+(44*4+66)*next.popped do
    throw (IO.userError "leader stream counter invariant failed")
  return (next,xs,fresh)

def operation (code : Nat) : Operation :=
  match code%8 with
  | 0=>.insert 0
  | 1=>.insert 2
  | 2=>.insert 4
  | 3=>.insert 6
  | 4=>.lower 5
  | 5=>.lower 3
  | 6=>.lower 20
  | _=>.insert 16

def main : IO Unit := do
  let mut streams:=0
  let mut checked:=0
  for n in [0:5] do
    for code in [0:8^n] do
      let mut out:=initial 4 12
      let mut expected:=[]
      let mut length:=12
      for i in [0:n] do
        let next←checkStep (operation (code/8^i)) out expected length
        out:=next.1
        expected:=next.2.1
        length:=next.2.2
        checked:=checked+1
      streams:=streams+1
  let extra : List Operation := [.insert 0,.insert 8,.lower 7,.insert 4,.lower 3,
    .insert 2,.insert 6,.lower 3,.lower 2,.lower 1,.insert 3,.insert 3,.lower 0]
  let mut out:=initial 4 16
  let mut expected:=[]
  let mut length:=16
  for op in extra do
    let next←checkStep op out expected length
    out:=next.1
    expected:=next.2.1
    length:=next.2.2
    checked:=checked+1
  let n:=4096
  let ops:=((List.range n).map fun i=>Operation.insert ((1597*i)%n))++
    ([4095,1023,255,63,15,3,1,0].map Operation.lower)
  let large:=execute 13 8192 ops
  unless large.state.occurrences.entries==List.range n && large.state.leaders.entries==List.range n &&
      large.popped=large.generated && REWB.MaskedThresholdQueue.count large.state.queue=0 &&
      large.work≤14+(305*13+416)*ops.length do
    throw (IO.userError "large inserted/shortened leader stream failed")
  IO.println s!"leader streams={streams+1}, checked steps={checked}; direct dense-component and future-record references passed"
  IO.println s!"large n={n}, operations={ops.length}, generated={large.generated}, popped={large.popped}, work={large.work}, final leaders={large.state.leaders.count}"
  IO.println "This maintains leaders and thresholds; suffix-trie query order, local-anchor repair and compiled-bank repair remain separate."
