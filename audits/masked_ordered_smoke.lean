import REWB.MaskedOrderedRegression
open REWB.MaskedOrdered
open REWB.MaskedEventBudget (MergeTree size lightVolume edges)

#print axioms Tree.insert_mem
#print axioms Tree.pred_correct
#print axioms Tree.succ_correct
#print axioms insert_reference
#print axioms insert_work
#print axioms merge_imports
#print axioms discarded_positions
#print axioms merge_new_edge
#print axioms execute_reference
#print axioms run_work_bound
#print axioms run_balance

-- Input construction and checks are test scaffolding, outside the
-- measured persistent ordered-set execution.
def balanced : Nat→Nat→MergeTree
  | 0,lo => .leaf (17*lo)
  | d+1,lo => .node (balanced d lo) (balanced d (lo+2^d))

def main : IO Unit := do
  let depth:=12
  let h:=20
  let input:=balanced depth 0
  let result:=run h input
  let tree:=result.1.tree
  let log:=result.2
  let n:=2^depth
  let cap:=2^h
  if tree.count≠n || result.1.positions.length≠n then
    throw (IO.userError "wrong cached cardinality or maintained list")
  if tree.first≠some 0 || tree.last≠some (17*(n-1)) then
    throw (IO.userError "wrong cached extrema")
  if tree.entries≠(List.range n).map (17*·) then
    throw (IO.userError "wrong ordered membership")
  for i in [0:n] do
    if !(Tree.contains tree cap (17*i)).1 then
      throw (IO.userError "missing sparse position")
    if (Tree.contains tree cap (17*i+1)).1 then
      throw (IO.userError "spurious sparse position")
  if (Tree.pred tree cap 17001).1≠some 17000 ||
      (Tree.succ tree cap 17001).1≠some 17017 then
    throw (IO.userError "wrong interior strict neighbor")
  if (Tree.pred tree cap 0).1.isSome || (Tree.succ tree cap cap).1.isSome then
    throw (IO.userError "wrong outside neighbor")
  if log.imports≠n*depth/2 || log.imports≠lightVolume input then
    throw (IO.userError "light-volume counter differs from actual imports")
  if log.freshCount≠log.fresh.length || log.retiredCount≠log.retired.length then
    throw (IO.userError "event count cache disagrees with actual records")
  if log.fresh.length≠n-1+log.retired.length then
    throw (IO.userError "adjacency generations are not conserved")
  if log.work>h+1+40*n*(n.log2+1)*(h+1) then
    throw (IO.userError "measured work exceeds the proved bound")
  let old:=Regression.second
  let changed:=insert old.tree 16 8
  let duplicate:=insert old.tree 16 4
  if old.tree.entries≠[4,12] || changed.tree.entries≠[4,8,12] ||
      duplicate.tree.entries≠[4,12] || duplicate.fresh≠[] || duplicate.retired≠[] then
    throw (IO.userError "persistent versions or duplicate no-op changed")
  let sparse:=insert (Tree.empty : Tree 40) (2^40) 1234567
  if sparse.tree.count≠1 || sparse.tree.first≠some 1234567 || sparse.work>28*40+18 then
    throw (IO.userError "sparse empty initialization expanded the universe")
  IO.println s!"positions={n} capacity={cap} height={h} imports={log.imports} fresh={log.freshCount} retired={log.retiredCount} work={log.work} sparse40Work={sparse.work}"
