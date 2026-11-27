import REWB.MaskedOrderedOwnerRegression
open REWB.MaskedOrdered.Owner
open REWB.RunGeometry (Bounds)

#print axioms location_owner_mem
#print axioms visit_at
#print axioms visit_at_event
#print axioms suffix_event_certified
#print axioms probe_sound
#print axioms collect_mem
#print axioms enumerateAuto_mem
#print axioms enumerateAuto_nodup
#print axioms enumerateAuto_work

-- Exhaustive reference enumeration is used only in this test harness.
def word (σ : Nat) (hσ : 0<σ) (n code : Nat) : Array (Fin σ) :=
  Array.ofFn (fun i : Fin n=>⟨(code/σ^i.val)%σ,Nat.mod_lt _ hσ⟩)

def sameRuns (xs ys : List Bounds) : Bool :=
  xs.length==ys.length && xs.all (fun R=>ys.contains R)

def checkWord {σ : Nat} (text : Array (Fin σ)) (fallback : Fin σ) : IO Unit := do
  let result:=enumerateAuto text fallback
  let expected:=(REWB.RunExtension.enumerate (REWB.ArrayText.read text fallback) text.size).filter
    (fun R=>3*R.period≤R.hi-R.lo)
  if !sameRuns result.runs expected then
    throw (IO.userError s!"enumeration mismatch text={repr text.toList} got={repr result.runs} expected={repr expected}")
  if !(decide result.runs.Nodup) then
    throw (IO.userError "duplicate run survived exact registry")
  let h:=(text.size+1).log2+1
  if result.work>preparationBudget σ text.size+executionBudget h text.size+h+2 then
    throw (IO.userError "full measured cost exceeds proved explicit budget")
  if result.nodeCount>2*(text.size+1) ||
      result.eventCount>2*((text.size+1)*(text.size+1).log2) then
    throw (IO.userError "node or generation count exceeds proved bound")

def checkPeriodic (n period : Nat) : IO Unit := do
  let text : Array (Fin 3):=Array.ofFn (fun i : Fin n=>⟨i.val%period%3,Nat.mod_lt _ (by decide)⟩)
  let result:=enumerateAuto text 0
  if result.runs≠[⟨0,n,period⟩] then
    throw (IO.userError s!"wrong periodic run n={n} period={period} runs={repr result.runs}")
  IO.println s!"periodic n={n} period={period} nodes={result.nodeCount} events={result.eventCount} work={result.work}"

def main : IO Unit := do
  let mut binary:=0
  for n in [0:10] do
    for code in [0:2^n] do
      checkWord (word 2 (by decide) n code) 0
      binary:=binary+1
  IO.println s!"exhaustive binary texts={binary} maxLength=9 passed"
  let mut ternary:=0
  for n in [0:7] do
    for code in [0:3^n] do
      checkWord (word 3 (by decide) n code) 0
      ternary:=ternary+1
  IO.println s!"exhaustive ternary texts={ternary} maxLength=6 passed"
  let text:=Regression.constantText
  let forward:=REWB.LCEIndex.prepare (REWB.ArrayText.read text 0) 6
  let backward:=REWB.LCEIndex.prepareReverse (REWB.ArrayText.read text 0) 6
  let stale:=probe forward backward 6 8 Regression.saved.nodes ⟨0,(0,2)⟩
  let current:=probe forward backward 6 8 Regression.saved.nodes ⟨0,(0,1)⟩
  if stale.1.isSome || current.1≠some ⟨0,6,1⟩ then
    throw (IO.userError "owner validation accepted a temporary adjacency or lost the true gap")
  if (Regression.saved.nodes[1]?.map Regression.project)≠some (4,0,some (2,3),[0,2]) then
    throw (IO.userError "earlier partial snapshot changed")
  let ownerText : Array (Fin 3):=#[0,1,2,0,1,2,0,1,2]
  let prepared:=REWB.MaskedRunDiscovery.prepareSuffixes ownerText 0
  let saved:=run 4 prepared.trie.tree
  for i in [0:saved.2.nodes.size] do
    let some rec:=saved.2.nodes[i]? | throw (IO.userError "missing node")
    let some owner:=saved.2.nodes[rec.owner]? | throw (IO.userError "invalid owner ID")
    if rec.owner>i || owner.owner≠rec.owner || owner.depth≠rec.depth then
      throw (IO.userError "owner metadata did not select the first equal-depth ancestor")
    if !(rec.state.tree.entries.all owner.state.tree.entries.contains) then
      throw (IO.userError "owner snapshot lost a descendant occurrence")
  IO.println s!"equal-depth snapshots={saved.2.nodes.size} staleWork={stale.2} trueGapWork={current.2} passed"
  checkPeriodic 1024 1
  checkPeriodic 2048 2
  checkPeriodic 1536 3
