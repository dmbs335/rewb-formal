import REWB.MaskedRunDiscoveryRegression
open REWB.MaskedRunDiscovery REWB.BoundaryTrie

#print axioms dense_least
#print axioms discover_dense
#print axioms discover_work
#print axioms completed_class_generated
#print axioms prepareSuffixes_complete
#print axioms discover_locus
#print axioms prepareSuffixes_work

-- This test-only path finder is not part of the discovery work counter.
def findPath {n : Nat} (start : Nat) : Tree n Nat → Option (List Bool)
  | .empty => none
  | .leaf a => if a.start=start then some [] else none
  | .node _ _ l r => match findPath start l with
    | some path => some (false::path)
    | none => (findPath start r).map (true::·)

def text : Array (Fin 2) := Array.ofFn (fun i : Fin 512 => Regression.alternating i.val)

def main : IO Unit := do
  let idx:=prepareSuffixes text 0
  let some path:=findPath 18 idx.trie.tree | throw (IO.userError "missing terminal path")
  let some cls:=Tree.locate 8 idx.trie.tree path | throw (IO.userError "missing prefix locus")
  let clsPositions:=(positions cls).mergeSort
  let expected:=(List.range 253).map (2*·)
  if clsPositions≠expected then throw (IO.userError "locus is not the complete occurrence class")
  let r:=idx.discover 18 20 8
  let some run:=r.1 | throw (IO.userError "dense discovery returned none")
  if run≠⟨0,512,2⟩ then throw (IO.userError s!"wrong discovered run {repr run}")
  let skip:=discoverClass idx.trie.prepared.ranks idx.backward 512 18 20 8 (some 8)
  if skip.1.isSome || skip.2≠2 then throw (IO.userError "equal-depth refinement was queried")
  let invalid:=idx.discover 20 18 8
  if invalid.1.isSome then throw (IO.userError "invalid ordered pair was accepted")
  IO.println s!"n={text.size} suffixes={idx.trie.prepared.keys.size} prepWork={idx.work} classSize={clsPositions.length} run={repr run} discoveryWork={r.2} equalDepthWork={skip.2}"
