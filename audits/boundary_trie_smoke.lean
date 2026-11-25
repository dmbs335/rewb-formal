import REWB.BoundaryTrieRegression
open REWB REWB.BoundaryTrie

def main : IO Unit := do
  let small := Regression.built
  let ordered := small.tree.leaves.map Key.record
  let expected : List (Terminal 2 2) :=
    [.source 5,.target 1 0 0,.target 1 1 0,.target 2 0 1,
      .source 4,.target 5 1 1,.source 3]
  unless ordered == expected do throw (IO.userError "sorted record sequence mismatch")
  unless small.tree.nodes == 13 && small.tree.depth == 0 do
    throw (IO.userError "small trie structure mismatch")
  let n := 2048
  let text := Array.replicate n (0 : Fin 2)
  let keys : List (Key text.size Nat) := (List.range (n+1)).map fun i =>
    if h : i≤text.size then ⟨0,i,by omega,i⟩ else ⟨0,0,by omega,i⟩
  let big := Build.run text 0 keys
  unless big.tree.nodes == 2*(n+1)-1 && big.prepared.keys.size == n+1 do
    throw (IO.userError "prefix chain lost keys or nodes")
  let first := Partition.keyAt big.prepared.keys ⟨0,0,by omega,0⟩ 0
  let last := Partition.keyAt big.prepared.keys ⟨0,0,by omega,0⟩ n
  unless first.length == 0 && last.length == n do
    throw (IO.userError "prefix sorting mismatch")
  IO.println s!"smallNodes={small.tree.nodes} emptyAndDuplicateRecords=true prefixKeys={big.prepared.keys.size} nodes={big.tree.nodes} representedCharacters={n*(n+1)/2} work={big.work}"
