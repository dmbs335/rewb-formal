import REWB.LCEIndexArray
import REWB.LCSTable

/-! Optional executable regression for the exact rank/LCE/LCS index.
Run after `lake build REWB.LCEIndexArray`:
`lake env lean --run audits/lean_lce_index_smoke.lean`
The kernel theorems remain the correctness evidence; this exercises
the actual compiled array/trie/descent entry points and stack behavior. -/
open REWB REWB.LCEIndexArray

def bit (x : Nat) : Fin 2 := ⟨x%2,Nat.mod_lt x (by decide)⟩

def checkPair (w : Word (Fin 2)) (I : WordIndex) (i j : Nat) : IO Unit := do
  let expected:=LCSTable.lcp (w.drop i) (w.drop j)
  let got:=(lceWord I i j).1
  let measured:=LCEIndex.lceMeasured I.forward I.length i j
  if measured.length != got || measured.levels != w.length.log2+1 ||
      measured.countedWork > 13*(w.length.log2+1)+1 then
    throw (IO.userError s!"measured LCE mismatch n={w.length}, i={i}, j={j}")
  if got != expected then
    throw (IO.userError s!"LCE mismatch n={w.length}, i={i}, j={j}, got={got}, expected={expected}")
  let expectedSuffix:=LCSTable.lcp (w.take i).reverse (w.take j).reverse
  let gotSuffix:=(lcsWord I i j).1
  let measuredSuffix:=LCEIndex.lcsMeasured I.backward I.length i j
  if measuredSuffix.length != gotSuffix || measuredSuffix.levels != w.length.log2+1 ||
      measuredSuffix.countedWork > 13*(w.length.log2+1)+1 then
    throw (IO.userError s!"measured LCS mismatch n={w.length}, e={i}, k={j}")
  if gotSuffix != expectedSuffix then
    throw (IO.userError s!"LCS mismatch n={w.length}, e={i}, k={j}, got={gotSuffix}, expected={expectedSuffix}")

def main : IO Unit := do
  let mut words:=0
  let mut pairs:=0
  for n in List.range 7 do
    for mask in List.range (2^n) do
      let w:=(List.range n).map (fun i=>bit (mask/2^i))
      let idx:=prepareWord w (bit 0)
      for i in List.range (n+1) do
        for j in List.range (n+1) do
          checkPair w idx i j
          pairs:=pairs+1
      words:=words+1
  IO.println s!"exhaustive binary words={words}, endpoint pairs={pairs}, LCE and LCS checks passed"
  let n:=4096
  let w:=(List.range n).map (fun i=>bit ((i*i+17*i+23)/31))
  let idx:=prepareWord w (bit 0)
  for p in [(0,0),(0,1),(0,62),(27,1089),(n,n),(n-1,n-1),(n-1,n)] do
    checkPair w idx p.1 p.2
  IO.println s!"large word n={n}, forward rows={idx.forward.rows.size}, backward rows={idx.backward.rows.size}"
  IO.println s!"tracked preparation work={idx.forward.countedWork+idx.backward.countedWork}"
  IO.println s!"LCE(0,62)={lceWord idx 0 62}, LCS(n,n-62)={lcsWord idx n (n-62)}"
  IO.println s!"measured LCE(0,62)={repr (LCEIndex.lceMeasured idx.forward n 0 62)}"
