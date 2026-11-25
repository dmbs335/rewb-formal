import REWB.IndexedGrid

/-! Exercise the compiled shared rank indexes, query counters and grid
coverage against direct substring/extension computations. -/
open REWB REWB.Periodic REWB.IndexedGrid

def bit (x : Nat) : Fin 2 := ⟨x%2,Nat.mod_lt x (by decide)⟩

def direct (f : Nat→Fin 2) (n s : Nat) : List Strip :=
  (GridCoverage.probes n s).filterMap fun (i,j) =>
    if i<j ∧ j≤n then
      let lo:=GridCoverage.regionLeft f (j-i) i
      let hi:=GridCoverage.regionEnd f n (j-i) i
      if i<hi then some ⟨lo,hi,j-i⟩ else none
    else none

def checkWord (w : Word (Fin 2)) (s : Nat) : IO Nat := do
  let a:=w.toArray
  let f:=fun i=>a[i]?.getD (bit 0)
  let n:=w.length
  let r:=generate f n s
  if r.strips != direct f n s then
    throw (IO.userError s!"strip mismatch n={n}, stride={s}")
  let count:=(n/s+1)*(n+1)
  if r.probes != count || r.strips.length>count ||
      r.queryWork>(26*(n.log2+1)+2)*count then
    throw (IO.userError s!"grid counter mismatch n={n}, stride={s}")
  let mut copies:=0
  for p in List.range (n+1) do
    for e in List.range (n+1) do
      for k in List.range (n+1) do
        if p<e && e≤k && k+(e-p)≤n && s≤e-p &&
            (w.drop p).take (e-p)==(w.drop k).take (e-p) then
          if !(r.strips.any fun R=>R.lo≤p && e≤R.hi && R.distance==k-p) then
            throw (IO.userError s!"uncovered copy n={n}, stride={s}, p={p}, e={e}, k={k}")
          copies:=copies+1
  return copies

def main : IO Unit := do
  let mut cases:=0
  let mut copies:=0
  for n in List.range 6 do
    for mask in List.range (2^n) do
      let w:=(List.range n).map (fun i=>bit (mask/2^i))
      for s in [1,2,3] do
        copies:=copies+(← checkWord w s)
        cases:=cases+1
  IO.println s!"grid cases={cases}; direct extensions and {copies} positive copy cover checks passed"
  let n:=1024
  let a:=((List.range n).map (fun i=>bit ((i*i+17*i+23)/31))).toArray
  let f:=fun i=>a[i]?.getD (bit 0)
  let r:=generate f n 32
  if r.strips != direct f n 32 then
    throw (IO.userError "large grid/direct mismatch")
  IO.println s!"n={n}, stride=32, probes={r.probes}, strips={r.strips.length}"
  IO.println s!"preparation={r.preparation}, measured query work={r.queryWork}"
