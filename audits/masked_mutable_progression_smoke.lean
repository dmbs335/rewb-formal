import REWB.MaskedMutableProgressionCost

/-! Independent runtime checks for the actual persistent source AP index.
Reference queries scan the physical window. Such scans occur only here,
never in the indexed operations being audited. -/
open REWB
open REWB.MaskedMutableProgression

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def marked (mask : Array Bool) (p : Nat) : Bool := mask[p]?.getD false

private def bruteGrid (idx : Index) (mask : Array Bool) (start wanted : Nat) : Option Nat :=
  if idx.step=0 then none else
  ((List.range (idx.len+1)).find? fun t=>
    t<wanted && start+t*idx.step<idx.len && marked mask (idx.base+start+t*idx.step)).map
      (fun t=>idx.base+start+t*idx.step)

private def bruteAP (idx : Index) (mask : Array Bool) (q K s lo hi r : Nat) : Option Nat :=
  if q=0 || K=0 || idx.step != K*q then none else
  ((List.range idx.len).find? fun i=>
    let p:=idx.base+i
    let k:=(p-s)/q
    marked mask p && s≤p && (p-s)%q=0 && lo≤k && k≤hi && k%K=r).map (idx.base+·)

private structure Stats where
  builds : Nat := 0
  erases : Nat := 0
  members : Nat := 0
  grids : Nat := 0
  aps : Nat := 0
  maxGrid : Nat := 0
  maxAP : Nat := 0

private def checkState (idx : Index) (mask : Array Bool) (tag : String) (stats : Stats) : IO Stats := do
  let mut out:=stats
  for i in [:idx.len+3] do
    let p:=if i=idx.len+2 then 0 else idx.base+i
    let got:=member idx p
    let want:=idx.base≤p && p<idx.base+idx.len && marked mask p
    require (got.1==want) s!"member {tag} p={p} got={got.1} want={want}"
    require (got.2≤4*idx.levels+11) "member counter"
    out:={out with members:=out.members+1}
  for start in [:idx.len+2] do
    for wanted in [:idx.len+3] do
      let got:=grid idx start wanted
      let want:=bruteGrid idx mask start wanted
      require (got.value==want) s!"grid {tag} start={start} wanted={wanted} got={got.value} want={want}"
      require (got.work≤7*idx.levels+35) "grid counter"
      out:={out with grids:=out.grids+1,maxGrid:=max out.maxGrid got.work}
  for qK in #[(idx.step,1),(1,idx.step)] do
    let q:=qK.1
    let K:=qK.2
    for s in #[0,idx.base,idx.base+1] do
      for bounds in #[(0,idx.len+2),(1,idx.len+1),(2,1),(0,0)] do
        for r in #[0,1,K-1,K] do
          let got:=ap idx q K s bounds.1 bounds.2 r
          let want:=bruteAP idx mask q K s bounds.1 bounds.2 r
          require (got.value==want)
            s!"ap {tag} q={q} K={K} s={s} lo={bounds.1} hi={bounds.2} r={r} got={got.value} want={want}"
          require (got.work≤7*idx.levels+65) "AP counter"
          out:={out with aps:=out.aps+1,maxAP:=max out.maxAP got.work}
  require ((ap idx 0 1 0 0 9 0).value==none) "zero q guard"
  require ((ap idx 1 0 0 0 9 0).value==none) "zero modulus guard"
  require ((ap idx 1 (idx.step+1) 0 0 9 0).value==none) "mismatched step guard"
  pure out

private def checkCase (mask : Array Bool) (base len step : Nat) (stats : Stats) : IO Stats := do
  let built:=build mask base len step
  require (built.work≤len*(10*height len+14)+2*height len+10) "build counter"
  require (built.work≤40*(len+1)*((len+1).log2+1)) "closed build counter"
  require (built.index.levels==2*((len+1).log2+1)) "cached height"
  require (built.index.capacity≤4*(len+1)*(len+1)) "polynomial capacity"
  let original:=built.index
  let mut idx:=original
  let mut live:=mask
  let mut out:={stats with builds:=stats.builds+1}
  let tag:=s!"mask={mask} base={base} len={len} step={step}"
  out←checkState idx live tag out
  for p in #[base+len,0,base,base+len/2,base] do
    let next:=erase idx p
    require (next.work≤12*idx.levels+13) "erase counter"
    require (next.index.base==base && next.index.len==len && next.index.step==step &&
      next.index.levels==original.levels && next.index.capacity==original.capacity) "erase dimensions"
    idx:=next.index
    live:=live.setIfInBounds p false
    out:={out with erases:=out.erases+1}
    out←checkState idx live s!"{tag} after erase {p}" out
  -- Force use of the retained old tree after all updates; it must still
  -- describe the original source array, including positions since erased.
  out←checkState original mask s!"{tag} retained original" out
  pure out

private def populated : {h : Nat}→MaskedOrdered.Tree h→Nat
  | _,.empty => 0
  | _,.tip _ => 1
  | _,.node _ _ _ l r => 1+populated l+populated r

private def deep (step : Nat) : IO Unit := do
  let len:=4096
  let mask:=Array.replicate len true
  let built:=build mask 0 len step
  let old:=built.index
  let mut idx:=old
  let mut live:=mask
  let mut work:=0
  for i in [:len/2] do
    let next:=erase idx (2*i)
    require (next.work≤12*idx.levels+13) "deep erase counter"
    work:=work+next.work
    idx:=next.index
    live:=live.setIfInBounds (2*i) false
  require (old.tree.count==len && idx.tree.count==len/2) "deep persistent counts"
  for p in [:len] do
    require ((member idx p).1==(p%2==1)) "deep current membership"
    require ((member old p).1==true) "deep retained membership"
  let mut maxGrid:=0
  for start in #[0,1,2,1023,4095,4096] do
    for wanted in #[0,1,2,4096,1000000007] do
      let got:=grid idx start wanted
      require (got.value==bruteGrid idx live start wanted) "deep grid"
      require (got.work≤7*idx.levels+35) "deep grid counter"
      maxGrid:=max maxGrid got.work
  for qK in #[(step,1),(1,step)] do
    for s in #[0,1,2] do
      for r in #[0,1,qK.2-1,qK.2] do
        let got:=ap idx qK.1 qK.2 s 0 1000000007 r
        require (got.value==bruteAP idx live qK.1 qK.2 s 0 1000000007 r) "deep AP"
        require (got.work≤7*idx.levels+65) "deep AP counter"
  require (built.work≤40*(len+1)*((len+1).log2+1)) "deep build budget"
  IO.println s!"mutableDeep step={step} length={len} levels={old.levels} capacity={old.capacity} populated={populated old.tree} buildWork={built.work} eraseWork={work} maxGridWork={maxGrid} oldCount={old.tree.count} newCount={idx.tree.count}"

def main : IO Unit := do
  let mut stats : Stats:={}
  for size in [:6] do
    for bits in [:2^size] do
      let mask:=Array.ofFn (fun i : Fin size=>((bits/2^i.val)%2)==1)
      for base in #[0,2] do
        for len in #[size,size+2] do
          for step in #[1,2,3,size+5,1000000007] do
            stats←checkCase mask base len step stats
  stats←checkCase #[true] 1000000007 7 1000000007 stats
  IO.println s!"mutableBuilds={stats.builds} erases={stats.erases} memberQueries={stats.members} gridQueries={stats.grids} apQueries={stats.aps} maxGridWork={stats.maxGrid} maxAPWork={stats.maxAP} exactWitnesses=true persistence=true shortMasks=true largeSteps=true"
  deep 1
  deep 3
  deep 1000000007
