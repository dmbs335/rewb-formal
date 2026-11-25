import REWB.ShortOuterBandRegression

/-! Independent direct-copy/gap/suffix scans are confined to this audit.
The actual path uses exact IDs, physical suffix bits and timestamp rows. -/
open REWB
open REWB.ShortOuter
open REWB.ShortOuter.Band

def automata : Array (DFA (Fin 2)) := #[
  Regression.any,Regression.eps,Regression.nonempty,Regression.lastOne,
  ⟨2,Regression.zero,fun q _=>⟨1-q.val,by omega⟩,fun q=>decide (q.val=0)⟩,
  ⟨1,⟨0,by decide⟩,fun _ _=>⟨0,by decide⟩,fun _=>false⟩]

def textOf (n code : Nat) : Array (Fin 2) :=
  (List.range n |>.map (fun i=>if Nat.testBit code i then Regression.one else Regression.zero)).toArray

def reference (G H : DFA (Fin 2)) (text : Array (Fin 2)) (limit p len : Nat) : Bool :=
  decide (len<limit ∧ p+len≤text.size) &&
  (List.range (text.size+1)).any (fun k=>
    decide (p+len≤k ∧ k+len≤text.size) &&
    decide (Spec.slice text.toList p (p+len)=Spec.slice text.toList k (k+len)) &&
    G.final (G.run G.initial (Spec.slice text.toList (p+len) k)) &&
    H.final (H.run H.initial (Spec.slice text.toList (k+len) text.size)))

def check (G H : DFA (Fin 2)) (text : Array (Fin 2)) (limit : Nat) : IO Nat := do
  let out:=build G H text Regression.zero limit
  let width:=min limit (text.size+1)
  unless out.bits.size==(text.size+1)*width && out.keys.ranks.size==(text.size+1)*width &&
      out.keys.registry.next≤(text.size+1)*width do
    throw <| IO.userError "short band allocation mismatch"
  unless out.touches≤2*(text.size+1)*width &&
      out.work≤budget 2 G.stateCount H.stateCount text.size width do
    throw <| IO.userError "short band work mismatch"
  let mut count:=0
  for p in List.range (text.size+3) do
    for len in List.range (width+3) do
      let got:=query out p len
      let expected:=reference G H text limit p len
      unless got.1==expected && got.2==8 do
        throw <| IO.userError s!"short band mismatch n={text.size} text={text} limit={limit} p={p} len={len} got={got.1} expected={expected}"
      count:=count+1
  return count

def main : IO Unit := do
  let mut texts:=0
  let mut builds:=0
  let mut queries:=0
  for n in List.range 7 do
    for code in List.range (2^n) do
      let text:=textOf n code
      texts:=texts+1
      for limit in List.range (n+4) do
        for i in List.range automata.size do
          let G:=automata[i]?.getD Regression.any
          let H:=automata[(3*i+code+n)%automata.size]?.getD Regression.any
          queries:=queries+(←check G H text limit)
          builds:=builds+1
  IO.println s!"short outer band texts={texts} builds={builds} queries={queries}"
  let n:=4096
  let limit:=32
  let text:=Array.replicate n Regression.zero
  let out:=build Regression.any Regression.any text Regression.zero limit
  unless out.touches≤2*(n+1)*limit && out.work≤budget 2 1 1 n limit do
    throw <| IO.userError "deep short band counter mismatch"
  for p in List.range (n+2) do
    for len in List.range (limit+1) do
      let got:=query out p len
      unless got.1==decide (len<limit ∧ p+2*len≤n) && got.2==8 do
        throw <| IO.userError s!"deep short band mismatch p={p} len={len}"
  IO.println s!"short outer band deep n={n} L={limit} keys={out.keys.registry.next} touches={out.touches} work={out.work}"
