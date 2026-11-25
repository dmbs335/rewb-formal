import REWB.MaskedSuffixClassRegression

/-! Independent executable references. Text slicing, leaf enumeration,
and ordinary path walks below belong only to this bounded audit. -/
open REWB.MaskedSuffixClass
open REWB.BoundaryTrie (Tree)

def reference (text : List (Fin σ)) (p H : Nat) : Option (List Nat) :=
  if p+H≤text.length then
    some ((List.range (text.length+1)).filter fun k=>
      decide (k+H≤text.length) && ((text.drop k).take H==(text.drop p).take H))
  else none

def path (p : Nat) : Tree n Nat→Nat→Option (List (Nat×Nat))
  | .empty,_ => none
  | .leaf a,base => if a.start=p then some [(base,a.length)] else none
  | .node _ d l r,base =>
    let tail:=match path p r (base+1+REWB.MaskedOrdered.Owner.slots l) with
      | some xs=>some xs
      | none=>path p l (base+1)
    tail.map ((base,d)::·)

def checkText (text : Array (Fin 2)) : IO (Nat×Nat×Nat) := do
  let idx:=prepare text 0
  unless idx.owner.nodes.size+1==2*(text.size+1) do
    throw (IO.userError "owner snapshot allocation")
  unless idx.addresses.cells.size==idx.owner.nodes.size do
    throw (IO.userError "locator/snapshot preorder mismatch")
  unless idx.work≤budget 2 text.size do throw (IO.userError "total build budget")
  unless idx.work≤(32*(2+2)+830)*(text.size+1)*((text.size+1).log2+1)^2 do
    throw (IO.userError "closed total build bound")
  let mut queries:=0
  let mut maxWork:=0
  let mut interior:=0
  for p in (List.ofFn id : List (Fin (text.size+1))) do
    let some trace:=path p.val idx.suffix.trie.tree 0 | throw (IO.userError "missing suffix path")
    for H in List.range (text.size+3) do
      let out:=query idx p H
      let actual:=out.value.map (fun v=>v.record.state.tree.entries)
      let expected:=reference text.toList p.val H
      unless actual==expected do
        throw (IO.userError s!"class mismatch text={text.toList} p={p.val} H={H} actual={actual} expected={expected}")
      let first:=trace.find? (fun a=>decide (H≤a.2))
      unless out.value.map (fun v=>v.node)==first.map Prod.fst do
        throw (IO.userError "first-depth preorder ID mismatch")
      unless out.work≤6*idx.levels+9 && out.work≤6*((text.size+1).log2+1)+15 do
        throw (IO.userError "query counter")
      if let some r:=out.value then
        unless r.record.depth≥H do throw (IO.userError "record below cutoff")
        if H<r.record.depth && H>0 then interior:=interior+1
      queries:=queries+1
      maxWork:=max maxWork out.work
  pure (queries,maxWork,interior)

def deep (n period : Nat) : IO Unit := do
  let text : Array (Fin 2):=Array.ofFn (fun i : Fin n=>⟨(i.val%period)%2,by omega⟩)
  let idx:=prepare text 0
  unless idx.addresses.cells.size+1==2*(n+1) do throw (IO.userError "deep addresses")
  unless idx.work≤budget 2 n do throw (IO.userError "deep build work")
  let mut tested:=0
  let mut maxWork:=0
  for source in [0,1,2,n/3,n/2,n-1,n] do
    if hp : source<text.size+1 then
      let p : Fin (text.size+1):=⟨source,hp⟩
      for H in [0,1,2,3,7,16,n/3,n/2,n-source,n-source+1,n+1] do
        let out:=query idx p H
        unless out.value.map (fun r=>r.record.state.tree.entries)==reference text.toList source H do
          throw (IO.userError s!"deep class n={n} period={period} p={source} H={H}")
        unless out.work≤6*idx.levels+9 do throw (IO.userError "deep query work")
        tested:=tested+1
        maxWork:=max maxWork out.work
  IO.println s!"suffixClassDeep n={n} period={period} nodes={idx.owner.nodes.size} levels={idx.levels} work={idx.work} queries={tested} maxQueryWork={maxWork} savedOccurrences=true"

def main : IO Unit := do
  let mut texts:=0
  let mut queries:=0
  let mut maxWork:=0
  let mut interior:=0
  for n in List.range 9 do
    for code in List.range (2^n) do
      let text : Array (Fin 2):=Array.ofFn (fun i : Fin n=>⟨(code/2^i.val)%2,by omega⟩)
      let result←checkText text
      texts:=texts+1
      queries:=queries+result.1
      maxWork:=max maxWork result.2.1
      interior:=interior+result.2.2
  let idx:=prepare Regression.partialText 0
  let a:=query idx 0 1
  let b:=query idx 0 3
  unless a.value.map (fun out=>(out.node,out.record.depth,out.record.state.tree.entries))==
      b.value.map (fun out=>(out.node,out.record.depth,out.record.state.tree.entries)) do
    throw (IO.userError "compressed edge changed retained class")
  unless a.value.map (fun out=>(out.record.depth,out.record.state.tree.entries))==some (3,[0,3]) do
    throw (IO.userError "strict compressed edge witness")
  IO.println s!"suffixClasses texts={texts} queries={queries} interiorCuts={interior} maxQueryWork={maxWork} firstThresholdIDs=true epsilon=true emptySuffix=true invalidCutoffs=true"
  (←IO.getStdout).flush
  deep 1024 1
  deep 512 3
