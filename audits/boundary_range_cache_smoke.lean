import REWB.BoundaryRangeCacheRegression

/-! This audit supplies the pending all-start rows by independent slow
cut enumeration on the actual prepared reverse masks. That test-only
computation is not a production all-start solver or part of the cache
cost theorem. The complete cache and its far-right branch are compared
with separate original-coordinate cut enumeration. -/
open REWB REWB.Spec REWB.BoundaryRange
open REWB.OneUseRange.Border.Regression

namespace BoundaryCacheAudit

def accepts (d : DFA (Fin 2)) (w : Word (Fin 2)) : Bool := d.final (d.run d.initial w)

def masked (B C E : DFA (Fin 2)) (w : Word (Fin 2)) (mask : Nat→Bool) (i : Nat) : Bool :=
  (List.range (w.length+1)).any fun a=>
    decide (i≤a) && (List.range (w.length+1)).any fun j=>
      decide (a≤j) && mask j && (List.range (w.length+1)).any fun t=>
        decide (j≤t) && decide (slice w i a=slice w j t) &&
          accepts B (slice w i a) && accepts C (slice w a j) && accepts E (slice w t w.length)

def physical (A B C K D E : DFA (Fin 2)) (w : Word (Fin 2)) (left right : Nat)
    (inside : Nat→Nat→Nat→Bool) : Bool :=
  decide (left≤right ∧ right≤w.length) &&
    (List.range (right+1)).any fun i=>
      (List.range (right+1)).any fun a=>
        decide (i≤a) && (List.range (right+1)).any fun p=>
          decide (a≤p ∧ left≤p) && (List.range (right+1)).any fun j=>
            decide (p≤j) && inside a p j && (List.range (right+1)).any fun t=>
              decide (j≤t) && decide (slice w i a=slice w j t) &&
                accepts A (slice w 0 i) && accepts B (slice w i a) && accepts C (slice w a p) &&
                accepts K (slice w left p) && accepts D (slice w p j) && accepts E (slice w t right)

structure Machines (K : DFA (Fin 2)) where
  capture : DFA (Fin 2)
  gaps : Vector (DFA (Fin 2)) K.stateCount
  suffix : DFA (Fin 2)

def machines (A B C K D : DFA (Fin 2)) : Machines K :=
  ⟨Automata.reverse B,Vector.ofFn (fun k=>Automata.reverse (Automata.gap C K D C.initial k)),Automata.reverse A⟩

def rows (K : DFA (Fin 2)) (w : Word (Fin 2)) (requests : FarRight.Requests K w)
    (compiled : Machines K) : FarRight.Input K :=
  let reversed:=w.reverse
  Vector.ofFn fun q=>Vector.ofFn fun k=>Array.ofFn fun y : Fin (w.length+1)=>
    masked compiled.capture (compiled.gaps.get k) compiled.suffix reversed (FarRight.readMask requests q k) y.val

def words : Nat→List (Word (Fin 2))
  | 0=>[[]]
  | n+1=>(words n).flatMap fun w=>[0::w,1::w]

structure Counts where
  builds : Nat:=0
  masks : Nat:=0
  queries : Nat:=0
  accepted : Nat:=0
  farQueries : Nat:=0
  farAccepted : Nat:=0
  maxWork : Nat:=0

def Counts.add (a b : Counts) : Counts :=
  ⟨a.builds+b.builds,a.masks+b.masks,a.queries+b.queries,a.accepted+b.accepted,
    a.farQueries+b.farQueries,a.farAccepted+b.farAccepted,max a.maxWork b.maxWork⟩

def queryBudget (A B C K D E : DFA (Fin 2)) (coefficient n width : Nat) : Nat :=
  let copy:=coefficient*((n+1).log2+1)^2+NearIndex.rangeBudget A n+NearIndex.rangeBudget E n+8
  let physical:=copy+NearIndex.Border.gapBudget C K D n+3
  FarLeft.queryBudget C K E n+FarRight.queryBudget K n+NearIndex.threeBudget A B C K D E n width width+
    (width*(width*(physical+3)+4)+1)+17

def check (A B C K D E : DFA (Fin 2)) (w : Word (Fin 2)) (compiled : Machines K)
    (coefficient width : Nat) (hw : 0<width) : IO Counts := do
  let prepared:=Cache.prepare A B C K D E w 0 width hw
  let mut counts : Counts:={builds:=1}
  for slot in List.finRange (CacheGrid.count w.length width) do
    let block:=Table.get prepared.blocks slot
    for q in List.finRange K.stateCount do
      for k in List.finRange K.stateCount do
        for y in List.range (w.length+2) do
          let found:=FarRight.readMask block.requests q k y
          let reference:=decide (y≤w.length) && farMask K w block.upper q k (w.length-y)
          unless found=reference do throw (IO.userError "prepared mask mismatch")
          counts:={counts with masks:=counts.masks+1}
  let bits : Cache.Inputs K w.length width:=Vector.ofFn fun slot=>
    rows K w (Table.get prepared.blocks slot).requests compiled
  let idx:=Cache.assemble A B C K D E w prepared bits
  unless prepared.work≤Cache.prepareBudget A B C K D E w.length width do throw (IO.userError "cache prepare budget")
  unless idx.work≤Cache.buildBudget A B C K D E w.length width do throw (IO.userError "cache total budget")
  let bound:=queryBudget A B C K D E coefficient w.length width
  for left in List.range (w.length+2) do
    for right in List.range (w.length+2) do
      let found:=Cache.query idx left right
      let reference:=physical A B C K D E w left right (fun _ _ _=>true)
      unless found.1=reference do throw (IO.userError s!"boundary cache {w} width={width} [{left},{right}] {found.1} != {reference}")
      unless found.2≤bound do throw (IO.userError "cache query budget")
      counts:={counts with queries:=counts.queries+1,accepted:=counts.accepted+(if found.1 then 1 else 0),maxWork:=max counts.maxWork found.2}
      if valid : left≤right ∧ right≤w.length then
        let slot : Fin (CacheGrid.count w.length width):=⟨left/width,CacheGrid.slot_bound w.length width left hw (by omega)⟩
        let g:=CacheGrid.upper w.length width slot.val
        let far:=FarRight.query K (Table.get idx.right slot) left right
        let expected:=physical A B C K D E w left right (fun a p _=>decide (g≤p ∧ g<a))
        unless far.1=expected do throw (IO.userError s!"far-right original cuts {w} g={g} [{left},{right}]")
        unless far.2≤FarRight.queryBudget K w.length do throw (IO.userError "far-right query budget")
        counts:={counts with farQueries:=counts.farQueries+1,farAccepted:=counts.farAccepted+(if far.1 then 1 else 0)}
  return counts

/- `Cache.Regression.copiedMasks_ready` proves that copying the actual
prepared masks supplies correct all-start output rows for these all-word
automata. This special deep fixture does not stand in for constructing
general all-start output rows. -/
def deep (coefficient : Nat) : IO Unit := do
  let n:=32
  let width:=8
  let w : Word (Fin 2):=(List.range n).map fun k=>if k%2=0 then 0 else 1
  have hlen : w.length=n := by simp [w]
  let prepared:=Cache.prepare all all all all all all w 0 width (by decide)
  let bits : Cache.Inputs all w.length width:=Vector.ofFn fun slot=>
    Cache.Regression.copiedMasks (Table.get prepared.blocks slot).requests
  let idx:=Cache.assemble all all all all all all w prepared bits
  unless idx.work≤Cache.buildBudget all all all all all all w.length width do throw (IO.userError "deep build budget")
  let bound:=queryBudget all all all all all all coefficient w.length width
  let mut queries:=0
  let mut farQueries:=0
  let mut maximum:=0
  for left in List.range (n+2) do
    for right in List.range (n+2) do
      let out:=Cache.query idx left right
      let expected:=decide (left≤right ∧ right≤n)
      unless out.1=expected do throw (IO.userError "deep all-word cache semantics")
      unless out.2≤bound do throw (IO.userError "deep query budget")
      if valid : left≤right ∧ right≤n then
        let slot : Fin (CacheGrid.count w.length width):=⟨left/width,CacheGrid.slot_bound w.length width left (by decide) (by rw [hlen]; omega)⟩
        let g:=CacheGrid.upper w.length width slot.val
        let far:=FarRight.query all (Table.get idx.right slot) left right
        unless far.1=decide (g<right) do throw (IO.userError "deep far-right exact empty-cut criterion")
        unless far.2≤FarRight.queryBudget all w.length do throw (IO.userError "deep far-right query budget")
        farQueries:=farQueries+1
      queries:=queries+1
      maximum:=max maximum out.2
  IO.println s!"boundaryCacheDeep n={n} width={width} slots={prepared.slots} queries={queries} farQueries={farQueries} prepareWork={prepared.work} buildWork={idx.work} maxQueryWork={maximum} allEmptyCuts=true"

def main : IO Unit := do
  IO.println "boundaryCache pending rows use independent slow masked-cut enumeration"
  let patterns : List (DFA (Fin 2)×DFA (Fin 2)×DFA (Fin 2)×DFA (Fin 2)×DFA (Fin 2)×DFA (Fin 2)):=
    [(all,all,all,all,all,all),(epsilon,positive,all,all,all,epsilon),(all,all,all,reset,all,all)]
  let mut total : Counts:={}
  let mut number:=0
  for (A,B,C,K,D,E) in patterns do
    let compiled:=machines A B C K D
    let coefficient:=2*BoundaryBorder.Regular.fixedBudget A B E+521
    for n in List.range 3 do
      for w in words n do
        for width in [1,3] do
          if hw : 0<width then total:=total.add (←check A B C K D E w compiled coefficient width hw)
      IO.println s!"boundaryCacheSmall pattern={number} n={n} builds={total.builds} queries={total.queries}"
      (←IO.getStdout).flush
    number:=number+1
  IO.println "boundaryCacheTarget noninjective far-right and same-block copies"
  let resetMachines:=machines all positive all reset all
  let resetCoefficient:=2*BoundaryBorder.Regular.fixedBudget all positive all+521
  total:=total.add (←check all positive all reset all all [1,0,1,0] resetMachines resetCoefficient 1 (by decide))
  let borderMachines:=machines epsilon positive all all all
  let borderCoefficient:=2*BoundaryBorder.Regular.fixedBudget epsilon positive epsilon+521
  total:=total.add (←check epsilon positive all all all epsilon [0,1,0] borderMachines borderCoefficient 5 (by decide))
  IO.println s!"boundaryCacheTotal builds={total.builds} masks={total.masks} queries={total.queries} accepted={total.accepted} farQueries={total.farQueries} farAccepted={total.farAccepted} maxWork={total.maxWork}"
  unless total.farAccepted>0 do throw (IO.userError "missing positive far-right coverage")
  deep (2*BoundaryBorder.Regular.fixedBudget all all all+521)

end BoundaryCacheAudit

def main : IO Unit:=BoundaryCacheAudit.main
