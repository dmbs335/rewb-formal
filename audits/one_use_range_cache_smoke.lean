import REWB.OneUseRangeCacheRegression

/-! Independent cut enumeration constructs the small test input rows.
This deliberately slow fixture is not an all-start implementation or
part of the claimed cache construction cost. -/
open REWB REWB.Spec REWB.OneUseRange REWB.OneUseRange.Border.Regression
open REWB.BoundaryRange REWB.BoundaryIndex

namespace OneUseCacheAudit

def accepts (d : DFA (Fin 2)) (w : Word (Fin 2)) : Bool := d.final (d.run d.initial w)

def masked (B C E : DFA (Fin 2)) (w : Word (Fin 2)) (i : Nat) : Bool :=
  (List.range (w.length+1)).any fun a=>
    decide (i≤a) && (List.range (w.length+1)).any fun j=>
      decide (a≤j) && (List.range (w.length+1)).any fun t=>
        decide (j≤t) && decide (slice w i a=slice w j t) &&
          accepts B (slice w i a) && accepts C (slice w a j) && accepts E (slice w t w.length)

def physical (A B C E : DFA (Fin 2)) (w : Word (Fin 2)) (left right : Nat) : Bool :=
  decide (left≤right ∧ right≤w.length) &&
    (List.range (right+1)).any fun i=>
      decide (left≤i) && (List.range (right+1)).any fun a=>
        decide (i≤a) && (List.range (right+1)).any fun j=>
          decide (a≤j) && (List.range (right+1)).any fun t=>
            decide (j≤t) && decide (slice w i a=slice w j t) &&
              accepts A (slice w left i) && accepts B (slice w i a) &&
              accepts C (slice w a j) && accepts E (slice w t right)

def rows (B C E : DFA (Fin 2)) (w : Word (Fin 2)) (grid : Nat) : FarBank.Input E :=
  Vector.ofFn fun c=>Array.ofFn fun i : Fin (grid+1)=>
    masked B C (FarSelection.variant E c) (w.take grid) i.val

def forward (B C E : DFA (Fin 2)) (w : Word (Fin 2)) (width : Nat) : Cache.Inputs E w.length width :=
  Vector.ofFn fun slot=>rows B C E w (Grid.position w.length width slot.val)

def backward (A B C : DFA (Fin 2)) (w : Word (Fin 2)) (width : Nat) :
    Cache.Inputs (Automata.reverse A) w.length width :=
  Vector.ofFn fun slot=>rows (Automata.reverse B) (Automata.reverse C) (Automata.reverse A)
    w.reverse (Grid.backward w.length width slot.val)

def words : Nat→List (Word (Fin 2))
  | 0=>[[]]
  | n+1=>(words n).flatMap fun w=>[0::w,1::w]

structure Counts where
  builds : Nat:=0
  queries : Nat:=0
  accepted : Nat:=0
  farTarget : Nat:=0
  farSource : Nat:=0
  near : Nat:=0
  nearOnly : Nat:=0
  maxWork : Nat:=0

def Counts.add (a b : Counts) : Counts :=
  ⟨a.builds+b.builds,a.queries+b.queries,a.accepted+b.accepted,a.farTarget+b.farTarget,
    a.farSource+b.farSource,a.near+b.near,a.nearOnly+b.nearOnly,max a.maxWork b.maxWork⟩

def budget (A E : DFA (Fin 2)) (coefficient n width : Nat) : Nat :=
  FarBank.queryBudget E n+FarBank.queryBudget (Automata.reverse A) n+
    (width*(width*(coefficient*((n+1).log2+1)^2)+4)+1)+23

def check (A B C E : DFA (Fin 2)) (w : Word (Fin 2)) (coefficient width : Nat) (hw : 0<width) : IO Counts := do
  let front:=forward B C E w width
  let back:=backward A B C w width
  let idx:=Cache.build A B C E w 0 width hw front back
  unless idx.work≤Cache.buildBudget A B C E w.length width do throw (IO.userError "cache build budget")
  let queryBound:=budget A E coefficient w.length width
  let mut out : Counts:={builds:=1}
  for left in List.range (w.length+2) do
    for right in List.range (w.length+2) do
      let found:=Cache.query idx left right
      let expected:=physical A B C E w left right
      unless found.1=expected do throw (IO.userError s!"cache original-cut mismatch {w} width={width} [{left},{right}] {found.1} != {expected}")
      unless found.2≤queryBound do throw (IO.userError s!"cache query budget {found.2} > {queryBound}")
      out:={out with queries:=out.queries+1,accepted:=out.accepted+(if found.1 then 1 else 0),maxWork:=max out.maxWork found.2}
      if valid : left≤right ∧ right≤w.length then
        let selected:=Grid.choose w.length width hw left right valid.1 valid.2
        let f:=FarBank.query (Table.get idx.forward selected.rightSlot) idx.selection left right
        let b:=idx.backward.query selected.leftSlot (w.length-right) (w.length-left)
        let near:=Border.query idx.near left right selected.leftGrid selected.rightGrid
        unless found.1=(f.1 || b.1 || near.1) do throw (IO.userError "cache branch assembly")
        out:={out with
          farTarget:=out.farTarget+(if f.1 then 1 else 0)
          farSource:=out.farSource+(if b.1 then 1 else 0)
          near:=out.near+(if near.1 then 1 else 0)
          nearOnly:=out.nearOnly+(if near.1 && !f.1 && !b.1 then 1 else 0)}
  return out

/- The deep fixture uses the one-state all-word automata. Their reverse
initial states also have identity transitions. Every final-subset row is
therefore the constant selected initial-state bit. We check the finite
transition premise and compare the complete cache against original cuts. -/
def stationaryRows (E : DFA (Fin 2)) (grid : Nat) : FarBank.Input E :=
  Vector.ofFn fun c=>Array.replicate (grid+1) (Colors.decode E c E.initial)

def deep (coefficient : Nat) : IO Unit := do
  let n:=128
  let width:=8
  let w : Word (Fin 2):=(List.range n).map fun k=>if k%2=0 then 0 else 1
  let rev:=Automata.reverse all
  for c in List.finRange 2 do
    unless rev.step rev.initial c=rev.initial do throw (IO.userError "deep stationary reverse premise")
  unless accepts all [] && accepts rev [] do throw (IO.userError "deep empty captures premise")
  let front : Cache.Inputs all w.length width:=Vector.ofFn fun slot=>stationaryRows all (Grid.position w.length width slot.val)
  let back : Cache.Inputs rev w.length width:=Vector.ofFn fun slot=>stationaryRows rev (Grid.backward w.length width slot.val)
  let idx:=Cache.build all all all all w 0 width (by decide) front back
  unless idx.work≤Cache.buildBudget all all all all w.length width do throw (IO.userError "deep cache build budget")
  let bound:=budget all all coefficient w.length width
  let mut queries:=0
  let mut maximum:=0
  for left in List.range (n+2) do
    for right in [left,min n (left+1),min n (left+7),min n (left+19),n,n+1] do
      let out:=Cache.query idx left right
      let reference:=physical all all all all w left right
      unless out.1=reference do throw (IO.userError s!"deep original cut {left} {right}")
      unless out.2≤bound do throw (IO.userError "deep cache query budget")
      queries:=queries+1
      maximum:=max maximum out.2
  IO.println s!"oneUseCacheDeep n={n} width={width} slots={idx.slots} builds=1 queries={queries} buildWork={idx.work} maxQueryWork={maximum} exactCuts=true"

def main : IO Unit := do
  IO.println "oneUseCache fixture all-start rows are independently enumerated, not production preprocessing"
  let patterns : List (DFA (Fin 2)×DFA (Fin 2)×DFA (Fin 2)×DFA (Fin 2)):=
    [(all,all,all,all),(all,positive,positive,all),(epsilon,positive,reset,reset),(reset,positive,reset,epsilon)]
  let mut total : Counts:={}
  let mut patternNo:=0
  for (A,B,C,E) in patterns do
    let coefficient:=Border.fixedBudget A B C E
    for n in List.range 4 do
      for w in words n do
        for width in [1,2,5] do
          if hw : 0<width then total:=total.add (←check A B C E w coefficient width hw)
      IO.println s!"oneUseCacheExhaustive pattern={patternNo} n={n} builds={total.builds} queries={total.queries}"
    patternNo:=patternNo+1
  let mixed:=Border.fixedBudget epsilon positive positive epsilon
  total:=total.add (←check epsilon positive positive epsilon [0,1,0] mixed 5 (by decide))
  IO.println s!"oneUseCacheTotal builds={total.builds} queries={total.queries} accepted={total.accepted} farTarget={total.farTarget} farSource={total.farSource} near={total.near} nearOnly={total.nearOnly} maxWork={total.maxWork}"
  unless total.nearOnly>0 && total.farTarget>0 && total.farSource>0 do throw (IO.userError "missing cache branch coverage")
  deep (Border.fixedBudget all all all all)

end OneUseCacheAudit

def main : IO Unit:=OneUseCacheAudit.main
