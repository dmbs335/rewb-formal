import REWB.OneUseRangeBorderRegression

open REWB REWB.Spec REWB.OneUseRange REWB.OneUseRange.Border.Regression
open REWB.BoundaryRange

namespace OneUseBorderAudit

def accepts (d : DFA (Fin 2)) (w : Word (Fin 2)) : Bool := d.final (d.run d.initial w)

def inner (B C : DFA (Fin 2)) (w : Word (Fin 2)) (i t : Nat) : Bool :=
  (List.range (t+1)).any fun L=>
    decide (i+2*L≤t) && decide (slice w i (i+L)=slice w (t-L) t) &&
      accepts B (slice w i (i+L)) && accepts C (slice w (i+L) (t-L))

def physical (A B C E : DFA (Fin 2)) (w : Word (Fin 2)) (left right i t : Nat) : Bool :=
  decide (left≤i ∧ i≤t ∧ t≤right ∧ right≤w.length) &&
    accepts A (slice w left i) && inner B C w i t && accepts E (slice w t right)

def region (A B C E : DFA (Fin 2)) (w : Word (Fin 2)) (left right gl gr : Nat) : Bool :=
  ((List.range (gl-left)).map (left+·)).any fun i=>
    ((List.range (right-gr)).map (gr+1+·)).any fun t=>physical A B C E w left right i t

def words : Nat→List (Word (Fin 2))
  | 0=>[[]]
  | n+1=>(words n).flatMap fun w=>[0::w,1::w]

structure Counts where
  builds : Nat:=0
  inners : Nat:=0
  points : Nat:=0
  regions : Nat:=0
  accepted : Nat:=0
  maxWork : Nat:=0

def Counts.add (a b : Counts) : Counts :=
  ⟨a.builds+b.builds,a.inners+b.inners,a.points+b.points,a.regions+b.regions,
    a.accepted+b.accepted,max a.maxWork b.maxWork⟩

def check (A B C E : DFA (Fin 2)) (w : Word (Fin 2)) (coefficient : Nat) : IO Counts := do
  let idx:=Border.build A B C E w 0
  unless idx.work≤Border.buildBound A B C E w.length do throw (IO.userError "one-use border build budget")
  let innerBound:=C.stateCount*(coefficient*((w.length+1).log2+1)^2+27)+NearIndex.rangeBudget C w.length+7
  let atBound:=innerBound+NearIndex.rangeBudget A w.length+NearIndex.rangeBudget E w.length+13
  let mut counts : Counts:={builds:=1}
  for i in List.finRange (w.toArray.size+1) do
    for t in List.range (w.length+1) do
      if i.val≤t then
        let out:=Border.inner idx i t
        let ref:=inner B C w i.val t
        unless out.1=ref do throw (IO.userError s!"one-use inner {w} {i.val} {t}: {out.1} != {ref}")
        unless out.2≤innerBound do throw (IO.userError "one-use inner budget")
        counts:={counts with inners:=counts.inners+1}
  for left in List.range (w.length+2) do
    for right in List.range (w.length+2) do
      for i in List.range (w.length+2) do
        for t in List.range (w.length+2) do
          let out:=Border.queryAt idx left right i t
          let ref:=physical A B C E w left right i t
          unless out.1=ref do throw (IO.userError s!"one-use point {w} {left} {right} {i} {t}")
          unless out.2≤atBound do throw (IO.userError "one-use point budget")
          counts:={counts with points:=counts.points+1}
  for left in List.range (w.length+1) do
    for right in List.range (w.length+1) do
      if left≤right then
        for gl in List.range (w.length+2) do
          for gr in List.range (w.length+1) do
            let out:=Border.query idx left right gl gr
            let ref:=region A B C E w left right gl gr
            unless out.1=ref do throw (IO.userError s!"one-use region {w} {left} {right} {gl} {gr}")
            unless out.2≤(gl-left)*((right-gr)*(atBound+3)+4)+1 do
              throw (IO.userError "one-use region budget")
            counts:={counts with regions:=counts.regions+1,accepted:=counts.accepted+(if out.1 then 1 else 0),maxWork:=max counts.maxWork out.2}
  return counts

def deep (B C : DFA (Fin 2)) (coefficient n left right gl gr : Nat) : IO Unit := do
  let w : Word (Fin 2):=(List.range n).map fun k=>if k%2=0 then 0 else 1
  let idx:=Border.build all B C all w 0
  unless idx.work≤Border.buildBound all B C all w.length do throw (IO.userError "deep build budget")
  let innerBound:=C.stateCount*(coefficient*((w.length+1).log2+1)^2+27)+NearIndex.rangeBudget C w.length+7
  let atBound:=innerBound+NearIndex.rangeBudget all w.length+NearIndex.rangeBudget all w.length+13
  let queryBound:=(gl-left)*((right-gr)*(atBound+3)+4)+1
  let out:=Border.query idx left right gl gr
  let ref:=region all B C all w left right gl gr
  unless out.1=ref do throw (IO.userError "deep physical slices")
  unless out.2≤queryBound do throw (IO.userError "deep query budget")
  IO.println s!"oneUseBorderDeep n={n} buildWork={idx.work} queryWork={out.2} answer={out.1} exactSlices=true"

def main : IO Unit := do
  IO.println "oneUseBorderPreparing fixed pattern budgets"
  let coefficientAll:=2*BoundaryBorder.Regular.fixedBudget all all all+521
  IO.println s!"oneUseBorderCoefficient all={coefficientAll}"
  let coefficientMixed:=2*BoundaryBorder.Regular.fixedBudget positive positive positive+521
  IO.println s!"oneUseBorderCoefficient mixed={coefficientMixed}"
  let patterns : List (DFA (Fin 2)×DFA (Fin 2)×DFA (Fin 2)×DFA (Fin 2)×Nat):=
    [(all,all,all,all,coefficientAll),(all,positive,positive,all,coefficientMixed),(epsilon,positive,reset,epsilon,coefficientMixed)]
  let mut total : Counts:={}
  for n in List.range 4 do
    for w in words n do
      for (A,B,C,E,coefficient) in patterns do
        total:=total.add (←check A B C E w coefficient)
    IO.println s!"oneUseBorderExhaustive length={n} builds={total.builds} points={total.points} regions={total.regions}"
  total:=total.add (←check all positive positive all [0,1,1,1,0] coefficientMixed)
  total:=total.add (←check reset positive reset reset [1,0,1,0,1] coefficientMixed)
  IO.println s!"oneUseBorderTotal builds={total.builds} inners={total.inners} points={total.points} regions={total.regions} accepted={total.accepted} maxWork={total.maxWork}"
  deep all all coefficientAll 256 61 244 65 240
  deep positive reset coefficientMixed 129 3 120 7 116

end OneUseBorderAudit

def main : IO Unit:=OneUseBorderAudit.main
