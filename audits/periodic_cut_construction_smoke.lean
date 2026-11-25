import REWB.PeriodicConstructionCutRegression
import REWB.PeriodicConstructionPattern
import REWB.MaskedClusterRegression
import REWB.MaskedPeriodicTextRegression

/-! Bounded compiled-runtime audit. Reference list scans and literal slices
occur only here. The production cut index uses the counted finite algebra.
Every comparison checks old scalar counters in addition to returned values. -/
namespace REWB.PeriodicConstruction.Cut.Audit
open REWB.PeriodicConstruction REWB.MaskedCut.DFAIndex
open REWB.MaskedPeriodic.Regression (universal)
open REWB.MaskedCluster.Regression (seen last)

def check (ok : Bool) (label : String) : IO Unit :=
  unless ok do throw (IO.userError label)

def flush : IO Unit := do (←IO.getStdout).flush

def summaryData {M : Type} [DecidableEq M] {e : FiniteRelation.Enumeration M}
    (s : MaskedCut.Summary e) : M×List (MatrixTable.Cell M) := (s.total,s.cuts.data)

def sameTree {M : Type} [DecidableEq M] {e : FiniteRelation.Enumeration M} :
    MaskedCut.Index.Tree e→MaskedCut.Index.Tree e→Bool
  | .leaf xs,.leaf ys=>decide (xs.map summaryData=ys.map summaryData)
  | .node row a b,.node other c d=>
    decide (row.cut=other.cut ∧ row.len=other.len) &&
      decide (row.leftSuffix.toList.map summaryData=other.leftSuffix.toList.map summaryData) &&
      decide (row.rightPrefix.toList.map summaryData=other.rightPrefix.toList.map summaryData) &&
      sameTree a c && sameTree b d
  | _,_=>false

def sameRange {M : Type} [DecidableEq M] {e : FiniteRelation.Enumeration M}
    (a b : DyadicIndex.Result (MaskedCut.Summary e)) : Bool :=
  decide (a.answer.map summaryData=b.answer.map summaryData) &&
    decide (a.products=b.products ∧ a.visits=b.visits)

def sameIndex {M : Type} [DecidableEq M] {e : FiniteRelation.Enumeration M}
    (a b : MaskedCut.Index.Result e) : Bool :=
  decide (a.answer.map (fun m=>m.data)=b.answer.map (fun m=>m.data)) &&
    decide (a.products=b.products ∧ a.visits=b.visits)

def sameTuples (B C E : DFA Bool) (a b : MaskedPeriodic.TupleResult B C E) : Bool :=
  decide (a.values=b.values ∧ a.products=b.products ∧ a.visits=b.visits)

def sameIndexed (a b : MaskedPeriodic.IndexedAnswer) : Bool :=
  a.result.answer=b.result.answer && a.result.slots=b.result.slots &&
    a.result.arithmetic=b.result.arithmetic && a.products=b.products && a.visits=b.visits

def words (n : Nat) : List (Word Bool) :=
  (List.range (2^n)).map fun bits=>
    List.ofFn (fun i : Fin n=>decide ((bits/2^i.val)%2=1))

def runSmall : IO Unit := do
  let patterns : List (DFA Bool×DFA Bool×DFA Bool) :=
    [(universal,universal,universal),(seen,universal,universal),
      (universal,seen,universal),(universal,universal,last)]
  let mut builds:=0
  let mut ranges:=0
  let mut windows:=0
  let mut cells:=0
  let mut tuples:=0
  for triple in patterns do
    let B:=triple.1
    let C:=triple.2.1
    let E:=triple.2.2
    let rc:=Cut.rangeCoefficient B.stateCount C.stateCount E.stateCount
    let ic:=Cut.indexCoefficient B.stateCount C.stateCount E.stateCount
    let tc:=Cut.tupleCost B.stateCount C.stateCount E.stateCount
    let intc:=Cut.interiorCoefficient B.stateCount C.stateCount E.stateCount
    let endc:=Cut.endingCoefficient B.stateCount C.stateCount E.stateCount
    let values:=(jointEnum B C E).elems
    for n in List.range 4 do
      for w in words n do
        let got:=Cut.buildDFA B C E w
        let old:=MaskedCut.DFAIndex.build B C E w
        check (got.1.2=old.2 && sameTree got.1.1 old.1) s!"build changed n={n}"
        check (got.2≤Cut.buildDFACost B.stateCount C.stateCount E.stateCount n) "build cost"
        builds:=builds+1
        let idx:=got.1.1
        for l in List.range (n+1) do
          for r in List.range (n+1) do
            if l≤r then
              let out:=Cut.queryRange B C E idx l r
              let ref:=DyadicIndex.query (MaskedCut.ops (jointOps B C E) (jointEnum B C E)) old.1 l r
              check (sameRange out.1 ref) "range whole value/counters"
              check (out.2≤rc*(ref.products+ref.visits+1)) "range cost"
              ranges:=ranges+1
        for bad in [(n+1,n+2),(n+2,0)] do
          let out:=Cut.queryRange B C E idx bad.1 bad.2
          let ref:=DyadicIndex.query (MaskedCut.ops (jointOps B C E) (jointEnum B C E)) old.1 bad.1 bad.2
          check (sameRange out.1 ref) "invalid range whole value/counters"
          check (out.2≤rc*(ref.products+ref.visits+1)) "invalid range cost"
          ranges:=ranges+1
        for l in List.range (n+1) do
          for a in List.range (n+1) do
            for b in List.range (n+1) do
              for r in List.range (n+1) do
                if l≤a ∧ a≤b ∧ b≤r then
                  let out:=Cut.queryIndex B C E idx l a b r
                  let ref:=MaskedCut.Index.query (jointOps B C E) (jointEnum B C E) old.1 l a b r
                  check (sameIndex out.1 ref) "cut window whole value/counters"
                  check (out.2≤ic*(ref.products+ref.visits+1)) "cut window cost"
                  let extracted:=Cut.fullTuples B C E out.1.answer
                  check (extracted.1=MaskedPeriodic.fullTuples B C E ref.answer) "full tuple order/value"
                  check (extracted.2≤tc) "full tuple extraction cost"
                  match out.1.answer with
                  | none=>throw (IO.userError "bounded window unexpectedly missing")
                  | some table=>
                    for p in values do
                      for s in values do
                        let expected:=(List.range (b-a+1)).any fun off=>
                          let cut:=a+off
                          decide (jointWord B C E (Spec.slice w l cut)=p ∧
                            jointWord B C E (Spec.slice w cut r)=s)
                        check (MatrixTable.denote table p s=expected)
                          s!"literal cut cell n={n}, range={l}/{a}/{b}/{r}"
                        cells:=cells+1
                  windows:=windows+1
        for start in List.range (n+1) do
          for q in List.range (n-start+1) do
            let inside:=Cut.interior B C E idx start q
            let oldInside:=MaskedPeriodic.interiorTuples B C E old.1 start q
            check (sameTuples B C E inside.1 oldInside) "interior whole value/counters"
            check (inside.2≤intc*(oldInside.products+oldInside.visits+1)) "interior cost"
            tuples:=tuples+1
            for eta in List.range (q+1) do
              let ending:=Cut.ending B C E idx start eta q
              let oldEnding:=MaskedPeriodic.endingTuples B C E old.1 start eta q
              check (sameTuples B C E ending.1 oldEnding) "ending whole value/counters"
              check (ending.2≤endc*(oldEnding.products+oldEnding.visits+1)) "ending cost"
              tuples:=tuples+1
  IO.println s!"cut small: builds={builds}, ranges={ranges}, windows={windows}, literal cells={cells}, tuple queries={tuples}"
  flush

def runPhases : IO Unit := do
  let mut cases:=0
  let mut full:=0
  let mut hits:=0
  for B in [universal,seen] do
    let C:=universal
    let E:=universal
    let prep:=Pattern.preparePattern B.stateCount C.stateCount E.stateCount
    let prepared:=prep.1
    let qc:=Cut.queryCoefficient B.stateCount C.stateCount E.stateCount prepared.K
    let pc:=Cut.phaseCoefficient B.stateCount C.stateCount E.stateCount prepared.K
    let tailc:=Cut.tailCoefficient B.stateCount C.stateCount E.stateCount
    for V in [[true],[true,false]] do
      for eta in List.range V.length do
        let w:Word Bool:=[false]++Periodic.repeatWord V 5++V.take eta++[true]
        let R:=1+5*V.length+eta
        let built:=Cut.buildDFA B C E w
        let idx:=built.1.1
        let oldIdx:=(MaskedCut.DFAIndex.build B C E w).1
        let tail:=Cut.prepareTail B C E idx R w.length
        let oldTail:=MaskedPeriodic.Text.prepareTail B C E oldIdx R w.length
        check (tail.1.map=oldTail.map && tail.1.products=oldTail.products && tail.1.visits=oldTail.visits)
          "tail whole value/counters"
        check (tail.2≤tailc*(oldTail.products+oldTail.visits+1)) "tail cost"
        for mask in [Array.replicate (w.length+1) true,#[false,false,true,false,true],
            Array.ofFn (fun i : Fin (w.length+1)=>decide (i.val%3=1)),#[]] do
          let counts:=MaskedProgression.build mask 0 (w.length+1) (prepared.K*V.length)
          let phase:=Cut.phaseQuery B C E prepared idx tail.1.map 1 eta V.length 5 counts.counts 0 1
          let oldPhase:=MaskedPeriodic.phaseQuery B C E prepared oldIdx oldTail.map 1 eta V.length 5 counts.counts 0 1
          check (sameIndexed phase.1 oldPhase) "whole phase old value/counters"
          check (phase.2≤pc*(MaskedPeriodic.Batch.queryCost oldPhase+1)) "whole phase cost"
          full:=full+1
          for s in [0,1,2,R,R+1] do
            for q in [0,V.length] do
              let got:=Cut.query B C E prepared idx tail.1.map s R q counts.counts 0
              let old:=MaskedPeriodic.Text.query B C E prepared oldIdx oldTail.map s R q counts.counts 0
              check (sameIndexed got.1 old) "guarded phase old value/counters"
              check (got.2≤qc*(MaskedPeriodic.Batch.queryCost old+1)) "guarded phase cost"
              if 1≤s then
                let expected:=MaskedPeriodic.Text.Regression.direct B C E w (w.drop R) s R q mask 0 (w.length+1)
                check (got.1.result.answer=expected) s!"literal phase s={s}, R={R}, q={q}"
              if got.1.result.answer then hits:=hits+1
              cases:=cases+1
  let prep:=Pattern.preparePattern 1 1 1
  let empty:=Cut.buildDFA universal universal universal []
  let tail:=Cut.prepareTail universal universal universal empty.1.1 0 0
  let out:=Cut.query universal universal universal prep.1 empty.1.1 tail.1.map 0 0 0 #[] 0
  let old:=MaskedPeriodic.Text.query universal universal universal prep.1
    (MaskedCut.DFAIndex.build universal universal universal []).1 tail.1.map 0 0 0 #[] 0
  check (sameIndexed out.1 old && out.1.result.answer=false) "empty text / zero period"
  check (out.2≤Cut.queryCoefficient 1 1 1 prep.1.K*(MaskedPeriodic.Batch.queryCost old+1)) "empty query cost"
  IO.println s!"cut phases: guarded={cases+1}, full phases={full}, accepted={hits}"
  flush

def runDeep : IO Unit := do
  let B:=universal
  let C:=universal
  let E:=universal
  let w:Word Bool:=List.replicate 257 true
  let got:=Cut.buildDFA B C E w
  let old:=MaskedCut.DFAIndex.build B C E w
  check (got.1.2=old.2 && sameTree got.1.1 old.1) "deep full tree"
  check (got.2≤Cut.buildDFACost 1 1 1 w.length) "deep build cost"
  let mut checks:=0
  for request in [(0,0,0,0),(0,0,257,257),(0,1,128,257),(128,128,129,257),(257,257,257,257)] do
    let l:=request.1
    let a:=request.2.1
    let b:=request.2.2.1
    let r:=request.2.2.2
    let out:=Cut.queryIndex B C E got.1.1 l a b r
    let ref:=MaskedCut.Index.query (jointOps B C E) (jointEnum B C E) old.1 l a b r
    check (sameIndex out.1 ref) "deep partial cut value"
    check (out.2≤Cut.indexCoefficient 1 1 1*(ref.products+ref.visits+1)) "deep partial cut cost"
    checks:=checks+1
  IO.println s!"cut deep: n=257, products={got.1.2}, construction work={got.2}, windows={checks}"
  flush

def main : IO Unit := do
  let start←IO.monoMsNow
  runSmall
  runPhases
  runDeep
  let finish←IO.monoMsNow
  IO.println s!"periodic cut construction audit passed in {finish-start} ms"

end REWB.PeriodicConstruction.Cut.Audit

def main : IO Unit := REWB.PeriodicConstruction.Cut.Audit.main
