import REWB.PeriodicActualJoinCost

/-! Bounded executable checks of the actual chronological join. The
literal witness search belongs only to this audit. All returned counters
are compared with the old executable and the measured extra-work bound
is checked on the same inputs. -/
namespace REWB.PeriodicActual.Join.Audit
open REWB.AffineProjection REWB.TimedJoin

def universal : DFA Bool := ⟨1,0,fun _ _=>0,fun _=>true⟩
def odd : DFA Bool := ⟨2,0,fun q _=>if q=0 then 1 else 0,fun q=>q==1⟩
def seen : DFA Bool := ⟨2,0,fun q a=>if a then 1 else q,fun q=>q==1⟩

def words : Nat→List (Word Bool)
  | 0=>[[]]
  | n+1=>(words n).flatMap fun w=>[false::w,true::w]

def forms : List AffineProjection.Formula :=
  [[],[[]],[[.le ((Aff.var 0).sub (.lit 2))]],
   [[.dvd 2 ((Aff.var 0).sub (.lit 1))]],
   [[.le ((Aff.lit 1).sub (.var 0)),.le ((Aff.var 0).sub (.lit 3))]]]

def atom (env : List Int) : Atom→Bool
  | .le a=>decide (a.eval env≤0)
  | .dvd m a=>decide (a.eval env%(m:Int)=0)

def formula (F : AffineProjection.Formula) (m : Nat) : Bool :=
  F.any fun conjunction=>conjunction.all (atom [(m:Int)])

def events (n mode : Nat) (flipped : Bool) : List TimedEntry :=
  if mode=0 && flipped then []
  else
    ((List.range (n+1)).filter (fun p=>
      if mode=2 then decide (p%2=if flipped then 1 else 0) else true)).map fun p=>
        ⟨p,⟨if mode=1 then p%2 else 0,
          forms[(p+(if flipped then 1 else 0))%forms.length]?.getD [[]]⟩⟩

def direct (d : DFA Bool) (w : Word Bool) (N : Nat) (es fs : List TimedEntry) : Bool :=
  es.any fun e=>fs.any fun f=>
    decide (e.pos≤f.pos ∧ f.pos≤w.length) && decide (e.entry.key=f.entry.key) &&
      d.final (d.run d.initial (Spec.slice w e.pos f.pos)) &&
      (List.range (N+1)).any fun m=>formula e.entry.formula m && formula f.entry.formula m

def same (x y : CountedJoin.Result) : Bool :=
  x.value.answer=y.value.answer && x.value.tests=y.value.tests &&
  x.value.eventVisits=y.value.eventVisits && x.value.textVisits=y.value.textVisits &&
  x.value.nodes=y.value.nodes && x.sortSteps=y.sortSteps

def runAudit : IO Unit := do
  let begin←IO.monoMsNow
  let mut cases:=0
  let mut witnesses:=0
  let mut positives:=0
  for n in List.range 5 do
    for w in words n do
      for d in [universal,odd,seen] do
        for mode in List.range 3 do
          let es:=events n mode false
          let fs:=events n mode true
          let B:=(es++fs).foldl (fun b e=>max b (UniformProjection.measure e.entry.formula)) 0
          for K in [0,2,4] do
            let got:=Join.run d K 3 w es fs
            let old:=CountedJoin.run d K 3 w es fs
            unless same got.1 old do
              throw (IO.userError s!"actual join changed a value or counter n={n}, mode={mode}, K={K}")
            let budget:=(Join.coefficient d.stateCount K B+10)*
              (DyadicIndex.heightFor w.length+1)*(es.length+fs.length+5*(w.length+1))
            unless got.2≤budget do
              throw (IO.userError s!"actual join work bound n={n}, mode={mode}, K={K}")
            if K>0 then
              unless got.1.value.answer=direct d w 3 es fs do
                throw (IO.userError s!"actual join literal witness n={n}, mode={mode}, K={K}")
              witnesses:=witnesses+1
            if got.1.value.answer then positives:=positives+1
            cases:=cases+1
  let finish←IO.monoMsNow
  IO.println s!"actual chronological join: cases={cases}, literal witness comparisons={witnesses}, positives={positives}, mismatches=0, elapsed={finish-begin} ms"

end REWB.PeriodicActual.Join.Audit

def main : IO Unit := REWB.PeriodicActual.Join.Audit.runAudit
