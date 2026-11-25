import REWB.BoundaryRangeRegression

open REWB REWB.BoundaryRange REWB.BoundaryRange.Regression

def binary (n code : Nat) : Word (Fin 2) :=
  (List.range n).map (fun i=>(⟨(code/2^i)%2,Nat.mod_lt _ (by decide)⟩ : Fin 2))

def accepts (d : DFA (Fin 2)) (w : Word (Fin 2)) : Bool := d.final (d.run d.initial w)

def parity : DFA (Fin 2) := ⟨2,0,fun q c=>⟨(q.val+c.val)%2,Nat.mod_lt _ (by decide)⟩,
  fun q=>decide (q.val=1)⟩

def main : IO Unit := do
  let begin ← IO.monoMsNow
  let mut maskBuilds:=0
  let mut maskChecks:=0
  let mut reversalChecks:=0
  let mut gapChecks:=0
  let mut maxMaskWork:=0
  let ds : List (DFA (Fin 2)) := [all,emptyOnly,positive,reset,parity]
  for d in ds do
    let reverse:=Automata.reverse d
    for n in [0:9] do
      for code in [0:2^n] do
        let w:=binary n code
        unless accepts reverse w==accepts d w.reverse do
          throw (IO.userError s!"noninjective reversal mismatch n={n}, code={code}")
        reversalChecks:=reversalChecks+1
        let ranges:=BoundaryApplication.Range.build d w
        for g in [0:n+3] do
          for q in List.ofFn (fun q : Fin d.stateCount=>q) do
            for k in List.ofFn (fun k : Fin d.stateCount=>k) do
              let result:=FarMask.build d ranges n g q k
              let bound:=(n+1)*(FarMask.pointBudget d n+8)+3
              unless result.work≤bound do
                throw (IO.userError s!"far mask exceeded returned-work bound n={n}")
              maxMaskWork:=max maxMaskWork result.work
              maskBuilds:=maskBuilds+1
              for y in List.ofFn (fun y : Fin (n+1)=>y) do
                let a:=n-y.val
                let want:=decide (g<a) && decide (d.run q (Spec.slice w g a)=k)
                unless result.bits.get y==want do
                  throw (IO.userError s!"far mask mismatch n={n}, code={code}, g={g}, y={y.val}")
                maskChecks:=maskChecks+1
  let gapPatterns : List (DFA (Fin 2)×DFA (Fin 2)×DFA (Fin 2)) :=
    [(emptyOnly,positive,all),(reset,all,all),(all,reset,all),(all,all,positive)]
  for (C,K,D) in gapPatterns do
    let gap:=Automata.gap C K D C.initial K.initial
    let reversedGap:=Automata.reverse gap
    for n in [0:6] do
      for code in [0:2^n] do
        let w:=binary n code
        let want:=(List.range (n+1)).any fun p=>
          accepts C (w.take p) && accepts K (w.take p) && accepts D (w.drop p)
        unless accepts gap w==want do
          throw (IO.userError s!"joint split mismatch n={n}, code={code}")
        unless accepts reversedGap w.reverse==want do
          throw (IO.userError s!"reversed joint split mismatch n={n}, code={code}")
        gapChecks:=gapChecks+2
  let finish ← IO.monoMsNow
  IO.println s!"boundary dispatch: mask builds={maskBuilds}, physical mask checks={maskChecks}, DFA reversals={reversalChecks}, joint gap checks={gapChecks}, max mask work={maxMaskWork}, mismatches=0 ({finish-begin} ms)"
  let n:=4096
  let w:=(List.range n).map fun i=>(⟨i%2,Nat.mod_lt _ (by decide)⟩ : Fin 2)
  let text:=w.toArray
  let ranges:=BoundaryApplication.Range.build reset w
  for g in [0,2048,4096,8192] do
    let out:=FarMask.build reset ranges n g 0 1
    unless out.work≤(n+1)*(FarMask.pointBudget reset n+8)+3 do
      throw (IO.userError "deep materialized far mask work failed")
    for y in List.ofFn (fun y : Fin (n+1)=>y) do
      let a:=n-y.val
      let want:=decide (g<a) && decide ((text[a-1]?.getD 0)=1)
      unless out.bits.get y==want do
        throw (IO.userError "deep far mask point mismatch")
    IO.println s!"far mask n={n}, g={g}, bits={out.bits.size}, work={out.work}; one shared K range index"
