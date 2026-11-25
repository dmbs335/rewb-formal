import REWB.MaskedCutRegression

open REWB
open REWB.MaskedCut
open REWB.MaskedCut.Regression

def bits (n seed : Nat) : List Bool :=
  (List.range n).map (fun i=>decide ((seed/2^i)%2=1))

private def toggleReset : DFA Bool :=
  ⟨2,0,fun q bit=>if bit then 1 else if q=0 then 1 else 0,fun q=>decide (q=1)⟩

private def trivialDFA : DFA Bool := ⟨1,0,fun _ _=>0,fun _=>true⟩

def main : IO Unit := do
  let mut words := 0
  let mut queries := 0
  let mut pairChecks := 0
  let mut rotations := 0
  for n in List.range 7 do
    for seed in List.range (2^n) do
      let w := bits n seed
      let idx := Index.build parity enumeration w
      words := words+1
      unless idx.2=(Nat.log2 n+1)*n do
        throw (IO.userError "joint-cut construction counter mismatch")
      for l in List.range (n+1) do
        for lo in List.range (n+1) do
          for hi in List.range (n+1) do
            for r in List.range (n+1) do
              if l≤lo && lo≤hi && hi≤r then
                let out := Index.query parity enumeration idx.1 l lo hi r
                unless out.products≤3 && out.visits≤3*(Nat.log2 n+2) do
                  throw (IO.userError "joint-cut query counter bound exceeded")
                queries := queries+1
                for p in [false,true] do
                  for s in [false,true] do
                    let got := (out.answer.map (fun table=>MatrixTable.denote table p s)).getD false
                    let want := direct w l lo hi r p s
                    unless got=want do
                      throw (IO.userError s!"joint cut mismatch: w={w}, bounds={l},{lo},{hi},{r}, maps={p},{s}")
                    pairChecks := pairChecks+1
      let batch := Rotations.batch parity enumeration w
      unless batch.values.size=n && batch.products≤3*n &&
          batch.visits≤3*n*(Nat.log2 (2*n)+2) do
        throw (IO.userError "rotation batch counter mismatch")
      for h in List.range n do
        let some out := batch.values[h]? | throw (IO.userError "missing rotation")
        for p in [false,true] do
          for s in [false,true] do
            let got := (out.answer.map (fun table=>MatrixTable.denote table p s)).getD false
            let want := direct (w++w) h h (h+n-1) (h+n) p s
            unless got=want do
              throw (IO.userError "rotation/cut reference mismatch")
        rotations := rotations+1
  IO.println s!"joint cut audit: words={words}, intervalQueries={queries}, pairChecks={pairChecks}, rotations={rotations}, mismatches=0"

  let w := [true,false,false,true,false,true]
  let idx := DFAIndex.build toggleReset trivialDFA trivialDFA w
  let mapUniverse := (DFAIndex.jointEnum toggleReset trivialDFA trivialDFA).elems
  let mut constrainedChecks := 0
  for start in List.range (w.length+1) do
    for q in List.range (w.length+1) do
      if start+q≤w.length then
        for eta in List.range (q+1) do
          for lower in [0,1] do
            let out := DFAIndex.queryConstrained toggleReset trivialDFA trivialDFA idx.1 start lower eta q
            unless out.products≤4 && out.visits≤4*(Nat.log2 w.length+2) do
              throw (IO.userError "constrained tuple query counter mismatch")
            for target in mapUniverse do
              let got := (out.answer.map (fun x=>x.contains toggleReset trivialDFA trivialDFA target)).getD false
              let want := (List.range (eta+1)).any (fun rho=>decide (lower≤rho ∧
                (MaskedFiniteAction.Maps.wordMap toggleReset (Spec.slice w start (start+rho)),
                 MaskedFiniteAction.Maps.wordMap trivialDFA (Spec.slice w (start+rho) (start+q)),
                 MaskedFiniteAction.Maps.wordMap trivialDFA (Spec.slice w (start+rho) (start+eta)))=target))
              unless got=want do
                throw (IO.userError s!"constrained tuple mismatch: start={start}, lower={lower}, eta={eta}, q={q}")
              constrainedChecks := constrainedChecks+1
  IO.println s!"noncommuting DFA-map audit: universe={mapUniverse.length}, constrainedTupleChecks={constrainedChecks}, mismatches=0"

  let q := 4096
  let period := (List.range q).map (fun i=>decide (i%7=1 ∨ i%11=4))
  let large := Rotations.batch parity enumeration period
  unless large.values.size=q && large.preparation=(Nat.log2 (2*q)+1)*(2*q) &&
      large.products≤3*q && large.visits≤3*q*(Nat.log2 (2*q)+2) do
    throw (IO.userError "large shared rotation batch mismatch")
  IO.println s!"shared doubled-period batch: q={q}, outputs={large.values.size}, preparationProducts={large.preparation}, queryProducts={large.products}, visits={large.visits}"
