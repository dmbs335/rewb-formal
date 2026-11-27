import REWB.ResidualSeparatedRegression
import REWB.ResidualRunWindows

open REWB REWB.ResidualSeparated REWB.ResidualSeparated.Regression
open REWB.BoundaryApplication

def binary (n code : Nat) : Word (Fin 2) :=
  (List.range n).map (fun i=>(⟨(code/2^i)%2,Nat.mod_lt _ (by decide)⟩ : Fin 2))

def accept (d : DFA (Fin 2)) (w : Word (Fin 2)) : Bool := d.final (d.run d.initial w)

def boundary (A B C K D E : DFA (Fin 2)) (w : Word (Fin 2)) (l r : Nat) : Bool := Id.run do
  for i in [0:r+1] do
    for a in [i:r+1] do
      if accept A (Spec.slice w 0 i) && accept B (Spec.slice w i a) then
        for p in [max a l:r+1] do
          if accept C (Spec.slice w a p) && accept K (Spec.slice w l p) then
            for j in [p:r+1] do
              let t:=j+(a-i)
              if t≤r && Spec.slice w i a==Spec.slice w j t &&
                accept D (Spec.slice w p j) && accept E (Spec.slice w t r) then return true
  return false

def oneUse (A B C E : DFA (Fin 2)) (w : Word (Fin 2)) (l r : Nat) : Bool := Id.run do
  for i in [l:r+1] do
    for a in [i:r+1] do
      if accept A (Spec.slice w l i) && accept B (Spec.slice w i a) then
        for j in [a:r+1] do
          let t:=j+(a-i)
          if t≤r && Spec.slice w i a==Spec.slice w j t &&
            accept C (Spec.slice w a j) && accept E (Spec.slice w t r) then return true
  return false

def literalP1 (P : SevenDFA (Fin 2)) (w : Word (Fin 2)) (l r d : Nat) : Bool := Id.run do
  for p in [l:r+1] do
    for e in [p:r+1] do
      if accept P.G (Spec.slice w e (p+d)) && accept P.H (Spec.slice w (e+d) w.length) then
        for i in [0:p+1] do
          for a in [i:p+1] do
            if accept P.A (Spec.slice w 0 i) && accept P.B (Spec.slice w i a) &&
              accept P.C (Spec.slice w a p) then
              for j in [p:e+1] do
                let t:=j+(a-i)
                if t≤e && Spec.slice w i a==Spec.slice w j t &&
                  accept P.D (Spec.slice w p j) && accept P.F (Spec.slice w t e) then return true
  return false

def literalP2 (P : SevenDFA (Fin 2)) (w : Word (Fin 2)) (l r d : Nat) : Bool := Id.run do
  for p in [l:r+1] do
    for e in [p:r+1] do
      if accept P.A (Spec.slice w 0 p) && accept P.G (Spec.slice w e (p+d)) &&
        accept P.H (Spec.slice w (e+d) w.length) then
        for i in [p:e+1] do
          for a in [i:e+1] do
            if accept P.B (Spec.slice w p i) && accept P.C (Spec.slice w i a) then
              for j in [a:e+1] do
                let t:=j+(a-i)
                if t≤e && Spec.slice w i a==Spec.slice w j t &&
                  accept P.D (Spec.slice w a j) && accept P.F (Spec.slice w t e) then return true
  return false

abbrev reset : DFA (Fin 2) := ⟨2,0,(fun _ c=>c),(fun q=>decide (q=1))⟩

def main : IO Unit := do
  let started←IO.monoMsNow
  let patterns : List (SevenDFA (Fin 2)) :=
    [⟨all,all,all,all,all,all,all⟩,p1,p2,
      ⟨all,positive,all,all,all,reset,all⟩,
      ⟨reset,all,positive,all,all,all,reset⟩]
  let mut windows:=0
  let mut positives1:=0
  let mut positives2:=0
  let mut runWindows:=0
  for n in [0:5] do
    for code in [0:2^n] do
      let w:=binary n code
      let f:=ArrayText.read w.toArray (0 : Fin 2)
      let runs:=(RankIndexSchedule.generate f n 1).runs
      for R in runs do
        for p in [0:n+2] do
          for d in [0:n+2] do
            if d%R.period=0 then
              let out:=ResidualRunWindows.candidate R p d
              unless out.2≤11 do throw (IO.userError "run-window scalar work")
              if let some c:=out.1 then
                unless c.lo≤c.hi && c.hi+c.distance≤n && c.hi≤c.lo+c.distance &&
                  Spec.slice w c.lo c.hi==Spec.slice w (c.lo+c.distance) (c.hi+c.distance) do
                  throw (IO.userError "run-derived window is invalid")
                runWindows:=runWindows+1
      for P in patterns do
        let ar:=Range.build P.A w
        let gr:=Range.build P.G w
        let hr:=Range.build P.H w
        for l in [0:n+1] do
          for r in [l:n+1] do
            for d in [0:n-r+1] do
              if r≤l+d && Spec.slice w l r==Spec.slice w (l+d) (r+d) then
                let states:=List.ofFn (fun q : Fin P.G.stateCount=>q)
                let got1:=states.any (fun q=>boundary P.A P.B P.C (gapStart P.G gr l r d q) P.D
                  (outerSuffix P.F P.G P.H hr r d n q) w l r)
                let got2:=states.any (fun q=>oneUse (innerPrefix P.A P.B P.G ar gr l r d q) P.C P.D
                  (outerSuffix P.F P.G P.H hr r d n q) w l r)
                unless got1==literalP1 P w l r d && got2==literalP2 P w l r d do
                  throw (IO.userError s!"separated reduction mismatch n={n}, code={code}, l={l}, r={r}, d={d}")
                windows:=windows+1
                if got1 then positives1:=positives1+1
                if got2 then positives2:=positives2+1
    IO.println s!"residualSeparated n={n} windows={windows} p1={positives1} p2={positives2} runWindows={runWindows}"
  unless boundary all positive all all all all [0,0] 1 2 && !oneUse all positive all all [0,0] 1 2 do
    throw (IO.userError "source lower-bound distinction lost")
  let finished←IO.monoMsNow
  IO.println s!"residualSeparatedComplete windows={windows} languageChecks={2*windows} runWindows={runWindows} mismatches=0 elapsed={finished-started}ms; tests use independent bounded cut scans, not a fast query implementation"
