import REWB.ResidualDispatchRegression

/-! Reproducible actual dispatch-list audit. All bounded cut scans below
are independent reference checks, not a fast query implementation. -/
open REWB REWB.ResidualSeparated REWB.ResidualSeparated.Regression
open REWB.BoundaryApplication REWB.ResidualDispatch REWB.RunGeometry

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

private def require (b : Bool) (msg : String) : IO Unit := unless b do throw (IO.userError msg)

private def referenceCandidate (R : Bounds) (p d : Nat) : List IndexedGrid.Strip :=
  if R.lo≤p && p+d≤R.hi then [⟨p,min (R.hi-d) (p+d),d⟩] else []

private def referenceWindows (plan : Plan) (D Q : Nat) : List IndexedGrid.Strip := Id.run do
  let mut out:=plan.strips.batch.jobs.map (fun W=>(⟨W.left,W.right,W.origin.distance⟩ : IndexedGrid.Strip))
  let mut low:=#[]
  let mut large:=#[]
  for R in plan.generated.runs do
    for i in [0:R.hi-R.lo-2*R.period+1+D] do
      for c in referenceCandidate R (R.lo+i) R.period do low:=low.push c
    if Q<R.period && 3*R.period≤R.hi-R.lo then
      for j in [1:(R.hi-R.lo)/R.period+1] do
        for p in [R.lo:R.hi+1] do
          for c in referenceCandidate R p (j*R.period) do large:=large.push c
  out:=out++low.toList++large.toList
  return out

private def checkPlan (w : Word (Fin 2)) (s L D Q : Nat) : IO Plan := do
  let n:=w.length
  let plan:=prepare (ArrayText.read w.toArray 0) n s L D Q
  require (plan.windows==referenceWindows plan D Q) s!"selector mismatch n={n} s={s} L={L} D={D} Q={Q}"
  require (plan.selectors==plan.windows.length) "cached selector count"
  require (plan.selectors≤selectorBudget n L D Q) "selector bound"
  require (plan.selectorWork≤selectorWorkBudget n L D Q) "row construction work"
  require (plan.work≤preparationBudget 2 n s L D Q) "complete preparation work"
  for c in plan.windows do
    require (c.lo≤c.hi && c.hi+c.distance≤n && c.hi≤c.lo+c.distance &&
      Spec.slice w c.lo c.hi==Spec.slice w (c.lo+c.distance) (c.hi+c.distance)) "invalid selected window"
  return plan

private structure MatchRef where
  p1 : Bool := false
  p2 : Bool := false
  short1 : Bool := false
  short2 : Bool := false

/-- Every possible separated literal copy interval, with all witness
cuts checked directly. Maximality, runs and grid sampling are unused. -/
private def referenceMatch (P : SevenDFA (Fin 2)) (w : Word (Fin 2)) (L : Nat) : MatchRef := Id.run do
  let mut out:MatchRef:={}
  for l in [0:w.length+1] do
    for r in [l:w.length+1] do
      for d in [0:w.length-r+1] do
        if r≤l+d && Spec.slice w l r==Spec.slice w (l+d) (r+d) then
          let one:=literalP1 P w l r d
          let two:=literalP2 P w l r d
          out:={
            p1:=out.p1 || one
            p2:=out.p2 || two
            short1:=out.short1 || (r-l<L && one)
            short2:=out.short2 || (r-l<L && two)}
  return out

private def queried (P : SevenDFA (Fin 2)) (w : Word (Fin 2)) (plan : Plan) : Bool×Bool := Id.run do
  let ar:=Range.build P.A w
  let gr:=Range.build P.G w
  let hr:=Range.build P.H w
  let states:=List.ofFn (fun q : Fin P.G.stateCount=>q)
  let mut one:=false
  let mut two:=false
  for c in plan.windows do
    for q in states do
      one:=one || boundary P.A P.B P.C (gapStart P.G gr c.lo c.hi c.distance q) P.D
        (outerSuffix P.F P.G P.H hr c.hi c.distance w.length q) w c.lo c.hi
      two:=two || oneUse (innerPrefix P.A P.B P.G ar gr c.lo c.hi c.distance q) P.C P.D
        (outerSuffix P.F P.G P.H hr c.hi c.distance w.length q) w c.lo c.hi
  return (one,two)

abbrev reset : DFA (Fin 2) := ⟨2,0,(fun _ c=>c),(fun q=>decide (q=1))⟩

def main : IO Unit := do
  let started←IO.monoMsNow
  let patterns : List (SevenDFA (Fin 2)) :=
    [⟨all,all,all,all,all,all,all⟩,p1,p2,
      ⟨all,positive,all,all,all,reset,all⟩,
      ⟨reset,all,positive,all,all,all,reset⟩]
  let mut schedules:=0
  let mut selectors:=0
  let mut languageChecks:=0
  let mut nonshort1:=0
  let mut nonshort2:=0
  for n in [0:7] do
    for code in [0:2^n] do
      let w:=binary n code
      for (s,L,D,Q) in [(1,1,1,0),(1,2,2,1),(2,2,3,0),(3,4,7,2)] do
        let plan←checkPlan w s L D Q
        schedules:=schedules+1
        selectors:=selectors+plan.selectors
      if n≤4 then
        let f:=ArrayText.read w.toArray (0 : Fin 2)
        for P in patterns do
          let small1:=(CountedP1Cubic.solve P f n 0).answer
          let small2:=(SmallPeriodP2.solve P f n 0).accepted
          require (!small1 && !small2) "period-zero solver accepted"
          for (s,L,D) in [(1,1,1),(1,2,2),(2,2,3)] do
            let plan←checkPlan w s L D 0
            let got:=queried P w plan
            let ref:=referenceMatch P w L
            require ((small1 || ref.short1 || got.1)==ref.p1 &&
              (small2 || ref.short2 || got.2)==ref.p2) s!"dispatch language mismatch n={n} code={code} L={L}"
            if got.1 && !ref.short1 then nonshort1:=nonshort1+1
            if got.2 && !ref.short2 then nonshort2:=nonshort2+1
            languageChecks:=languageChecks+2
    IO.println s!"residualDispatch n={n} schedules={schedules} selectors={selectors} languageChecks={languageChecks}"
  require (nonshort1>0 && nonshort2>0) "nonshort branches untested"
  for (n,period,s,L,D,Q) in [(512,1,16,24,16,2),(384,3,16,24,16,1)] do
    let w:=(List.range n).map (fun i=>(⟨(i%period)%2,by omega⟩ : Fin 2))
    let plan←checkPlan w s L D Q
    IO.println s!"residualDispatchDeep n={n} period={period} runs={plan.generated.runs.length} windows={plan.selectors} selectorWork={plan.selectorWork} totalWork={plan.work}"
  let ended←IO.monoMsNow
  IO.println s!"residualDispatchComplete schedules={schedules} selectors={selectors} languageChecks={languageChecks} nonshortP1={nonshort1} nonshortP2={nonshort2} mismatches=0 elapsed={ended-started}ms; bounded query scans are audit references"
