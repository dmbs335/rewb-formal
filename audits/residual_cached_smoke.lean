import REWB.ResidualCachedRegression

/-! Pending all-start rows are supplied by independent finite cut scans
only in this audit. They are not a production row solver and their cost
is not hidden in the cache ledger. The tested bank/dispatch paths are
the actual compiled definitions, including every state/window fold. -/
open REWB REWB.Spec REWB.BoundaryRange REWB.BoundaryIndex
open REWB.OneUseRange.Border.Regression
open REWB.ResidualCached

namespace ResidualCachedAudit

def accept (A : DFA (Fin 2)) (w : Word (Fin 2)) : Bool := A.final (A.run A.initial w)
def reject : DFA (Fin 2) := ⟨1,⟨0,by decide⟩,fun _ _=>⟨0,by decide⟩,fun _=>false⟩

def masked (B C E : DFA (Fin 2)) (w : Word (Fin 2)) (mask : Nat→Bool) (i : Nat) : Bool := Id.run do
  for a in [i:w.length+1] do
    for j in [a:w.length+1] do
      let t:=j+(a-i)
      if t≤w.length && mask j && slice w i a==slice w j t && accept B (slice w i a) &&
          accept C (slice w a j) && accept E (slice w t w.length) then return true
  return false

def p1Rows (P : SevenDFA (Fin 2)) (w : Word (Fin 2)) (s : Nat) : P1.Inputs P w.length s :=
  Vector.ofFn fun g=>
    let K:=gap P g
    let reverseB:=Automata.reverse P.B
    let reverseA:=Automata.reverse P.A
    let gaps:=Vector.ofFn fun k : Fin P.G.stateCount=>Automata.reverse (Automata.gap P.C K P.D P.C.initial k)
    let reversed:=w.reverse
    Vector.ofFn fun slot=>
      let grid:=CacheGrid.upper w.length s slot.val
      Vector.ofFn fun q=>Vector.ofFn fun k=>Array.ofFn fun i : Fin (w.length+1)=>
        masked reverseB (gaps.get k) reverseA reversed
          (fun j=>farMask K w grid q k (w.length-j)) i.val

def plainRows (B C E : DFA (Fin 2)) (w : Word (Fin 2)) (s : Nat) : OneUseRange.Cache.Inputs E w.length s :=
  Vector.ofFn fun slot=>
    let grid:=OneUseRange.Grid.position w.length s slot.val
    Vector.ofFn fun c=>Array.ofFn fun i : Fin (grid+1)=>
      masked B C (OneUseRange.FarSelection.variant E c) (w.take grid) (fun _=>true) i.val

def reverseRows (A B C : DFA (Fin 2)) (w : Word (Fin 2)) (s : Nat) :
    OneUseRange.Cache.Inputs (Automata.reverse A) w.length s :=
  let E:=Automata.reverse A
  let B':=Automata.reverse B
  let C':=Automata.reverse C
  let reversed:=w.reverse
  Vector.ofFn fun slot=>
    let grid:=OneUseRange.Grid.backward w.length s slot.val
    Vector.ofFn fun c=>Array.ofFn fun i : Fin (grid+1)=>
      masked B' C' (OneUseRange.FarSelection.variant E c) (reversed.take grid) (fun _=>true) i.val

def p2Rows (P : SevenDFA (Fin 2)) (w : Word (Fin 2)) (s : Nat) : P2.Inputs P w.length s :=
  ⟨Table.build (fun q=>
    let row:=Table.build fun c=>(plainRows P.C P.D (suffix P q c) w s,0)
    (row,row.work)),
   Table.build (fun a=>
    let row:=Table.build fun g=>(reverseRows (front P a g) P.C P.D w s,0)
    (row,row.work))⟩

def inner1 (P : SevenDFA (Fin 2)) (w : Word (Fin 2)) (p e : Nat) : Bool := Id.run do
  for i in [0:p+1] do
    for a in [i:p+1] do
      if accept P.A (slice w 0 i) && accept P.B (slice w i a) && accept P.C (slice w a p) then
        for j in [p:e+1] do
          let t:=j+(a-i)
          if t≤e && slice w i a==slice w j t && accept P.D (slice w p j) &&
              accept P.F (slice w t e) then return true
  return false

def inner2 (P : SevenDFA (Fin 2)) (w : Word (Fin 2)) (p e : Nat) : Bool := Id.run do
  if !accept P.A (slice w 0 p) then return false
  for i in [p:e+1] do
    for a in [i:e+1] do
      if accept P.B (slice w p i) && accept P.C (slice w i a) then
        for j in [a:e+1] do
          let t:=j+(a-i)
          if t≤e && slice w i a==slice w j t && accept P.D (slice w a j) &&
              accept P.F (slice w t e) then return true
  return false

def inWindow (P : SevenDFA (Fin 2)) (w : Word (Fin 2)) (c : IndexedGrid.Strip) : Bool×Bool := Id.run do
  let mut one:=false
  let mut two:=false
  for p in [c.lo:c.hi+1] do
    for e in [p:c.hi+1] do
      if accept P.G (slice w e (p+c.distance)) && accept P.H (slice w (e+c.distance) w.length) then
        one:=one || inner1 P w p e
        two:=two || inner2 P w p e
  return (one,two)

def reference (P : SevenDFA (Fin 2)) (w : Word (Fin 2)) : Bool×Bool := Id.run do
  let mut one:=false
  let mut two:=false
  for p in [0:w.length+1] do
    for e in [p:w.length+1] do
      let len:=e-p
      for k in [e:w.length-len+1] do
        if slice w p e==slice w k (k+len) && accept P.G (slice w e k) && accept P.H (slice w (k+len) w.length) then
          one:=one || inner1 P w p e
          two:=two || inner2 P w p e
  return (one,two)

def check (P : SevenDFA (Fin 2)) (text : Array (Fin 2)) (s : Nat) (hs : 0<s) (dispatch : Bool) : IO (Nat×Nat×Nat) := do
  let w:=text.toList
  let one:=p1Rows P w s
  let two:=p2Rows P w s
  let a:=P1.build P w 0 s hs one
  let b:=P2.build P w 0 s hs two
  unless a.work≤P1.buildBudget P w.length s && b.work≤P2.buildBudget P w.length s do
    throw (IO.userError "variant bank build ledger")
  let qa:=P1.queryBudget P w.length s
  let qb:=P2.queryBudget P w.length s
  let mut count:=0
  let mut yes:=0
  let mut no:=0
  for lo in [0:w.length+1] do
    for hi in [lo:w.length+1] do
      for shift in [hi-lo:w.length-hi+1] do
        if slice w lo hi==slice w (lo+shift) (hi+shift) then
          let c : IndexedGrid.Strip:=⟨lo,hi,shift⟩
          let found1:=P1.query a c
          let found2:=P2.query b c
          let expected:=inWindow P w c
          unless found1.1=expected.1 && found2.1=expected.2 do
            throw (IO.userError s!"variant query mismatch {text} s={s} window={repr c} got={found1.1}/{found2.1} expected={expected}")
          unless found1.2≤qa && found2.2≤qb do throw (IO.userError "variant query work")
          count:=count+2
          yes:=yes+(if found1.1 then 1 else 0)+(if found2.1 then 1 else 0)
          no:=no+(if found1.1 then 0 else 1)+(if found2.1 then 0 else 1)
  if dispatch then
    let r₁:=P1.execute P text 0 s s 1 0 hs one
    let r₂:=P2.execute P text 0 s s 1 0 hs two
    let expected:=reference P w
    unless r₁.answer=expected.1 && r₂.answer=expected.2 do throw (IO.userError s!"full residual dispatch {text}")
    unless r₁.residualWork≤P1.residualBudget P text.size s s 1 0 &&
        r₂.residualWork≤P2.residualBudget P text.size s s 1 0 do throw (IO.userError "full dispatch ledger")
  return (count,yes,no)

def patterns : List (SevenDFA (Fin 2)) :=
  [⟨all,all,all,all,all,all,all⟩,⟨all,all,positive,all,all,all,all⟩,
   ⟨all,all,all,reset,all,all,all⟩,
   ⟨all,all,all,all,all,all,reject⟩]

-- The G/H selector is tested separately with noninjective transitions:
-- compiling every finite variant of the nested reversals would create an
-- enormous fixed-pattern state universe, unrelated to input length.
def checkSelectors : IO Nat := do
  let P : SevenDFA (Fin 2):=⟨reset,all,all,all,all,reset,reset⟩
  let w : Word (Fin 2):=[0,1,1,0]
  let idx:=prepareSelectors P w
  let mut checks:=0
  for lo in [0:w.length+1] do
    for hi in [lo:w.length+1] do
      for d in [hi-lo:w.length-hi+1] do
        let c:=select idx lo hi d
        unless c.initial==P.A.run P.A.initial (slice w 0 lo) do
          throw (IO.userError "initial selector")
        for q in List.finRange P.G.stateCount do
          unless c.middle.get q==P.G.run q (slice w hi (lo+d)) do
            throw (IO.userError "noninjective gap selector")
        for q in List.finRange P.H.stateCount do
          unless Colors.decode P.H c.tailKey q==P.H.final (P.H.run q (slice w (hi+d) w.length)) do
            throw (IO.userError "noninjective final-subset selector")
        unless c.work≤selectorBudget P w.length do throw (IO.userError "selector ledger")
        checks:=checks+1
  return checks

def main : IO Unit := do
  let began←IO.monoMsNow
  IO.println "residualCached begin; all-start fixture is independent slow cut enumeration"
  (←IO.getStdout).flush
  let selectors←checkSelectors
  IO.println s!"residualCached selectorComparisons={selectors} noninjective=true"
  (←IO.getStdout).flush
  let mut builds:=0
  let mut queries:=0
  let mut yes:=0
  let mut no:=0
  for n in [0:3] do
    for code in [0:2^n] do
      let text:=((List.range n).map fun i : Nat=>if code.testBit i then (1 : Fin 2) else 0).toArray
      for P in patterns do
        for s in [1,3] do
          if hs : 0<s then
            let r←check P text s hs (s==1)
            builds:=builds+2
            queries:=queries+r.1
            yes:=yes+r.2.1
            no:=no+r.2.2
      IO.println s!"residualCached text n={n} code={code} bankBuilds={builds}"
      (←IO.getStdout).flush
    IO.println s!"residualCached n={n} bankBuilds={builds} queryComparisons={queries} positive={yes} negative={no}"
    (←IO.getStdout).flush
  let repeated:=Array.replicate 8 (0 : Fin 2)
  let r←check ⟨all,all,positive,all,all,all,all⟩ repeated 3 (by decide) true
  queries:=queries+r.1
  unless yes>0 && no>0 do throw (IO.userError "missing positive/negative coverage")
  IO.println s!"residualCached complete queries={queries} allEmptyCuts=true deep=8 elapsed={(←IO.monoMsNow)-began}ms"

end ResidualCachedAudit
def main : IO Unit:=ResidualCachedAudit.main
