import REWB.ShortOuterRegression

/-! Independent literal-cut scans are audit references only.  The actual
solvers below execute their shared tables and measured concrete joins. -/
open REWB REWB.ShortOuter
open REWB.ShortOuter.Band.Regression
open REWB.ShortOuter.Regression

private def accept (A : DFA (Fin 2)) (w : Word (Fin 2)) : Bool := A.final (A.run A.initial w)

private def inner1 (P : SevenDFA (Fin 2)) (w : Word (Fin 2)) (p e : Nat) : Bool := Id.run do
  for i in [0:p+1] do
    for a in [i:p+1] do
      if accept P.A (Spec.slice w 0 i) && accept P.B (Spec.slice w i a) &&
          accept P.C (Spec.slice w a p) then
        for j in [p:e+1] do
          let t:=j+(a-i)
          if t≤e && Spec.slice w i a==Spec.slice w j t &&
              accept P.D (Spec.slice w p j) && accept P.F (Spec.slice w t e) then
            return true
  return false

private def inner2 (P : SevenDFA (Fin 2)) (w : Word (Fin 2)) (p e : Nat) : Bool := Id.run do
  if !accept P.A (Spec.slice w 0 p) then return false
  for i in [p:e+1] do
    for a in [i:e+1] do
      if accept P.B (Spec.slice w p i) && accept P.C (Spec.slice w i a) then
        for j in [a:e+1] do
          let t:=j+(a-i)
          if t≤e && Spec.slice w i a==Spec.slice w j t &&
              accept P.D (Spec.slice w a j) && accept P.F (Spec.slice w t e) then
            return true
  return false

private def reference (P : SevenDFA (Fin 2)) (w : Word (Fin 2)) (L : Nat) : Bool×Bool := Id.run do
  let mut one:=false
  let mut two:=false
  for p in [0:w.length+1] do
    for len in [0:min L (w.length-p+1)] do
      let e:=p+len
      for k in [e:w.length-len+1] do
        if Spec.slice w p e==Spec.slice w k (k+len) &&
            accept P.G (Spec.slice w e k) && accept P.H (Spec.slice w (k+len) w.length) then
          one:=one || inner1 P w p e
          two:=two || inner2 P w p e
          if one && two then return (true,true)
  return (one,two)

private def binary (n code : Nat) : Array (Fin 2) :=
  ((List.range n).map (fun i=>if Nat.testBit code i then one else zero)).toArray

private def even : DFA (Fin 2) :=
  ⟨2,zero,fun q _=>⟨1-q.val,by omega⟩,fun q=>decide (q=zero)⟩
private def reject : DFA (Fin 2) := ⟨1,⟨0,by decide⟩,fun _ _=>⟨0,by decide⟩,fun _=>false⟩
private def automata : Array (DFA (Fin 2)) := #[any,eps,nonempty,lastOne,even,reject]

private def patterns : List (SevenDFA (Fin 2)) :=
  [emptyPattern,anyPattern,gapPattern,earlierPattern,
   ⟨any,any,nonempty,any,any,any,any⟩,
   ⟨lastOne,even,any,eps,any,lastOne,eps⟩,
   ⟨any,lastOne,even,any,lastOne,any,even⟩,
   ⟨nonempty,nonempty,nonempty,nonempty,nonempty,nonempty,nonempty⟩]++
  (List.range 8).map (fun i=>
    ⟨automata[i%6]?.getD any,automata[(2*i+1)%6]?.getD any,
     automata[(3*i+2)%6]?.getD any,automata[(5*i+3)%6]?.getD any,
     automata[(i+4)%6]?.getD any,automata[(2*i+5)%6]?.getD any,
     automata[(5*i+1)%6]?.getD any⟩)

private def require (b : Bool) (msg : String) : IO Unit := unless b do throw (IO.userError msg)

private def check (P : SevenDFA (Fin 2)) (text : Array (Fin 2)) (L tag : Nat) : IO (Bool×Bool) := do
  let got1:=P1.solve P text zero L
  let got2:=P2.solve P text zero L
  let expected:=reference P text.toList L
  require (got1.answer==expected.1 && got2.answer==expected.2)
    s!"short solver mismatch text={text} L={L} pattern={tag} p1={got1.answer}/{expected.1} p2={got2.answer}/{expected.2}"
  require (got1.work≤P1.budget P text.size L && got2.work≤P2.budget P text.size L)
    s!"short solver work bound text={text} L={L} pattern={tag}"
  return expected

def main : IO Unit := do
  let started←IO.monoMsNow
  IO.println "shortOuterBegin"
  (←IO.getStdout).flush
  let mut texts:=0
  let mut checks:=0
  let mut yes1:=0
  let mut yes2:=0
  for n in [0:6] do
    for code in [0:2^n] do
      let text:=binary n code
      texts:=texts+1
      for L in [0:n+4] do
        for tag in [0:patterns.length] do
          let P:=patterns[tag]?.getD anyPattern
          let r←check P text L tag
          checks:=checks+2
          if r.1 then yes1:=yes1+1
          if r.2 then yes2:=yes2+1
    IO.println s!"shortOuter n={n} texts={texts} comparisons={checks} yesP1={yes1} yesP2={yes2}"
    (←IO.getStdout).flush
  let far←check earlierPattern earlierText 2 100
  require far.1 "unrestricted earlier P1 source lost"
  require ((P1.solve earlierPattern earlierText zero 1).answer==false) "strict outer limit P1"
  require ((P2.solve earlierPattern #[zero,zero] zero 1).answer==false) "strict outer limit P2"
  for (n,L) in [(512,16),(1024,8)] do
    let text:=Array.replicate n zero
    let a:=P1.solve anyPattern text zero L
    let b:=P2.solve anyPattern text zero L
    require (a.answer && b.answer && a.work≤P1.budget anyPattern n L && b.work≤P2.budget anyPattern n L)
      s!"deep short solver failed n={n} L={L}"
    IO.println s!"shortOuterDeep n={n} L={L} P1work={a.work} P2work={b.work}"
    (←IO.getStdout).flush
  let farText:=([zero]++List.replicate 1024 one++[zero,zero]).toArray
  let a:=P1.solve earlierPattern farText zero 2
  let b:=P2.solve earlierPattern farText zero 2
  require (a.answer && !b.answer && a.work≤P1.budget earlierPattern farText.size 2 &&
    b.work≤P2.budget earlierPattern farText.size 2) "deep absolute earlier source"
  require (yes1>0 && yes2>0 && yes1<checks/2 && yes2<checks/2) "positive/negative coverage absent"
  let ended←IO.monoMsNow
  IO.println s!"shortOuterComplete texts={texts} comparisons={checks} yesP1={yes1} yesP2={yes2} mismatches=0 elapsed={ended-started}ms"
