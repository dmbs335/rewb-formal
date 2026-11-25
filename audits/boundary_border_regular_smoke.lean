import REWB.BoundaryBorderRegularRegression

/-! Independent bounded runtime audit of the complete text-built regular
border query. Literal slices and exponent scans occur only in this test.
Production queries reuse one suffix index and three DFA range indices. -/
open REWB REWB.BoundaryBorder REWB.BoundaryBorder.Regular

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def machine (code : Nat) : DFA (Fin 2) where
  stateCount:=2
  initial:=⟨(code/16)%2,by omega⟩
  step q c:=⟨(code/2^(2*q.val+c.val))%2,by omega⟩
  final q:=decide ((code/2^(5+q.val))%2=1)

private def accept (d : DFA (Fin 2)) (w : Word (Fin 2)) : Bool := d.final (d.run d.initial w)

private def reference (A B E : DFA (Fin 2)) (w : Word (Fin 2)) (a j r : Nat) : Bool :=
  (List.range a).any fun p=>
    let t:=j+(a-p)
    decide (t≤r) && decide (Spec.slice w p a=Spec.slice w j t) &&
      accept A (Spec.slice w 0 p) && accept B (Spec.slice w p a) && accept E (Spec.slice w t r)

private def orbit (code : Nat) : Orbit 2 :=
  ⟨Vector.ofFn (fun q=>⟨((code/8)/2^q.val)%2,by omega⟩),
    ⟨(code/4)%2,by omega⟩,Vector.ofFn (fun q=>decide (((code%4)/2^q.val)%2=1))⟩

private def checkOrbits : IO Unit := do
  let mut checked:=0
  let mut maxWork:=0
  for i in [:32] do
    let before:=orbit i
    let compressed:=Counted.compress before
    require (compressed.2≤Counted.orbitBudget 2) "counted orbit construction"
    for j in [0,3,5,9,12,19,27,31] do
      let after:=orbit j
      let base:=Counted.solve before after 0 0
      for m in [0,1,2,5,11,31] do
        let out:=Counted.solve before after 0 m
        let wanted:=(List.range (m+1)).any fun k=>before.data.test k && after.data.test (m-k)
        require (out.1==wanted) s!"orbit solver i={i} j={j} m={m}"
        require (out.2==base.2) "literal-independent orbit solver work"
        let pair:=Counted.pair before after 0 m
        require (pair.2≤Counted.pairBudget 2 2) "counted formula construction"
        maxWork:=max maxWork out.2
        checked:=checked+1
      let large:=Counted.solve before after 0 100000000
      let finite:=Counted.solve before after 0 100
      require (large.1==finite.1 && large.2==base.2) "large exponent does not change solver traversal"
  IO.println s!"borderRegularOrbits checks={checked} maxWork={maxWork} hugeExponent=100000000 independentWork=true"
  (←IO.getStdout).flush

private def checkAlignment : IO Unit := do
  let mut checked:=0
  for first in [:7] do
    for q in [:6] do
      for lo in [:9] do
        for hi in [:9] do
          let out:=align first q lo hi
          require (out.2≤14) "alignment work"
          if q=0 then require out.1.isNone "zero-step rejection"
          else
            for p in [:16] do
              let got:=match out.1 with
                | none=>false
                | some (start,m)=>(List.range (m+1)).any fun k=>p==start+k*q
              let wanted:=decide (lo≤p ∧ p≤hi ∧ first≤p ∧ (p-first)%q=0)
              require (got==wanted) s!"alignment first={first} q={q} lo={lo} hi={hi} p={p}"
              checked:=checked+1
  IO.println s!"borderRegularAlignment checks={checked} emptyWindows=true residueClipping=true"
  (←IO.getStdout).flush

private structure Stats where
  texts : Nat := 0
  queries : Nat := 0
  accepted : Nat := 0
  rejected : Nat := 0
  maxWork : Nat := 0

private def small (n samples fixed : Nat) (stats : Stats) : IO Stats := do
  let mut stats:=stats
  for code in [:samples] do
    let w : Word (Fin 2):=List.ofFn fun i : Fin n=>⟨(code/2^i.val)%2,by omega⟩
    let wi:=WindowIndex.prepare w.toArray 0
    stats:={stats with texts:=stats.texts+1}
    for (ac,bc,ec) in [(96,96,96),(47,96,47),(35,74,78),(78,35,74)] do
      let A:=machine ac
      let B:=machine bc
      let E:=machine ec
      let ai:=BoundaryApplication.Range.build A w
      let bi:=BoundaryApplication.Range.build B w
      let ei:=BoundaryApplication.Range.build E w
      for a in [:n+1] do
        for j in [:n+1] do
          if hj : j<w.toArray.size+1 then
            for r in [:n+1] do
              let out:=dyadic A B E wi ai bi ei a ⟨j,hj⟩ r
              let wanted:=reference A B E w a j r
              require (out.1==wanted) s!"full query w={w.map Fin.val} A={ac} B={bc} E={ec} a={a} j={j} r={r} got={out.1} want={wanted}"
              require (out.2≤(2*fixed+521)*((n+1).log2+1)^2) "full query closed counter"
              stats:={stats with
                queries:=stats.queries+1
                accepted:=stats.accepted+(if out.1 then 1 else 0)
                rejected:=stats.rejected+(if out.1 then 0 else 1)
                maxWork:=max stats.maxWork out.2}
  IO.println s!"borderRegularLength n={n} texts={stats.texts} queries={stats.queries} accepted={stats.accepted} maxWork={stats.maxWork}"
  (←IO.getStdout).flush
  pure stats

private def deep (n period : Nat) : IO Unit := do
  let w : Word (Fin 2):=List.ofFn fun i : Fin n=>⟨(if period=1 then 0 else (i.val%period)/2)%2,by omega⟩
  let d:=Regular.Regression.allWords
  let wi:=WindowIndex.prepare w.toArray 0
  let di:=BoundaryApplication.Range.build d w
  let fixed:=fixedBudget d d d
  let mut checked:=0
  let mut maxWork:=0
  for a in [0,n/3,n/2,n] do
    for j in [0,n/4,n/2,n] do
      if hj : j<w.toArray.size+1 then
        for r in [j,min n (j+n/3),n] do
          let out:=dyadic d d d wi di di di a ⟨j,hj⟩ r
          require (out.1==reference d d d w a j r) "deep exact slices"
          require (out.2≤(2*fixed+521)*((n+1).log2+1)^2) "deep closed counter"
          checked:=checked+1
          maxWork:=max maxWork out.2
  IO.println s!"borderRegularDeep n={n} period={period} queries={checked} scales={wi.scales} maxWork={maxWork} fixedBudget={fixed} exactSlices=true"
  (←IO.getStdout).flush

def main : IO Unit := do
  checkAlignment
  checkOrbits
  IO.println "borderRegular computing fixed two-state proof budget once"
  (←IO.getStdout).flush
  let d:=machine 0
  let fixed:=fixedBudget d d d
  IO.println s!"borderRegular fixedTwoStateBudget={fixed}"
  (←IO.getStdout).flush
  let mut stats : Stats:={}
  for n in [:5] do stats←small n (2^n) fixed stats
  stats←small 5 16 fixed stats
  stats←small 6 16 fixed stats
  require (0<stats.accepted && 0<stats.rejected) "positive and negative coverage"
  IO.println s!"borderRegularTotal texts={stats.texts} queries={stats.queries} accepted={stats.accepted} rejected={stats.rejected} maxWork={stats.maxWork} empty=true clipping=true noninjective=true"
  (←IO.getStdout).flush
  deep 512 1
  deep 513 3
