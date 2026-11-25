import REWB.BoundaryApplicationSeparatedCost
open REWB REWB.BoundaryApplication

/-! Independent source/length/target enumeration. These exhaustive
scans occur only in the audit, never in the index implementation. -/

def machine (seed : Nat) : DFA (Fin 2) :=
  ⟨2,⟨seed%2,by omega⟩,
    fun q c=>⟨(seed/(2^(q.val*2+c.val+1)))%2,by omega⟩,
    fun q=>decide ((seed/(2^(q.val+5)))%2=1)⟩

def allWords : DFA (Fin 2) := ⟨1,0,fun _ _=>0,fun _=>true⟩
def epsilon : DFA (Fin 2) := ⟨2,0,fun _ _=>1,fun q=>decide (q=0)⟩
def nonempty : DFA (Fin 2) := ⟨2,0,fun _ _=>1,fun q=>decide (q=1)⟩
def lastZero : DFA (Fin 2) := ⟨2,1,fun _ c=>c,fun q=>decide (q=0)⟩
def lastOne : DFA (Fin 2) := ⟨2,0,fun _ c=>c,fun q=>decide (q=1)⟩
def even : DFA (Fin 2) := ⟨2,0,fun q _=>⟨1-q.val,by have h:=q.isLt; omega⟩,fun q=>decide (q=0)⟩

def bruteBit (A B C D : DFA (Fin 2)) (w : Word (Fin 2)) (g0 g1 target : Nat) : Bool :=
  decide (g1≤target) && (List.range (g0+1)).any fun source=>
    (List.range (min source (target-g1)+1)).any fun len=>
      decide (Spec.slice w (source-len) source=Spec.slice w (target-len) target) &&
      A.final (A.run A.initial (Spec.slice w 0 (source-len))) &&
      B.final (B.run B.initial (Spec.slice w (source-len) source)) &&
      C.final (C.run C.initial (Spec.slice w source g0)) &&
      D.final (D.run D.initial (Spec.slice w g1 (target-len)))

def brute (A B C D E : DFA (Fin 2)) (w : Word (Fin 2)) (g0 g1 right : Nat) : Bool :=
  (List.range (right+1)).any fun target=>bruteBit A B C D w g0 g1 target &&
    E.final (E.run E.initial (Spec.slice w target right))

structure Stats where
  builds : Nat := 0
  bits : Nat := 0
  queries : Nat := 0
  accepted : Nat := 0
  maximum : Nat := 0
  padding : Nat := 0

def combine (a b : Stats) : Stats :=
  ⟨a.builds+b.builds,a.bits+b.bits,a.queries+b.queries,a.accepted+b.accepted,
    max a.maximum b.maximum,a.padding+b.padding⟩

def check (A B C D E : DFA (Fin 2)) (w : Word (Fin 2)) (g0 g1 : Nat) (h1 : g1≤w.length) : IO Stats := do
  let idx:=Separated.build A B C D E w 0 g0 g1 h1
  unless idx.work≤Separated.bound A B C D E w.length do throw (IO.userError "separated build counter")
  unless idx.endpoints.work≤Separated.bitBound A B C D w.length do throw (IO.userError "separated bit counter")
  unless idx.suffix.length==w.length do throw (IO.userError "cached suffix length")
  unless idx.suffix.height==(w.length+1).log2+1 do throw (IO.userError "cached suffix height")
  let mut out : Stats:=⟨1,0,0,0,0,0⟩
  for target in (List.ofFn id : List (Fin (w.length+1))) do
    let expected:=bruteBit A B C D w g0 g1 target.val
    unless idx.endpoints.bits.get target==expected do
      throw (IO.userError s!"bit mismatch word={w.map Fin.val} g0={g0} g1={g1} t={target.val}")
    out:={out with bits:=out.bits+1}
  for right in List.range (w.length+1) do
    let actual:=Separated.query E idx right
    unless actual.1==brute A B C D E w g0 g1 right do
      throw (IO.userError s!"query mismatch word={w.map Fin.val} g0={g0} g1={g1} right={right}")
    unless actual.2≤((w.length+1).log2+2)*BoundaryIndex.Tree.queryBudget 1 E.stateCount+E.stateCount+2 do
      throw (IO.userError "separated query counter")
    out:={out with
      queries:=out.queries+1
      accepted:=out.accepted+(if actual.1 then 1 else 0)
      maximum:=max out.maximum actual.2}
  for i in List.range (2^idx.suffix.height) do
    if hi : i<2^idx.suffix.height then
      let point:=BoundaryIndex.Merge.point idx.suffix.tree ⟨i,hi⟩
      for q in (List.ofFn id : List (Fin E.stateCount)) do
        let active:=idx.endpoints.bits.getD i false && decide (q=E.initial)
        unless point.active 0 q==active do throw (IO.userError "E marker position/padding mismatch")
        let expected:=if i=0 then q else match w[i-1]? with
          | none=>q
          | some c=>E.step q c
        unless point.trans q==expected do throw (IO.userError "E letter transition/padding mismatch")
      if w.length<i then out:={out with padding:=out.padding+1}
  pure out

def main : IO Unit := do
  let empty←check allWords allWords allWords allWords allWords [] 0 0 (by decide)
  unless empty.accepted==1 do throw (IO.userError "empty epsilon query")
  IO.println "separatedEmpty=true"
  (←IO.getStdout).flush
  let mut stats:=empty
  for n in List.range 4 do
    for code in List.range (2^n) do
      let w : Word (Fin 2):=(List.range n).map fun i=>⟨(code/(2^i))%2,by omega⟩
      for g0 in List.range (n+1) do
        for g1 in List.range (n+1) do
          if g0≤g1 then
            if h1 : g1≤w.length then
              stats:=combine stats (←check allWords allWords allWords allWords allWords w g0 g1 h1)
              stats:=combine stats (←check allWords nonempty even allWords epsilon w g0 g1 h1)
    IO.println s!"separatedExhaustiveLength={n} builds={stats.builds}"
    (←IO.getStdout).flush
  for seed in List.range 32 do
    let n:=seed%11
    let w : Word (Fin 2):=(List.range n).map fun i=>⟨((seed+7)*(i+3)+i/2)%2,by omega⟩
    let a:=(seed*7)%(n+1)
    let b:=(seed*13+1)%(n+1)
    let g0:=min a b
    let g1:=max a b
    if h1 : g1≤w.length then
      if seed%2=0 then
        stats:=combine stats (←check (machine (seed*17+33)) (machine (seed*31+69))
          (machine (seed*43+101)) allWords (machine (seed*53+47)) w g0 g1 h1)
      else
        stats:=combine stats (←check allWords (machine (seed*31+69))
          (machine (seed*43+101)) (machine (seed*47+53)) (machine (seed*53+47)) w g0 g1 h1)
  let gap : Word (Fin 2):=[0,1,0]
  stats:=combine stats (←check epsilon nonempty epsilon epsilon epsilon gap 1 2 (by decide))
  let gapIdx:=Separated.build epsilon nonempty epsilon epsilon epsilon gap 0 1 2 (by decide)
  unless (Separated.query epsilon gapIdx 3).1 do throw (IO.userError "distinct-boundary witness")
  let wrongIdx:=Separated.build epsilon nonempty epsilon epsilon epsilon gap 0 0 2 (by decide)
  if (Separated.query epsilon wrongIdx 3).1 then throw (IO.userError "source boundary ignored")
  let resetWord : Word (Fin 2):=[1,0,1,0]
  stats:=combine stats (←check lastOne nonempty even lastOne epsilon resetWord 2 2 (by decide))
  let resetIdx:=Separated.build lastOne nonempty even lastOne epsilon resetWord 0 2 2 (by decide)
  unless (Separated.query epsilon resetIdx 4).1 do throw (IO.userError "joint noninjective A/D witness")
  IO.println s!"separatedSmallBuilds={stats.builds} bits={stats.bits} queries={stats.queries} accepted={stats.accepted} maxQueryWork={stats.maximum} padding={stats.padding} distinctBoundaries=true noninjective=true"
  (←IO.getStdout).flush
  let w : Word (Fin 2):=List.replicate 512 0
  let idx:=Separated.build allWords allWords allWords allWords allWords w 0 128 384
    (by simp only [w,List.length_replicate]; omega)
  unless idx.work≤Separated.bound allWords allWords allWords allWords allWords w.length do
    throw (IO.userError "deep construction counter")
  for target in (List.ofFn id : List (Fin (w.length+1))) do
    unless idx.endpoints.bits.get target==bruteBit allWords allWords allWords allWords w 128 384 target.val do
      throw (IO.userError "deep endpoint bit")
  for right in [0,127,128,383,384,385,511,512] do
    let q:=Separated.query allWords idx right
    unless q.1==brute allWords allWords allWords allWords allWords w 128 384 right do
      throw (IO.userError "deep suffix query")
    unless q.2≤((w.length+1).log2+2)*BoundaryIndex.Tree.queryBudget 1 1+3 do
      throw (IO.userError "deep query counter")
  let q:=Separated.query allWords idx 512
  IO.println s!"separatedDeepLength=512 deepBits=513 deepQueries=8 buildWork={idx.work} height={idx.suffix.height} queryWork={q.2} exactSlices=true fullPipeline=true"
