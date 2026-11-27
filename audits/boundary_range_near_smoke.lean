import REWB.BoundaryRangeNearIndexRegression
open REWB REWB.BoundaryRange REWB.BoundaryRange.NearIndex
set_option maxRecDepth 10000

/-! Independent enumeration of the original four endpoints and capture
length. These scans are audit-only. Every tested production query uses
one already-built eager table for its fixed boundary pair. -/

def allWords : DFA (Fin 2) := ⟨1,0,fun _ _=>0,fun _=>true⟩
def epsilon : DFA (Fin 2) := ⟨2,0,fun _ _=>1,fun q=>decide (q=0)⟩
def nonempty : DFA (Fin 2) := ⟨2,0,fun _ _=>1,fun q=>decide (q=1)⟩
def reset : DFA (Fin 2) := ⟨2,0,fun _ c=>c,fun q=>decide (q=1)⟩
def even : DFA (Fin 2) := ⟨2,0,fun q _=>⟨1-q.val,by have h:=q.isLt; omega⟩,fun q=>decide (q=0)⟩
def machine (seed : Nat) : DFA (Fin 2) :=
  ⟨2,⟨seed%2,by omega⟩,fun q c=>⟨(seed/(2^(q.val*2+c.val+1)))%2,by omega⟩,
    fun q=>decide ((seed/(2^(q.val+5)))%2=1)⟩

def accepts (D : DFA (Fin 2)) (w : Word (Fin 2)) (lo hi : Nat) : Bool :=
  D.final (D.run D.initial (Spec.slice w lo hi))

def brute (A B C K D E : DFA (Fin 2)) (w : Word (Fin 2))
    (g0 g left right : Nat) (kind : Nat) : Bool :=
  (List.range (g-left)).any fun offset=>
    let p:=left+offset
    accepts K w left p && (List.range (p+1)).any fun a=>
      accepts C w a p && (List.range (right+1-p)).any fun jump=>
        let j:=p+jump
        let region:=if kind=0 then decide (a≤g0 ∧ g≤j)
          else if kind=1 then decide (g0<a ∧ g≤j)
          else decide (a≤g0 ∧ j<g)
        region && accepts D w p j && (List.range (min a (right-j)+1)).any fun L=>
          decide (j+L≤right) && decide (Spec.slice w (a-L) a=Spec.slice w j (j+L)) &&
          accepts A w 0 (a-L) && accepts B w (a-L) a && accepts E w (j+L) right

structure Stats where
  builds : Nat := 0
  queries : Nat := 0
  keyBits : Nat := 0
  separated : Nat := 0
  ends : Nat := 0
  starts : Nat := 0
  maximum : Nat := 0

def addStats (a b : Stats) : Stats :=
  ⟨a.builds+b.builds,a.queries+b.queries,a.keyBits+b.keyBits,a.separated+b.separated,
    a.ends+b.ends,a.starts+b.starts,max a.maximum b.maximum⟩

def check (A B C K D E : DFA (Fin 2)) (w : Word (Fin 2)) (g0 g : Nat)
    (h0g : g0≤g) (hg : g≤w.length) : IO Stats := do
  let idx:=NearIndex.build A B C K D E w 0 g0 g h0g hg
  unless idx.work≤buildBound A B C K D E w.length do throw (IO.userError "near build work")
  unless idx.lower==g0 && idx.upper==g && idx.length==w.length && idx.height==w.length.log2+2 do
    throw (IO.userError "near cached coordinates")
  let mut s : Stats:={builds:=1}
  for offset in List.range (g+1-g0) do
    let p:=g0+offset
    let c:=cKey idx p
    unless c.2≤cBudget C w.length do throw (IO.userError "C selector work")
    for q in (List.ofFn id : List (Fin C.stateCount)) do
      unless BoundaryIndex.Colors.decode C c.1 q==C.final (C.run q (Spec.slice w g0 p)) do
        throw (IO.userError "C final subset")
      s:={s with keyBits:=s.keyBits+1}
    let d:=dKey idx p
    unless d.1==D.run D.initial (Spec.slice w p g) do throw (IO.userError "D initial state")
    unless d.2≤dBudget D w.length do throw (IO.userError "D selector work")
  for offset in List.range (g+1-g0) do
    let left:=g0+offset
    for right in List.range (w.length+1) do
      let a:=querySeparated idx left right
      let b:=queryEnd idx left right
      let c:=queryStart idx left right
      unless a.1==brute A B C K D E w g0 g left right 0 do
        throw (IO.userError s!"near separated word={w.map Fin.val} g0={g0} g={g} left={left} right={right}")
      unless b.1==brute A B C K D E w g0 g left right 1 do
        throw (IO.userError s!"near end word={w.map Fin.val} g0={g0} g={g} left={left} right={right}")
      unless c.1==brute A B C K D E w g0 g left right 2 do
        throw (IO.userError s!"near start word={w.map Fin.val} g0={g0} g={g} left={left} right={right}")
      let all:=queryThree idx left right
      unless all.1==(a.1 || b.1 || c.1) && all.2==a.2+b.2+c.2+2 do
        throw (IO.userError "three cached scans/counter")
      unless all.2≤threeBudget A B C K D E w.length (g-left) (g-g0) do
        throw (IO.userError "three scans work bound")
      s:={s with
        queries:=s.queries+1
        separated:=s.separated+(if a.1 then 1 else 0)
        ends:=s.ends+(if b.1 then 1 else 0)
        starts:=s.starts+(if c.1 then 1 else 0)
        maximum:=max s.maximum all.2}
  pure s

def main (args : List String) : IO Unit := do
  let full:=args.contains "--full"
  let slots : Table.Index (fun i : Fin 4096=>Vector Nat (i.val%7+1)):=
    Table.build fun i=>(Vector.ofFn (fun j=>i.val*10+j.val),i.val%7+3)
  for i in (List.ofFn id : List (Fin 4096)) do
    let row:=Table.get slots i
    for j in (List.ofFn id : List (Fin (i.val%7+1))) do
      unless row.get j==i.val*10+j.val do throw (IO.userError "dependent table lookup")
  IO.println s!"nearDependent slots=4096 work={slots.work} payloads=true"
  let mut total : Stats:={}
  for n in List.range (if full then 4 else 3) do
    for code in List.range (2^n) do
      let w : Word (Fin 2):=(List.range n).map fun i=>⟨(code/(2^i))%2,by omega⟩
      for g0 in List.range (n+1) do
        for g in List.range (n+1) do
          if h0g : g0≤g then
            if hg : g≤w.length then
              total:=addStats total (←check allWords allWords allWords allWords allWords allWords w g0 g h0g hg)
              total:=addStats total (←check allWords nonempty reset even even epsilon w g0 g h0g hg)
    IO.println s!"nearExhaustive length={n} builds={total.builds} queries={total.queries}"
    (←IO.getStdout).flush
  for seed in List.range (if full then 20 else 6) do
    let n:=seed%(if full then 8 else 4)
    let w : Word (Fin 2):=(List.range n).map fun i=>⟨((seed+3)*(i+5)+i/2)%2,by omega⟩
    let g0:=(seed*3)%(n+1)
    let g:=max g0 ((seed*5+2)%(n+1))
    if hg : g≤w.length then
      total:=addStats total (←check (machine (seed*17+33)) (machine (seed*31+69))
        (machine (seed*43+101)) (machine (seed*53+47)) (machine (seed*47+53))
        (machine (seed*59+73)) w g0 g (Nat.le_max_left _ _) hg)
  let fixture : Word (Fin 2):=[0,1,0]
  total:=addStats total (←check epsilon nonempty epsilon allWords nonempty epsilon fixture 1 2 (by decide) (by decide))
  total:=addStats total (←check epsilon nonempty epsilon allWords nonempty epsilon fixture 0 2 (by decide) (by decide))
  total:=addStats total (←check epsilon nonempty epsilon allWords nonempty epsilon fixture 1 3 (by decide) (by decide))
  IO.println s!"nearTotal builds={total.builds} queries={total.queries} physicalComparisons={3*total.queries} keyBits={total.keyBits} separated={total.separated} ends={total.ends} starts={total.starts} maxWork={total.maximum}"
  (←IO.getStdout).flush
  let w : Word (Fin 2):=(List.range 128).map fun i=>⟨i%2,by omega⟩
  let deep←check allWords allWords allWords allWords allWords allWords w 62 66 (by decide) (by decide)
  IO.println s!"nearDeep n=128 queries={deep.queries} keyBits={deep.keyBits} maxWork={deep.maximum} exactSlices=true"
