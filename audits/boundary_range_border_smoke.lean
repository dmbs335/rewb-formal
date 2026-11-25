import REWB.BoundaryRangeNearIndexBorderRegression
open REWB REWB.BoundaryRange REWB.BoundaryRange.NearIndex

def allWords : DFA (Fin 2) := ⟨1,0,fun _ _=>0,fun _=>true⟩
def epsilon : DFA (Fin 2) := ⟨2,0,fun _ _=>1,fun q=>decide (q=0)⟩
def nonempty : DFA (Fin 2) := ⟨2,0,fun _ _=>1,fun q=>decide (q=1)⟩
def reset : DFA (Fin 2) := ⟨2,0,fun _ c=>c,fun q=>decide (q=1)⟩
def even : DFA (Fin 2) := ⟨2,0,fun q _=>⟨1-q.val,by have h:=q.isLt; omega⟩,fun q=>decide (q=0)⟩

def accepts (D : DFA (Fin 2)) (w : Word (Fin 2)) (lo hi : Nat) : Bool :=
  D.final (D.run D.initial (Spec.slice w lo hi))

def copyReference (A B E : DFA (Fin 2)) (w : Word (Fin 2)) (a j right : Nat) : Bool :=
  (List.range (a+1)).any fun L=>decide (j+L≤right) &&
    decide (Spec.slice w (a-L) a=Spec.slice w j (j+L)) &&
    accepts A w 0 (a-L) && accepts B w (a-L) a && accepts E w (j+L) right

def gapReference (C K D : DFA (Fin 2)) (w : Word (Fin 2)) (left a j : Nat) : Bool :=
  (List.range (j+1)).any fun p=>decide (a≤p ∧ left≤p) &&
    accepts C w a p && accepts K w left p && accepts D w p j

/-- Original p/a/j/L coordinates; the production gap/AP selectors do
not occur in this reference. `borderOnly=false` checks all four regions. -/
def reference (A B C K D E : DFA (Fin 2)) (w : Word (Fin 2))
    (left right g0 g : Nat) (borderOnly : Bool) : Bool :=
  (List.range (right+1)).any fun p=>decide (left≤p ∧ p<g) && accepts K w left p &&
    (List.range (p+1)).any fun a=>accepts C w a p &&
      (List.range (right+1)).any fun j=>decide (p≤j) &&
        (!borderOnly || decide (g0<a ∧ j<g)) && accepts D w p j && copyReference A B E w a j right

structure Stats where
  builds : Nat := 0
  copies : Nat := 0
  gaps : Nat := 0
  queries : Nat := 0
  positive : Nat := 0
  maximum : Nat := 0

def addStats (a b : Stats) : Stats :=
  ⟨a.builds+b.builds,a.copies+b.copies,a.gaps+b.gaps,a.queries+b.queries,
    a.positive+b.positive,max a.maximum b.maximum⟩

def check (A B C K D E : DFA (Fin 2)) (w : Word (Fin 2)) : IO Stats := do
  let idx:=Border.build A B C K D E w 0
  unless idx.work≤Border.buildBound A B C K D E w.length do throw (IO.userError "border build work")
  let copyBound:=Border.copyBudget A B E w.length
  let gapBound:=Border.gapBudget C K D w.length
  let atBound:=copyBound+gapBound+3
  let mut s : Stats:={builds:=1}
  for a in List.range (w.length+1) do
    for j in (List.ofFn id : List (Fin (w.toArray.size+1))) do
      for right in List.range (w.length+1) do
        if j.val≤right then
          let out:=Border.copy idx a j right
          unless out.1==copyReference A B E w a j.val right do
            throw (IO.userError s!"border copy word={w.map Fin.val} a={a} j={j.val} right={right}")
          unless out.2≤copyBound do throw (IO.userError "border copy work")
          s:={s with copies:=s.copies+1}
    for left in List.range (w.length+1) do
      for j in List.range (w.length+1) do
        if a≤j && left≤j then
          let out:=Border.gap idx left a j
          unless out.1==gapReference C K D w left a j do
            throw (IO.userError s!"border gap word={w.map Fin.val} left={left} a={a} j={j}")
          unless out.2≤gapBound do throw (IO.userError "border gap work")
          s:={s with gaps:=s.gaps+1}
  for g0 in List.range (w.length+1) do
    for g in List.range (w.length+1) do
      if g0≤g then
        for left in List.range (w.length+1) do
          if g0≤left && left≤g then
            for right in List.range (w.length+1) do
              let out:=Border.query idx left right g0 g
              unless out.1==reference A B C K D E w left right g0 g true do
                throw (IO.userError s!"border region word={w.map Fin.val} g0={g0} g={g} left={left} right={right}")
              unless out.2≤(g-g0)*((g-g0)*(atBound+3)+4)+1 do
                throw (IO.userError "border region work")
              s:={s with
                queries:=s.queries+1
                positive:=s.positive+(if out.1 then 1 else 0)
                maximum:=max s.maximum out.2}
  pure s

def checkFull (A B C K D E : DFA (Fin 2)) (w : Word (Fin 2)) (g0 g : Nat)
    (h0g : g0≤g) (hg : g≤w.length) : IO Nat := do
  let idx:=Full.build A B C K D E w 0 g0 g h0g hg
  unless idx.work≤NearIndex.buildBound A B C K D E w.length+Border.buildBound A B C K D E w.length+1 do
    throw (IO.userError "all-four build work")
  let borderBound:=Border.queryBudget A B C K D E w.length (g-g0)
  let mut count:=0
  for left in List.range (g+1) do
    if g0≤left then
      let queryBound:=NearIndex.threeBudget A B C K D E w.length (g-left) (g-g0)+borderBound+1
      for right in List.range (w.length+1) do
        let out:=Full.query idx left right
        unless out.1==reference A B C K D E w left right g0 g false do
          throw (IO.userError s!"all-four word={w.map Fin.val} g0={g0} g={g} left={left} right={right}")
        unless out.2≤queryBound do throw (IO.userError "all-four query work")
        count:=count+1
  pure count

def main : IO Unit := do
  let mut total : Stats:={}
  for n in List.range 3 do
    for code in List.range (2^n) do
      let w : Word (Fin 2):=(List.range n).map fun i=>⟨(code/(2^i))%2,by omega⟩
      total:=addStats total (←check allWords allWords allWords allWords allWords allWords w)
      total:=addStats total (←check allWords nonempty epsilon allWords allWords epsilon w)
      total:=addStats total (←check allWords allWords epsilon nonempty allWords allWords w)
    IO.println s!"borderIndexExhaustive length={n} builds={total.builds} queries={total.queries}"
    (←IO.getStdout).flush
  let fixture : Word (Fin 2):=[0,1,0]
  total:=addStats total (←check epsilon nonempty epsilon allWords nonempty epsilon fixture)
  total:=addStats total (←check even nonempty reset allWords nonempty even fixture)
  IO.println s!"borderIndexTotal builds={total.builds} copies={total.copies} gaps={total.gaps} queries={total.queries} accepted={total.positive} maxWork={total.maximum}"
  (←IO.getStdout).flush
  let mut full:=0
  full:=full+(←checkFull allWords allWords allWords allWords allWords allWords [] 0 0 (by decide) (by decide))
  for g0 in List.range 4 do
    for g in List.range 4 do
      if h0g : g0≤g then
        if hg : g≤fixture.length then
          full:=full+(←checkFull allWords allWords allWords allWords allWords allWords fixture g0 g h0g hg)
  full:=full+(←checkFull epsilon nonempty epsilon allWords nonempty epsilon fixture 0 3 (by decide) (by decide))
  IO.println s!"borderIndexAllFour queries={full} exactAt=true"
  (←IO.getStdout).flush
  let w : Word (Fin 2):=(List.range 128).map fun i=>⟨i%2,by omega⟩
  let idx:=Border.build allWords allWords allWords allWords allWords allWords w 0
  unless idx.work≤Border.buildBound allWords allWords allWords allWords allWords allWords w.length do
    throw (IO.userError "border deep build work")
  let deepBound:=Border.queryBudget allWords allWords allWords allWords allWords allWords w.length 4
  let mut deep:=0
  let mut maximum:=0
  for left in [62,63,64,66] do
    for right in [64,66,80,128] do
      let out:=Border.query idx left right 62 66
      unless out.1==reference allWords allWords allWords allWords allWords allWords w left right 62 66 true do
        throw (IO.userError "border deep exact slices")
      unless out.2≤deepBound do
        throw (IO.userError "border deep work")
      deep:=deep+1
      maximum:=max maximum out.2
  IO.println s!"borderIndexDeep n=128 buildWork={idx.work} queries={deep} maxWork={maximum} exactSlices=true"
