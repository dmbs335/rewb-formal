import REWB.BoundaryBorderWindowRegression

/-! Independent literal substring reference for the actual prepared
suffix/locus, ordered-window and dyadic period-break query path. -/
open REWB REWB.BoundaryBorder

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def inChoice (choice : Choice) (p : Nat) : Bool :=
  match choice with
  | .empty => false
  | .point q => p==q
  | .progression first step lo hi => decide (Member first step lo hi p)

private def inRow (row : Window.Selected) (p : Nat) : Bool :=
  inChoice row.first p || inChoice row.second p

private def inBand (band : Option Window.Band) (p : Nat) : Bool :=
  match band with
  | none => false
  | some b => decide (Member b.first b.step b.first b.last p)

private def equal (text : Array (Fin 2)) (p j len : Nat) : Bool :=
  p+len≤text.size && j+len≤text.size && text.extract p (p+len)==text.extract j (j+len)

private structure Stats where
  texts : Nat := 0
  queries : Nat := 0
  physical : Nat := 0
  rows : Nat := 0
  points : Nat := 0
  progressions : Nat := 0
  empties : Nat := 0
  windows : Nat := 0
  windowChecks : Nat := 0
  doubleComponents : Nat := 0
  maxWork : Nat := 0

private def countChoice (stats : Stats) : Choice→Stats
  | .empty => {stats with empties:=stats.empties+1}
  | .point _ => {stats with points:=stats.points+1}
  | .progression _ _ _ _ => {stats with progressions:=stats.progressions+1}

private def checkQuery (text : Array (Fin 2))
    (idx : WindowIndex.Index text.size (MaskedSuffixClass.height text.size))
    (a j : Nat) (hj : j<text.size+1) (stats : Stats) : IO Stats := do
  let out:=Dyadic.query idx a ⟨j,hj⟩
  require (out.work≤317*((text.size+1).log2+1)^2+3) "dyadic query work"
  require (out.rows.length==idx.scales) "dyadic cached scale count"
  let mut stats:={stats with queries:=stats.queries+1,maxWork:=max stats.maxWork out.work}
  let mut L:=1
  for row in out.rows do
    stats:=countChoice (countChoice stats row.first) row.second
    for p in [:text.size+2] do
      let want:=p≤a && L≤a-p && a-p<2*L && equal text p j (a-p)
      unless inRow row p==want do
        throw (IO.userError s!"scale text={text.toList.map Fin.val} a={a} j={j} L={L} p={p} row={repr row}")
      stats:={stats with physical:=stats.physical+1}
    stats:={stats with rows:=stats.rows+1}
    L:=2*L
  for p in [:text.size+2] do
    let got:=out.rows.any (fun row=>inRow row p)
    let want:=p<a && equal text p j (a-p)
    unless got==want do
      throw (IO.userError s!"query text={text.toList.map Fin.val} a={a} j={j} p={p}")
    stats:={stats with physical:=stats.physical+1}
  pure stats

private def checkWindows (text : Array (Fin 2))
    (idx : WindowIndex.Index text.size (MaskedSuffixClass.height text.size)) (stats : Stats) : IO Stats := do
  let mut stats:=stats
  for j in [:text.size+1] do
    if hj : j<text.size+1 then
      for L in [1:text.size-j+1] do
        let found:=MaskedSuffixClass.query idx.classes ⟨j,hj⟩ L
        match found.value with
        | none => throw (IO.userError "valid class missing")
        | some out =>
          for lo in [:text.size+1] do
            for hi in [lo,min text.size (lo+L-1),text.size,lo-1] do
              if hi-lo<L then
                let got:=Window.extract idx.classes.suffix.trie.prepared.ranks out.record.state.tree
                  idx.capacity idx.length L lo hi
                require (got.work≤28*MaskedSuffixClass.height text.size+26*(text.size.log2+1)+71) "window counter"
                stats:={stats with
                  windows:=stats.windows+1
                  doubleComponents:=stats.doubleComponents+(if got.second.isSome then 1 else 0)}
                for p in [:text.size+2] do
                  let actual:=inBand got.first p || inBand got.second p
                  let want:=lo≤p && p≤hi && equal text p j L
                  require (actual==want) s!"window n={text.size} j={j} L={L} lo={lo} hi={hi} p={p}"
                  stats:={stats with windowChecks:=stats.windowChecks+1}
  pure stats

private def deep (n kind : Nat) : IO Unit := do
  let text : Array (Fin 2):=Array.ofFn fun i : Fin n=>
    ⟨(if kind=0 then 0 else if kind=1 then i.val%2 else if i.val<3*n/4 then (i.val%3)/2 else 0)%2,by omega⟩
  let idx:=WindowIndex.prepare text 0
  require (idx.work≤(32*(2+2)+836)*(text.size+1)*((text.size+1).log2+1)^2) "deep build counter"
  let mut stats : Stats:={}
  for a in [0,n/3,n/2,n] do
    for j in [0,n/4,n/2,n] do
      if hj : j<text.size+1 then stats←checkQuery text idx a j hj stats
  IO.println s!"borderWindowDeep n={n} kind={kind} buildWork={idx.work} scales={idx.scales} queries={stats.queries} physical={stats.physical} maxWork={stats.maxWork} exactSlices=true"

def main : IO Unit := do
  let mut stats : Stats:={}
  for n in [:8] do
    for code in [:2^n] do
      let text : Array (Fin 2):=Array.ofFn fun i : Fin n=>⟨(code/2^i.val)%2,by omega⟩
      let idx:=WindowIndex.prepare text 0
      require (idx.length==text.size && idx.capacity==2^MaskedSuffixClass.height text.size) "cached metadata"
      require (idx.work≤(32*(2+2)+836)*(text.size+1)*((text.size+1).log2+1)^2) "build counter"
      stats:={stats with texts:=stats.texts+1}
      for a in [:n+1] do
        for j in [:n+1] do
          if hj : j<text.size+1 then stats←checkQuery text idx a j hj stats
      if n≤5 then stats←checkWindows text idx stats
    IO.println s!"borderWindowLength={n} texts={stats.texts} queries={stats.queries} physical={stats.physical}"
    (←IO.getStdout).flush
  require (0<stats.doubleComponents && 0<stats.points && 0<stats.progressions) "component/choice coverage"
  IO.println s!"borderWindowTotal texts={stats.texts} queries={stats.queries} rows={stats.rows} physical={stats.physical} points={stats.points} progressions={stats.progressions} empties={stats.empties} windows={stats.windows} windowChecks={stats.windowChecks} doubleComponents={stats.doubleComponents} maxWork={stats.maxWork}"
  (←IO.getStdout).flush
  for kind in [:3] do deep 1024 kind
