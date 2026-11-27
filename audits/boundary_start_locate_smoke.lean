import REWB.BoundaryApplicationStartLocateIndex
open REWB.BoundaryApplication.StartLocate

/-! Runtime reference checks. Linear paths and parent walks occur only
in this independent audit, never in the implementation being checked. -/

def sample : Nat→Nat→Nat→Tree Nat 32
  | 0,d,seed => .leaf (d+seed%4) seed
      (if seed%5=0 then none else some ⟨seed%32,by omega⟩)
  | fuel+1,d,seed => .node d seed
      (sample fuel (d+seed%3) (2*seed+1))
      (sample fuel (d+(seed/3)%3) (2*seed+2))

def trace (p : Fin 32) : Tree Nat 32→Option (List (Nat×Nat))
  | .leaf d a terminal => if terminal=some p then some [(d,a)] else none
  | .node d a l r =>
    let tail:=match trace p r with | some xs=>some xs | none=>trace p l
    tail.map ((d,a)::·)

def reference (p : Fin 32) (limit : Nat) (t : Tree Nat 32) : Option (Nat×Nat) :=
  (trace p t).bind fun path=>path.find? fun v=>decide (limit≤v.1)

def slowParent (xs : Array (Cell Nat)) : Option Nat→Nat→Option Nat
  | value,0 => value
  | none,_+1 => none
  | some i,k+1 => slowParent xs ((xs[i]?).bind fun c=>c.parent) k

def checkRows (levels : Nat) (s : Store Nat 32) : IO Unit := do
  for i in List.range s.cells.size do
    let some c:=s.cells[i]? | throw (IO.userError "missing cell")
    unless c.jumps.size==levels do throw (IO.userError "wrong materialized row width")
    for k in List.range levels do
      let actual:=(c.jumps[k]?).getD none
      let expected:=slowParent s.cells (some i) (2^k)
      unless actual==expected do throw (IO.userError s!"jump mismatch i={i} k={k}")

def chain : Nat→Nat→Tree Nat 32
  | 0,d => .leaf (d+3) 777777 (some 0)
  | k+1,d => .node d (k+1) (chain k (d+(k%3))) (.leaf d (100000+k) none)

def main : IO Unit := do
  let mut checked:=0
  let mut rowCells:=0
  let mut maxQueryWork:=0
  for seed in List.range 48 do
    let t:=sample 5 0 (seed+1)
    let levels:=levelsFor t.nodes
    let idx:=build levels t
    unless idx.cells.size==t.nodes do throw (IO.userError "allocation count")
    unless idx.work≤33+t.nodes*(6*levels+8) do throw (IO.userError "preorder construction counter")
    checkRows levels idx
    rowCells:=rowCells+idx.cells.size*levels
    for p in (List.ofFn id : List (Fin 32)) do
      for limit in List.range 20 do
        let result:=query levels idx p limit
        let actual:=result.value.map fun out=>(out.cell.depth,out.cell.payload)
        let expected:=reference p limit t
        unless actual==expected do throw (IO.userError s!"cut mismatch seed={seed} terminal={p.val} limit={limit}")
        unless result.work≤6*levels+6 do throw (IO.userError "query counter")
        maxQueryWork:=max maxQueryWork result.work
        checked:=checked+1
  IO.println s!"smallQueries={checked} checkedJumpCells={rowCells} maxQueryWork={maxQueryWork} duplicateTargets=lastWrite sources=unlabelled"
  (←IO.getStdout).flush
  let t:=chain 8192 0
  let levels:=levelsFor t.nodes
  let idx:=build levels t
  unless idx.cells.size==16385 do throw (IO.userError "deep allocation")
  unless idx.work≤33+t.nodes*(6*levels+8) do throw (IO.userError "deep construction counter")
  let zero:=query levels idx 0 0
  unless zero.value.map (fun out=>out.address)==some 0 do throw (IO.userError "zero-depth root ownership")
  for limit in [0,1,2,3,5,17,257,1024,4096,8191,8192,8193,10000] do
    let result:=query levels idx 0 limit
    let actual:=result.value.map fun out=>(out.cell.depth,out.cell.payload)
    unless actual==reference 0 limit t do throw (IO.userError s!"deep cutoff mismatch {limit}")
    unless result.work≤6*levels+6 do throw (IO.userError "deep query counter")
  IO.println s!"depthCutQueries={checked+13} deepNodes={idx.cells.size} levels={levels} buildWork={idx.work} queryBound={6*levels+6} rootPayload={zero.value.map (fun out=>out.cell.payload)} exactPaths=true zeroRefinements=true"
