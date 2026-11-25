import REWB.BoundaryApplicationHeavyQuery
open REWB REWB.BoundaryApplication

/-! Independent executable checks of the actual compressed/persistent
implementation. Explicit target/length enumeration occurs only here. -/

def machine (seed : Nat) : DFA (Fin 2) :=
  ⟨2,⟨seed%2,by omega⟩,
    fun q c=>⟨(seed/(2^(q.val*2+c.val+1)))%2,by omega⟩,
    fun q=>decide ((seed/(2^(q.val+5)))%2=1)⟩

def acceptAll : DFA (Fin 2) := ⟨1,0,fun _ _=>0,fun _=>true⟩

def brute (A B D E : DFA (Fin 2)) (w : Word (Fin 2)) (g a r : Nat) : Bool :=
  (List.range (r+1)).any fun t=>decide (g≤t) &&
    (List.range (min a (t-g)+1)).any fun len=>
      decide (Spec.slice w (a-len) a=Spec.slice w (t-len) t) &&
      A.final (A.run A.initial (Spec.slice w 0 (a-len))) &&
      B.final (B.run B.initial (Spec.slice w (a-len) a)) &&
      D.final (D.run D.initial (Spec.slice w g (t-len))) &&
      E.final (E.run E.initial (Spec.slice w t r))

def checkAddresses (A B D E : DFA (Fin 2)) (w : Word (Fin 2)) (g : Nat)
    (idx : HeavyIndex.Index A B D E w) : IO Unit := do
  unless idx.addresses.nodes.size == 2*(w.length+2)-1 do throw (IO.userError "address allocation count")
  unless idx.paths.imports == (Versions.root idx.normal.versions).transfers+(w.length-g+1) do
    throw (IO.userError "light imports plus one target seed")
  unless idx.work ≤ HeavyIndex.bound A B D E w.length do throw (IO.userError "total construction bound")
  for i in List.range idx.addresses.nodes.size do
    let some c:=idx.addresses.nodes[i]? | throw (IO.userError "missing address")
    unless c.rank≤(w.length+2).log2 do throw (IO.userError "light rank bound")
    match c.jump with
    | none => unless c.rank==0 do throw (IO.userError "terminal head rank")
    | some j =>
      let some up:=idx.addresses.nodes[j]? | throw (IO.userError "missing head jump")
      unless j<i && up.rank+1==c.rank do throw (IO.userError "head jump is not an earlier rank")
  for a in (List.ofFn id : List (Fin (w.length+1))) do
    match idx.addresses.sources.get a with
    | none => unless g<a.val do throw (IO.userError "missing source slot")
    | some i =>
      let some c:=idx.addresses.nodes[i]? | throw (IO.userError "invalid source address")
      unless a.val≤g && c.terminal==some (.source a) do throw (IO.userError "wrong source slot")

def main : IO Unit := do
  let mut checked:=0
  let mut yes:=0
  let mut maximumVisits:=0
  for seed in List.range 40 do
    let n:=seed%11
    let w : Word (Fin 2):=(List.range n).map fun i=>⟨((seed+3)*(i+1)+i/3)%2,by omega⟩
    let g:=(seed/3)%(n+1)
    have hg : g≤w.length := by
      have hm:=Nat.mod_lt (seed/3) (by omega : 0<n+1)
      simpa only [w,List.length_map,List.length_range] using (show g≤n by omega)
    let A:=machine (seed*17+33)
    let B:=machine (seed*31+69)
    let D:=machine (seed*43+101)
    let E:=machine (seed*53+47)
    let idx:=HeavyIndex.build A B D E w 0 g hg
    checkAddresses A B D E w g idx
    for source in (List.ofFn id : List (Fin (w.length+1))) do
      if source.val≤g then
        for right in List.range (w.length+1) do
          let actual:=HeavyIndex.query A B D E w idx source right
          let expected:=brute A B D E w g source.val right
          unless actual.value==expected do
            throw (IO.userError s!"fixed-end mismatch seed={seed}, n={n}, g={g}, source={source.val}, right={right}")
          unless actual.visits≤(w.length+2).log2+1 do throw (IO.userError "query visit bound")
          unless actual.work≤((w.length+2).log2+1)*(HeavyIndex.probeBudget A D E w.length+4)+5 do
            throw (IO.userError "query work bound")
          checked:=checked+1
          if actual.value then yes:=yes+1
          maximumVisits:=max maximumVisits actual.visits
  IO.println s!"smallChecks={checked} accepted={yes} maxVisits={maximumVisits}"
  (← IO.getStdout).flush
  let w : Word (Fin 2):=List.replicate 512 0
  let A:=acceptAll
  let B:=acceptAll
  let D:=acceptAll
  let E:=acceptAll
  let idx:=HeavyIndex.build A B D E w 0 256 (by simp only [w,List.length_replicate]; omega)
  checkAddresses A B D E w 256 idx
  let q:=HeavyIndex.query A B D E w idx 256 512
  unless q.visits≤(w.length+2).log2+1 do throw (IO.userError "deep-prefix jump bound")
  IO.println s!"fixedEndChecks={checked} accepted={yes} maxVisits={maximumVisits} deepNodes={idx.addresses.nodes.size} deepImports={idx.paths.imports} deepVisits={q.visits} work={idx.work} exactClosedCuts=true directHeadJumps=true"
