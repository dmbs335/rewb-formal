import REWB.BoundaryApplicationStartCost
open REWB REWB.BoundaryApplication

/-! Independent source/length enumeration for the complete fixed-start
pipeline. These scans are audit code, not index operations. -/

def machine (seed : Nat) : DFA (Fin 2) :=
  ⟨2,⟨seed%2,by omega⟩,
    fun q c=>⟨(seed/(2^(q.val*2+c.val+1)))%2,by omega⟩,
    fun q=>decide ((seed/(2^(q.val+5)))%2=1)⟩

def acceptAll : DFA (Fin 2) := ⟨1,0,fun _ _=>0,fun _=>true⟩
def epsilon : DFA (Fin 2) := ⟨2,0,fun _ _=>1,fun q=>decide (q=0)⟩

def brute (A B C E : DFA (Fin 2)) (w : Word (Fin 2)) (g j right : Nat) : Bool :=
  (List.range (g+1)).any fun i=>
    (List.range (min (g-i) (right-j)+1)).any fun len=>
      decide (Spec.slice w i (i+len)=Spec.slice w j (j+len)) &&
      A.final (A.run A.initial (Spec.slice w 0 i)) &&
      B.final (B.run B.initial (Spec.slice w j (j+len))) &&
      C.final (C.run C.initial (Spec.slice w (i+len) g)) &&
      E.final (E.run E.initial (Spec.slice w (j+len) right))

def check (A B C E : DFA (Fin 2)) (w : Word (Fin 2)) (g : Nat) (hg : g≤w.length) : IO (Nat×Nat×Nat×Nat) := do
  let idx:=StartIndex.build A B C E w 0 g hg
  unless idx.addresses.cells.size==2*(w.length+2)-1 do throw (IO.userError "fixed-start allocation count")
  unless idx.work≤StartIndex.bound A B C E w.length do throw (IO.userError "total construction counter")
  unless idx.cachedLength==w.length do throw (IO.userError "cached text length")
  let mut checked:=0
  let mut accepted:=0
  let mut partialCuts:=0
  let mut maximum:=0
  for j in (List.ofFn id : List (Fin (w.length+1))) do
    if g≤j.val then
      for right in List.range (w.length+1) do
        if j.val≤right then
          let actual:=StartIndex.query B C E idx j right
          let expected:=brute A B C E w g j.val right
          unless actual.value==expected do
            throw (IO.userError s!"fixed-start mismatch n={w.length} g={g} j={j.val} right={right}")
          unless actual.work≤6*StartIndex.levels w.length+StartStep.budget B C E w.length+E.stateCount+10 do
            throw (IO.userError "fixed-start query counter")
          unless actual.locateWork≤6*idx.levels+6 do throw (IO.userError "ancestor query counter")
          let loc:=StartLocate.query idx.levels idx.addresses j (right-j.val)
          let some found:=loc.value | throw (IO.userError "missing valid target/cut")
          unless found.cell.payload.parentDepth≤right-j.val && right-j.val≤found.cell.payload.depth do
            throw (IO.userError "cut outside compressed edge")
          if found.cell.payload.parentDepth<right-j.val && right-j.val<found.cell.payload.depth then
            partialCuts:=partialCuts+1
          checked:=checked+1
          if actual.value then accepted:=accepted+1
          maximum:=max maximum actual.work
  pure (checked,accepted,partialCuts,maximum)

def main : IO Unit := do
  let mut checked:=0
  let mut accepted:=0
  let mut partialCuts:=0
  let mut maximum:=0
  for seed in List.range 48 do
    let n:=seed%11
    let w : Word (Fin 2):=(List.range n).map fun i=>⟨((seed+3)*(i+1)+i/3)%2,by omega⟩
    let g:=(seed/3)%(n+1)
    have hg : g≤w.length := by
      have hm:=Nat.mod_lt (seed/3) (by omega : 0<n+1)
      simpa only [w,List.length_map,List.length_range] using (show g≤n by omega)
    let out←check (machine (seed*17+33)) (machine (seed*31+69))
      (machine (seed*43+101)) (machine (seed*53+47)) w g hg
    checked:=checked+out.1
    accepted:=accepted+out.2.1
    partialCuts:=partialCuts+out.2.2.1
    maximum:=max maximum out.2.2.2
  let small : Word (Fin 2):=[0,1,1,0,1,1]
  let out←check epsilon acceptAll acceptAll epsilon small 3 (by decide)
  checked:=checked+out.1
  accepted:=accepted+out.2.1
  partialCuts:=partialCuts+out.2.2.1
  maximum:=max maximum out.2.2.2
  let smallIdx:=StartIndex.build epsilon acceptAll acceptAll epsilon small 0 3 (by decide)
  let strict:=StartIndex.query acceptAll acceptAll epsilon smallIdx 3 4
  unless strict.value do throw (IO.userError "strict partialCuts-edge witness rejected")
  let some strictCell:=(StartLocate.query smallIdx.levels smallIdx.addresses 3 1).value |
    throw (IO.userError "missing strict partialCuts edge")
  unless strictCell.cell.payload.parentDepth<1 && 1<strictCell.cell.payload.depth do
    throw (IO.userError "witness did not stop strictly inside edge")
  unless 0<partialCuts do throw (IO.userError "no partialCuts cuts exercised")
  IO.println s!"fixedStartSmallQueries={checked} accepted={accepted} strictPartialCuts={partialCuts} maxQueryWork={maximum} closedEpsilon=true"
  (←IO.getStdout).flush
  let w : Word (Fin 2):=List.replicate 512 0
  let idx:=StartIndex.build acceptAll acceptAll acceptAll acceptAll w 0 256 (by simp only [w,List.length_replicate]; omega)
  unless idx.work≤StartIndex.bound acceptAll acceptAll acceptAll acceptAll w.length do throw (IO.userError "deep total construction counter")
  unless idx.addresses.cells.size==1027 do throw (IO.userError "deep fixed-start allocation")
  for right in [256,257,258,333,511,512] do
    let q:=StartIndex.query acceptAll acceptAll acceptAll idx 256 right
    unless q.value==brute acceptAll acceptAll acceptAll acceptAll w 256 256 right do
      throw (IO.userError "deep repeated-word query")
    unless q.work≤6*StartIndex.levels w.length+StartStep.budget acceptAll acceptAll acceptAll w.length+11 do
      throw (IO.userError "deep query counter")
    unless q.locateWork≤6*idx.levels+6 do throw (IO.userError "deep ancestor counter")
  let q:=StartIndex.query acceptAll acceptAll acceptAll idx 256 512
  IO.println s!"fixedStartQueries={checked+6} deepNodes={idx.addresses.cells.size} levels={idx.levels} buildWork={idx.work} deepQueryWork={q.work} deepLocateWork={q.locateWork} fullPipeline=true exactCuts=true"
