import REWB.BoundaryIndexRegression
import REWB.BoundaryIndexCutsRegression
import REWB.BoundaryIndexMergeRegression

/-! Runtime probes of persistent recoloring, exact cut windows and the
actual small-to-large schedule. Run after scripts/check.sh. -/
open REWB REWB.BoundaryIndex REWB.BoundaryIndex.MergeSchedule

def makeProgram : Nat→Nat→Program 3 2 10
  | 0,off => .leaf ⟨off%1024,by omega⟩ ⟨off%3,by omega⟩ ⟨off%2,by omega⟩
  | d+1,off =>
    let g : Vector (Fin 3) 3:=Vector.ofFn (fun _=>0)
    .node g g (makeProgram d off) (makeProgram d (off+2^d))

def main : IO Unit := do
  let d:=Regression.reset
  let xs : List (Token Bool 3):=List.replicate 30000 (.mark 1)
  let base:=TokenIndex.buildFor d xs
  let merged:=Tree.recolor Regression.collapse base.1
  let inserted:=Tree.insert merged.1 12345 2 d.initial
  let yes:=TokenIndex.query d (Regression.select 0) merged.1 12346
  let fresh:=TokenIndex.query d (Regression.select 2) inserted.1 12346
  let old:=TokenIndex.query d (Regression.select 2) merged.1 12346
  if !yes.1 || !fresh.1 || old.1 then
    throw (IO.userError "persistent recoloring or fresh-insertion failure")
  IO.println s!"cells={xs.length} build={base.2} recolor={merged.2} insert={inserted.2} query={yes.2}; retained versions passed"
  let w : Word Bool:=List.replicate 512 false
  let I:=Cuts.build CutsRegression.emptyWord CutsRegression.anyWord w
  let left:=Cuts.query CutsRegression.emptyWord CutsRegression.anyWord I.1 0 0 0 512 (0 : Fin 2)
  let excluded:=Cuts.query CutsRegression.emptyWord CutsRegression.anyWord I.1 0 1 511 512 (0 : Fin 2)
  let A:=CutsRegression.singleton true
  let B:=CutsRegression.singleton false
  let D:=CutsRegression.anyWord
  let J:=FixedEnd.build A B D [true,false]
  let exact:=FixedEnd.query A B D J.1 2 2 1 1 (0 : Fin 3) (0 : Fin 1)
  if left.answer != some true || excluded.answer != some false || exact.answer != some true then
    throw (IO.userError "cut-window or reversed fixed-end failure")
  IO.println s!"cut n={w.length} buildProducts={I.2} products={excluded.products} visits={excluded.visits}; exact windows passed"
  let rows : Array (Vector (Fin 2) 2):=Array.replicate 512 (Vector.ofFn id)
  let p:=makeProgram 9 0
  let out:=MergeBuild.run rows p
  let at7:=Merge.point out.state.tree (7 : Fin 1024)
  if out.state.cachedSize != 512 || out.state.positions.length != 512 || out.transfers != 2304 ||
      !at7.active 0 1 || at7.trans 0 != 0 || at7.trans 1 != 1 then
    throw (IO.userError "persistent light-import schedule failure")
  IO.println s!"merge positions={out.state.cachedSize}, transfers={out.transfers}, steps={out.steps}; static text preserved"
