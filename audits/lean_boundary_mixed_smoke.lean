import REWB.BoundaryIndexMixedRegression
/-! Optional actual-entrypoint smoke for the persistent mixed scheduler.
Run: lake env lean --run audits/lean_boundary_mixed_smoke.lean
The 512 input leaves alternate silent sources and seeded targets. -/
open REWB REWB.BoundaryIndex

def makeMixed : Nat→Nat→Mixed.Program 3 2 10
  | 0,off =>
    let pos : Fin 1024 := ⟨off%1024,by omega⟩
    if off%2=0 then .source pos else .target pos ⟨off%3,by omega⟩ ⟨off%2,by omega⟩
  | d+1,off =>
    let g : Vector (Fin 3) 3 := Vector.ofFn (fun _=>0)
    .node g g (makeMixed d off) (makeMixed d (off+2^d))

def main : IO Unit := do
  let rows : Array (Vector (Fin 2) 2) := Array.replicate 512 (Vector.ofFn id)
  let out := Mixed.run rows (makeMixed 9 0)
  let at7 := Merge.point out.state.tree (7 : Fin 1024)
  let at6 := Merge.point out.state.tree (6 : Fin 1024)
  unless out.totalMass=512 && out.state.cachedSize=256 && out.state.positions.length=256 &&
      out.transfers=1024 && at7.active 0 1 && !(at6.active 0 1) &&
      at7.trans 0=0 && at7.trans 1=1 do
    throw (IO.userError "mixed boundary scheduler smoke failed")
  IO.println s!"totalMass={out.totalMass} targets={out.state.cachedSize} list={out.state.positions.length} transfers={out.transfers} steps={out.steps} target={at7.active 0 1} source={at6.active 0 1} static0={at7.trans 0} static1={at7.trans 1}"
