import REWB.BoundaryApplicationHeavyRegression
open REWB REWB.BoundaryApplication

/-! Small runtime regression for the observed aliased-pattern code path.
Two DFA states give four subset colors, exposing a mistaken D-tree value
passed where a subset State is required. -/
def machine : DFA (Fin 2) := ⟨2,0,fun _ a=>a,fun _=>true⟩

def main : IO Unit := do
  let idx:=HeavyIndex.build machine machine machine machine [] 0 0 (Nat.le_refl 0)
  unless idx.addresses.nodes.size==3 && idx.paths.imports==1 do throw (IO.userError "empty construction")
  let q:=HeavyIndex.query machine machine machine machine [] idx 0 0
  unless q.value && q.visits==2 do throw (IO.userError "empty endpoint/head-jump query")
  IO.println s!"emptyHeavyNodes={idx.addresses.nodes.size} emptyImports={idx.paths.imports} emptyQuery={q.value} emptyVisits={q.visits}"
