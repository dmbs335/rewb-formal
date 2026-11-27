import REWB.MaskedEventBudget

/-! Run after `lake build REWB.MaskedEventBudget` with:
    `lake env lean --run audits/masked_event_smoke.lean`. -/

open REWB.MaskedEventBudget

def main : IO Unit := do
  let built := build sampleTree
  IO.println s!"small-to-large: positions={built.positions}, transfers={built.transfers}, fresh={built.fresh.length}, retired={built.retired.length}, thresholds={(records sampleTree).length}"
  IO.println s!"unary chain N=100: resetRecords={(unaryRebuild 100).length}, persistentAdjacencies={(edges (List.range 100)).length}"

#print axioms lightVolume_bound
#print axioms insert_edge_repair
#print axioms build_strict
#print axioms build_transfers
#print axioms build_balance
#print axioms records_bound
#print axioms oneShot_bound
#print axioms unaryRebuild_quadratic
#print axioms sample_execution
