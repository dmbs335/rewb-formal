#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
# Run scripts/check.sh first to build the implementation and regression imports.
for name in masked_reporting_smoke masked_event_smoke boundary_index_smoke \
  lean_lce_index_smoke indexed_grid_smoke lean_run_index_smoke lean_p2_tail_smoke \
  lean_context_smoke lean_boundary_mixed_smoke masked_finite_action_smoke; do
  echo "Running $name"
  lake env lean --run "audits/$name.lean"
done
