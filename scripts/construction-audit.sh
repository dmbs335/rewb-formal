#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

# Mandatory bounded probes for the installed construction path.
# Large positive P1 and full normalization/independent diagnostics remain
# separately named modes; a skipped or failed mode is not a passing case.
lake build REWB

timeout 120s lake env lean --run audits/periodic_actual_join_smoke.lean
timeout 300s lake env lean --run audits/periodic_cut_construction_smoke.lean
timeout 300s lake env lean --run audits/masked_full_cost_solve_smoke.lean
timeout 180s lake env lean --run audits/masked_full_cost_rows_smoke.lean
timeout 180s lake env lean --run audits/periodic_cache_construction_smoke.lean
timeout 180s lake env lean --run audits/periodic_runs_construction_smoke.lean
timeout 120s lake env lean --run audits/periodic_keys_construction_smoke.lean
timeout 120s lake env lean --run audits/periodic_actual_full_cost_smoke.lean
bash audits/run_full_matcher_composite.sh regular

python3 audits/masked_full_cost_execution_codegen.py
python3 audits/masked_full_cost_rows_codegen.py
