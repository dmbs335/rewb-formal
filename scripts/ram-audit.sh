#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

lake build REWB.ActualModulusFoldRAM REWB.ActualProjectionModulusRAM \
  REWB.PeriodicModulusRAM REWB.ProjectionTraversalRAM REWB.WordRAMInputLists \
  REWB.AffineWordBounds REWB.MatcherMachineCostTransfer
log=$(mktemp)
trap 'rm -f "$log"' EXIT
lake env lean audits/word_ram_axioms.lean | tee "$log"
python3 scripts/check-principal-axioms.py audits/word_ram_axioms.lean "$log"
timeout 60s lake env lean --run audits/word_ram_smoke.lean
