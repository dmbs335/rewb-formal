#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
if grep -nE '\b(sorry|admit|sorryAx|native_decide)\b|^[[:space:]]*(axiom|constant)[[:space:]]' REWB.lean REWB/*.lean; then
  echo 'Untrusted or incomplete proof construct detected.' >&2
  exit 1
fi
lake build REWB REWB.ShortSourceRegression REWB.BoundaryIndexRegression \
  REWB.BoundaryIndexCutsRegression REWB.BoundaryIndexMergeRegression \
  REWB.BoundaryIndexMixedRegression REWB.MaskedFiniteActionRegression \
  REWB.MaskedProgressionRegression REWB.MaskedCutRegression REWB.BoundaryTrieRegression \
  REWB.MaskedRunDiscoveryRegression REWB.BoundaryApplicationRegression \
  REWB.MaskedPeriodicRegression REWB.MaskedOrderedRegression \
  REWB.MaskedPeriodicTextRegression
log=$(mktemp)
trap 'rm -f "$log"' EXIT
lake env lean REWB/Tests.lean | tee "$log"
if grep -Eq 'sorryAx' "$log"; then
  echo 'Unexpected proof dependency.' >&2
  exit 1
fi
