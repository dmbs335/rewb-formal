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
  REWB.MaskedPeriodicTextRegression REWB.MaskedOrderedOwnerRegression \
  REWB.BoundaryApplicationHeavyRegression REWB.MaskedClusterRegression \
  REWB.MaskedPeriodicBatchRegression \
  REWB.BoundaryApplicationStartRegression REWB.MaskedClusterCursorRegression \
  REWB.MaskedThresholdRegression REWB.MaskedDensityChargeRegression \
  REWB.MaskedClusterBankRegression \
  REWB.BoundaryApplicationSeparatedRegression \
  REWB.MaskedClusterCutRegression \
  REWB.MaskedMutableProgressionRegression \
  REWB.MaskedSourceFanoutRegression \
  REWB.MaskedClusterLeaderRegression \
  REWB.MaskedClusterMutableRegression \
  REWB.MaskedMutableProgressionBatchRegression \
  REWB.MaskedEmptyRegression \
  REWB.MaskedEmptyBatchRegression \
  REWB.MaskedClusterDescriptorRegression \
  REWB.BoundaryBorderRegression \
  REWB.MaskedSuffixClassRegression \
  REWB.MaskedClusterMutableStoreRegression \
  REWB.BoundaryBorderWindowRegression \
  REWB.BoundaryRangeRegression \
  REWB.MaskedTraversalEdgeRegression \
  REWB.BoundaryBorderRegularRegression \
  REWB.BoundaryRangeNearIndexRegression \
  REWB.BoundaryRangeFarIndexRegression \
  REWB.MaskedTraversalDriverRegression \
  REWB.MaskedRunCatalogRegression \
  REWB.BoundaryRangeNearIndexBorderRegression \
  REWB.ResidualSeparatedRegression \
  REWB.ResidualStripScheduleRegression \
  REWB.MaskedTraversalBankReadyRegression \
  REWB.OneUseRangeBorderRegression \
  REWB.ResidualDispatchRegression \
  REWB.OneUseRangeFarAggregateRegression \
  REWB.MaskedTraversalRepairRegression \
  REWB.MaskedTraversalContextRegression \
  REWB.OneUseRangeCacheRegression \
  REWB.ShortOuterBandRegression \
  REWB.MaskedTraversalNeighborRegression \
  REWB.MaskedTraversalRetainedRegression \
  REWB.BoundaryRangeCacheRegression \
  REWB.MaskedTraversalIncomingRegression \
  REWB.ShortOuterRegression \
  REWB.MaskedTraversalCompleteRegression \
  REWB.MaskedTraversalRepairCoherenceRegression \
  REWB.MaskedTraversalRepairSnapshotRegression \
  REWB.MaskedTraversalPeriodicCoverageRegression \
  REWB.MaskedTraversalAnswersRegression \
  REWB.MaskedTraversalRepairTransportShortenRegression \
  REWB.MaskedTraversalExecuteSupport \
  REWB.MaskedTraversalPositiveCoverageRegression \
  REWB.MaskedTraversalPositiveCoverageExhaustion \
  REWB.MaskedAllStartRegression \
  REWB.ResidualCachedRegression \
  REWB.ResidualActualRegression \
  REWB.MaskedFiniteConstruction \
  REWB.PeriodicConstructionRegression
log=$(mktemp)
trap 'rm -f "$log"' EXIT
lake env lean REWB/Tests.lean | tee "$log"
if grep -Eq 'sorryAx' "$log"; then
  echo 'Unexpected proof dependency.' >&2
  exit 1
fi
