# Root construction recovery — 2026-11-25

The execution environment became unavailable at approximately 09:48 UTC. The exact frozen baseline is commit `0f4ef40210db753fe143046bf7312ce7b619aaaf`, tree `25ab4c86ed272e1ed0f220075c79d9d7efd4657b`.

The eight files below were reconstructed from their complete successful tool-write payloads and subsequent patches. All eight had successful local kernel builds before the outage. The inaccessible workspace could not be hashed against this reconstruction; a fresh build of this reconstructed tree is still required. No runtime or principal-axiom audit was completed for these eight new files before the outage.

- REWB/MaskedAllStartFullCostInitialScan.lean
- REWB/MaskedAllStartFullCostInitialRuns.lean
- REWB/MaskedAllStartFullCostInitial.lean
- REWB/PeriodicActualJoinCut.lean
- REWB/PeriodicActualJoinCross.lean
- REWB/PeriodicActualJoinSplit.lean
- REWB/PeriodicActualJoin.lean
- REWB/PeriodicActualJoinCost.lean

## Last observed local checks

- InitialScan: successful build recorded in `build-full-cost-initial-scan.txt`.
- InitialRuns: successful build recorded in `build-full-cost-initial-runs.txt`.
- Initial: successful 433-target dependency build, `build-full-cost-initial.txt`.
- JoinCut: successful build, `build-periodic-actual-join-cut.txt`.
- JoinCross: successful build, `build-periodic-actual-join-cross.txt`.
- JoinSplit: successful build, `build-periodic-actual-join-split.txt`.
- Join: successful 69-target dependency build, `build-periodic-actual-join.txt`.
- JoinCost: successful 70-target dependency build, `build-periodic-actual-join-cost.txt`.

Those logs were in the unavailable workspace under `/workspace/scratch/b3ea3fdc0b59/`; this recovery does not claim to have copied them.

## Completed interfaces

`MaskedAllStart.FullCost.Initial.start_value` preserves the complete old initialization result and counters. `start_work_closed` bounds the newly executed formula-construction initialization by a fixed-pattern multiple of `(n+2)*height(n)^2`. Its current local cut/tail primitives still need replacement by the separately developed `PeriodicConstruction.Cut` implementations.

`PeriodicActual.Join.run_value` preserves the complete old `CountedJoin.Result`. The separately returned work executes DFA cut rows, formula windows, colored events, text partitions, filters, coordinate shifts and dyadic powers. `run_work_bound_modulus` proves:

```
extra <= (coefficient(states,maxK,B)+10)
         * (heightFor(n)+1)
         * (sources.length+targets.length+5*(n+1))
```

The hypotheses are the actual event formulas' uniform measure bound B and K<=maxK. They are structural lemmas, not runtime answer/cost callbacks.

## Next integration

1. Swap measured finite cut build/tail/query operations into InitialScan/InitialRuns, preserving their complete-value interfaces.
2. Complete the cost-bearing all-start prepare/execute/solve and actual row/cached matcher wrappers.
3. Install this measured Join.run in the measured long/short P1 branch preparations.
4. Run fresh kernel, principal-axiom, executable and generated-code checks before publishing a new verified checkpoint.

The baseline's 25/13 theorem remains a theorem for its returned ledger. This recovery snapshot does not assert a completed full-construction or machine-cost theorem.
