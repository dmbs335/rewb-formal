# Cut construction source recovery

Date: 2026-11-25. Repository: dmbs335/rewb-formal.

This recovery adds the nine Cut construction sources listed below at their original repository paths. The content was reconstructed from retained exact `apply_patch` and source-edit tool payloads after the execution environment became unavailable. No additional proof fixes or algorithm changes were made during recovery.

## Provenance and verification boundary

The original filesystem is unavailable. The recovered contents have **not** been compared against original filesystem hashes or bytes. Prior local PASS observations below describe the earlier local executions; they are not fresh verification of this recovery tree.

Seven modules were observed to pass Lean kernel checking and produce oleans, including the final change that explicitly charges construction of the summary identity table:

- `REWB/PeriodicConstructionCutTable.lean`
- `REWB/PeriodicConstructionCutSummary.lean`
- `REWB/PeriodicConstructionCutDFA.lean`
- `REWB/PeriodicConstructionCutRange.lean`
- `REWB/PeriodicConstructionCutQuery.lean`
- `REWB/PeriodicConstructionCutTuples.lean`
- `REWB/PeriodicConstructionCutInputs.lean`

The last complete local dependency build for those seven was recorded at `/tmp/periodic_cut_inputs_build.log`, with 210 targets. That temporary log is currently inaccessible and is not included in this recovery.

The remaining two files have the following prior status:

- `REWB/PeriodicConstructionCutBuild.lean`: the measured build and its value/work theorems passed locally. A final saved patch then added the explicit summary identity factory cost to `buildDFA`, `buildDFACost`, and the corresponding proof. The result of the subsequent combined build was not observed before the environment disconnected.
- `REWB/PeriodicConstructionCutPhase.lean`: the full phase/query value and work theorems passed a local `lake env lean` invocation; its successful log at `/tmp/periodic_cut_phase.log` was empty. A later combined build against the enlarged lower-level query coefficients was started but its result was not observed.

The unobserved combined build wrote to `/tmp/periodic_cut_full_build.log` (execution session 73387). The recovery tree requires a fresh build; it must not be labeled frozen solely on these historical observations.

All nine source files are included. No source file was omitted or replaced with an inferred placeholder.

## Work still required

- Build the recovered nine modules against the recorded repository base and the frozen Construction/Pattern dependencies.
- Run principal `#print axioms` checks.
- Add and run kernel regressions and a bounded compiled runtime comparison audit.
- Inspect generated runtime code for duplicate construction and unmeasured text scans.
- Complete the callers' primitive substitution and overall cost integration.

No Cut runtime audit, regression module, principal axiom manifest, or codegen audit had been completed when the environment became unavailable. This recovery does not claim the complete runtime theorem.

## Public interfaces

Namespace: `REWB.PeriodicConstruction.Cut`.

- `buildDFA`, `buildDFA_value`, `buildDFA_work`: actual joint-map index construction, preserving the old index and product counter.
- `queryRange`, `queryRange_value`, `queryRange_work`: actual dyadic query, preserving the entire old result.
- `queryIndex`, `queryIndex_value`, `queryIndex_work`: actual three-range cut query, including finite table transport.
- `prepareTail`, `prepareTail_value`, `prepareTail_work`: actual shared suffix map preparation.
- `phaseQuery`, `phaseQuery_value`, `phaseQuery_work`: finite summary algebra, tuple extraction, orbit/formula/window construction and target AP reads.
- `query`, `query_value`, `query_work`: the guarded local periodic query, preserving the entire old `MaskedPeriodic.Text.query` record.
- `dfaBuild_tiny`: the singleton/empty-leaf invariant for the actual old DFA index builder.

Query bounds use concrete fixed-pattern coefficients multiplying the old products/visits or query-cost ledger. The prebuilt text index and immutable target arrays remain explicit inputs. The construction bound is:

```lean
def buildDFACost (b c e n : Nat) : Nat :=
  prepareCost b c e+n*(primitiveCost b c e+1)+
    n*(atomCost (cardinality b c e) (primitiveCost b c e)+1)+
    oneCost (cardinality b c e) (primitiveCost b c e)+
    buildCost (summaryCost (cardinality b c e) (primitiveCost b c e)) n+7

def buildCost (C n : Nat) : Nat :=
  6*(C+20)*(n+1)*(n.log2+2)
```

The ledger counts structural operations with scalar arithmetic and fixed DFA steps as primitives. Vector equality is charged by full fixed-state lengths, consistently with the frozen finite-construction module. This is not a native CPU, garbage-collection or bit-complexity measurement.
