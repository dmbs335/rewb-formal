# Full-cost execution recovery snapshot

Date: 2026-11-25
Owner: /root/boundary_index
Repository: dmbs335/rewb-formal
Base tree: 25ab4c86ed272e1ed0f220075c79d9d7efd4657b
Last published validated checkpoint reported by root: 0f4ef40210db753fe143046bf7312ce7b619aaaf
Published validation scope: 694 targets / 2343 principal reports / 83 compiled probes.

## Recovery provenance and limits

This tree preserves source reconstructed from exact recent tool-call patch payloads and complete file reads after the execution environment became unavailable. It is a recovery snapshot, not a validated release or a frozen proof family.

The unavailable filesystem could not be read for hashes or byte comparison. Exact byte identity between these reconstructed text blobs and the former local files is therefore unverified. No new proof repairs or algorithmic changes were made while reconstructing this snapshot.

The public PR's validated head must remain unchanged until the recovered sources and their dependencies are rebuilt and audited. The owner created only a Git tree object; root owns any separate recovery commit/ref.

## Included files and last observed state

| File | Recovery source | Last local verification |
| --- | --- | --- |
| REWB/MaskedAllStartFullCostReport.lean | Complete file read | Kernel build PASS |
| REWB/MaskedAllStartFullCostRepair.lean | Complete file read | Kernel build PASS |
| REWB/MaskedAllStartFullCostClip.lean | Two complete contiguous file reads | Kernel build PASS |
| REWB/MaskedAllStartFullCostQuery.lean | Complete creation patch and all subsequent replacement payloads | Kernel build PASS as dependency of Window and Collect |
| REWB/MaskedAllStartFullCostWindow.lean | Complete creation patch | Kernel build PASS |
| REWB/MaskedAllStartFullCostCollect.lean | Complete creation patch and final proof replacement payload | Kernel build PASS; final command returned exit 0 |
| REWB/MaskedAllStartFullCostExecuteBand.lean | Complete creation patch and all subsequent replacement payloads | Final build result unread; preceding build had exactly one remaining normalization error |
| REWB/MaskedAllStartFullCostExecute.lean | Complete last apply_patch payload | No build result; local save itself was unconfirmed when environment disconnected |

The final ExecuteBand change inserted `simp only [Nat.one_mul] at hs` before a `change` that previously failed on the expression `1 * (...)`. The final build was started as session 97511. Its result was never observed. This is not a PASS claim.

The Execute patch and following build were submitted in functions cell g3:238. The call produced no result, then the environment became unavailable. The cell was later terminated. This snapshot preserves the exact intended source from that tool payload, without claiming it was saved or compiled locally.

## Three source files not reconstructed here

The following dependencies existed locally and had kernel PASS before the interruption, but only summaries or partial reads remained in this agent's available context. Their complete source was not guessed:

- REWB/MaskedAllStartFullCostBank.lean
- REWB/MaskedAllStartFullCostUpdates.lean
- REWB/MaskedAllStartFullCostErase.lean

The included family cannot be rebuilt in isolation without those files. Recover the exact local files or an exact prior payload if available. Any later reconstruction from API notes must be identified as a fresh implementation requiring full proof validation.

### Preserved interface notes for missing files

These notes are a resumption guide, not reconstructed source.

Namespace `REWB.MaskedAllStart.FullCost.Bank`:

- `abbrev Result (X : Type) := X × Nat`.
- `extra C E K := PeriodicConstruction.Cluster.denseBankExtra C.stateCount E.stateCount K + 3`.
- Actual `compileRun`, `compile`, `readyCompile`, and `contextCompile` return the original complete compiler result, including its original counter, plus full construction work.
- Each `*_value` proves equality of that entire original result.
- Each `*_extra` bounds the new work by the old counter plus `extra C E prepared.K`.
- Dense construction calls actual `PeriodicConstruction.Cluster.compileDenseBank`; the singleton path retains actual counted point primitives.

Namespace `REWB.MaskedAllStart.FullCost.Updates`:

- Actual `write` and tail sparse `loop` preserve original store.repairWork.
- `write_charged`: full work plus old repairWork is at most new repairWork plus fixed extra.
- `write_progress`: old repairWork + 1 <= new repairWork.
- `loop_credit`: full plus initial repairWork <= final repairWork + extra * keys.length.
- `loop_work`: full <= (extra + 1) * (final.repairWork - initial.repairWork).
- Concrete `resetOne` uses Bank.readyCompile; `contextOne` uses Bank.contextCompile.
- `resetOne_charged/progress`, `contextOne_charged/progress`, `resetLoop_value`, and `contextLoop_value` instantiate the generic loop with actual compilers.

Namespace `REWB.MaskedAllStart.FullCost.Erase`:

- Actual `refreshCurrent` compiles the current slot through Bank.compile and replaces the real persistent aggregate cell.
- Actual `eraseCurrent` executes descriptor locate and Batch.eraseSource, then refreshCurrent.
- Actual `eraseMany` folds these operations and returns the original complete SourceChange plus full local work.
- `eraseMany_value` proves exact old Aggregate.eraseMany result equality.
- `eraseMany_work`: full <= (Bank.extra C E env.prepared.K + 1) * returned old SourceChange.work.
- Source fanout is preserved in returned store.sources.updateWork and is not silently absorbed into this local ledger.

## Established substitution path

The six included locally verified modules implement actual measured operations, not an arbitrary cost-counter multiplication:

1. Measured finite cut index products and actual replay-map encoding.
2. At most two actual clipped boundary-bank recompilations.
3. Actual aggregate region and closure scans.
4. One concrete source-window query returning the original WindowResult.
5. One interval reporter with all positive and negative query visits and list-copy work.
6. One actual erase fold and one actual answer push.

Value theorems preserve original answers, data structures, and original counters, allowing the published semantic and amortized proofs to be reused.

The pending execution files install these operations into the real band/bands/edge/plan traversal. The intended final interface is:

- `Execution.plan env capacity template actualPlan global : Bank.Result (MaskedTraversalExecute.State C E h)`.
- `Execution.plan_value`: exact original Execute.plan state.
- `Execution.plan_credit`: full work plus fixed coefficient times initial stats.work <= fixed coefficient times final stats.work.
- `Execution.plan_work`: full work <= fixed coefficient times original final stats.work.

Only `PeriodicConstruction.Cut.Tiny env.cut.tree` is needed for the local substitution cost. `Query.build_tiny` proves it for the actual Cut.build. The source-update fanout remains separately charged by the final public solver using the exact original returned source state.

These execution theorems are source targets, not verified claims in this snapshot.

## Observed logs and commands before loss

Paths below name prior transient logs; their contents are not recreated here and may be unavailable after environment replacement.

- /tmp/rewb-masked-full-cost-local-build.log — 365-target Bank/Updates/Repair/Clip/Erase/Report family build PASS.
- /tmp/rewb-masked-full-cost-query-build.log — intermediate query proof failures; later dependent build passed after the documented fixes.
- /tmp/rewb-masked-full-cost-window-build.log — final Window and Query build PASS, session 42219 exit 0.
- /tmp/rewb-masked-full-cost-collect-build.log — final Collect build PASS, command returned exit 0.
- /tmp/rewb-masked-full-cost-execute-band-build.log — final result unread, session 97511.
- /tmp/rewb-masked-full-cost-execute-build.log — command submitted after pending patch, execution/save unconfirmed.

## Dependencies under separate ownership

Root owns FullCostInitialScan/InitialRuns/Initial and the final measured prepare/solve bridge.

Helper /root/boundary_index/trie_sort owns PeriodicConstructionCutTable/Summary/DFA/Range/Query/Build/Tuples/Inputs/Phase. Its last report:

- Table/Summary/DFA/Range/Query/Tuples/Inputs rebuilt PASS after explicitly charging identity-table construction, 210 targets, /tmp/periodic_cut_inputs_build.log.
- BuildDFA's final identity charge was saved but the final combined build result was unread.
- Phase's complete phaseQuery/query value and work proofs passed standalone Lean, but the final dependent rebuild result was unread.
- Final combined session 73387, /tmp/periodic_cut_full_build.log.
- Cut9 runtime/regression/axiom/codegen audit was not completed, so it is not frozen.

## Required resumption checks

1. Restore/recover Bank, Updates and Erase without overwriting any surviving originals.
2. Finish helper Cut9 final build and its requested runtime/regression/axiom checks.
3. Build REWB.MaskedAllStartFullCostCollect to verify the reconstructed snapshot and dependency signatures.
4. Build REWB.MaskedAllStartFullCostExecuteBand, then REWB.MaskedAllStartFullCostExecute; resolve only actual kernel errors.
5. Inspect generated C for a single actual report transaction per band and owned store/anchor array threading, following the already published Runtime fix. No general compiler allocation theorem has been claimed.
6. Add bounded actual old/new output and counter comparisons, including empty input and nonempty reporting.
7. Generate principal axiom manifests, then connect root's measured initialization and prepare/solve path.
8. Add the exact preserved source-fanout delta once, and use the published ExecuteCost/Growth bounds for the fixed-pattern global envelope.
9. Freeze/publish only after those checks pass.

The last direct environment retry failed with: "No usable execution environment is available. Wait for an environment to become available before using this tool."
