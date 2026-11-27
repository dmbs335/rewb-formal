# Reimplementation of full-cost execution dependencies

Date: 2026-11-25
Owner: /root/boundary_index
Repository: dmbs335/rewb-formal
Base recovery tree: 03a4880a62dd1e9766196ea013ed539fc6c37eeb
Base recovery commit: be6c2e1933a5311764459fd22ff8d0fb9e6135f8
Validated public checkpoint retained separately: 0f4ef40210db753fe143046bf7312ce7b619aaaf

## Status

These three files are NEW IMPLEMENTATIONS of the missing dependencies. They are not claimed to be byte-exact restorations of the unavailable local files.

The complete frozen originals were read from the published Git tree via GitHub before writing this implementation. The surviving FullCostRepair/Clip/Report/Query/Window/Collect/ExecuteBand/Execute interfaces were preserved. No frozen source or public PR ref was changed by this owner.

Local execution is unavailable. At the moment this tree was submitted, these new sources had NOT been compiled, run, or axiom-audited. Root will run the dedicated GitHub Actions kernel job and return actual errors. This document must not be interpreted as a PASS or freeze manifest.

## Files

- REWB/MaskedAllStartFullCostBank.lean
- REWB/MaskedAllStartFullCostUpdates.lean
- REWB/MaskedAllStartFullCostErase.lean

## Actual executed paths

### Bank

The measured PeriodicConstruction.Cluster.compileDenseBank is called through the real run ID, stored run and source index. Incompatible modulus, missing slots, and invalid run geometry preserve their original branches.

Singleton compilation retains the existing counted point-bank procedure. The stored-bank compiler retains the exact original Option bank and original work counter while adding a separately returned full construction counter.

The leader and context wrappers execute the original actual descriptor/catalog/anchor preparation, then the measured compiler. They preserve the entire original Option Entry × oldWork result.

Public compatibility APIs:

- Bank.Result, Bank.extra.
- compileRun / compileRun_value / compileRun_extra.
- compile / compile_value / compile_extra.
- readyCompile / readyCompile_value / readyCompile_extra.
- contextCompile / contextCompile_value / contextCompile_extra.

### Updates

write executes its actual compiler once and writes the real indexed slot. Its original repairWork, rebuilds and writes counters are retained.

loop executes the actual selected key list. Its proof charges the returned full work against the increment of the real original repairWork, with one fixed dense-construction extra per actual selected key. The concrete reset and context factories instantiate the generic lemma; no bank, answer or cost oracle is passed to the final execution path.

Public compatibility APIs:

- write / write_charged / write_progress.
- loop / loop_credit / loop_progress / loop_work.
- resetOne / resetOne_value / resetOne_charged / resetOne_progress / resetLoop_value.
- contextOne / contextOne_value / contextOne_charged / contextOne_progress / contextLoop_value.

### Erase

refreshCurrent uses the stored entry with the current length, executes Bank.compile, replaces the actual persistent tree cell and updates the real owned slot.

eraseCurrent executes MaskedClusterDescriptor.locate and MaskedMutableProgression.Batch.eraseSource. It then rebuilds only the located current bank. The exact original SourceChange and old counters are retained.

eraseMany is the actual list fold. Its full local work is bounded by (Bank.extra + 1) times its returned original work. The source fanout is not omitted: it stays in the exact returned store.sources.updateWork and must be added once by the final public solver, as in the preserved original solver.

Public compatibility APIs:

- refreshCurrent / refreshCurrent_value / refreshCurrent_extra / refreshCurrent_calls_work.
- eraseCurrent / eraseCurrent_value / eraseCurrent_extra / eraseCurrent_calls_work.
- step / fold_value / fold_extra / fold_calls_work.
- eraseMany / eraseMany_value / eraseMany_work.

## Sources used

Definitions were read from the published Git objects for:

- MaskedClusterMutableBatch
- MaskedClusterMutableStore
- MaskedTraversalBankReady
- MaskedTraversalContext
- MaskedTraversalRepair
- MaskedTraversalRepairCoherence
- MaskedTraversalAggregateErase
- MaskedTraversalAggregateEraseMany
- PeriodicConstructionClusterBank

The dense measured primitive's existing compileDenseBank_extra theorem is the concrete input to Bank.extra. The new wrappers preserve original counters in addition to values, so the already proved semantic and amortized interfaces remain applicable once the new files compile.

## Required validation

The first kernel targets should be:

    lake build REWB.MaskedAllStartFullCostBank REWB.MaskedAllStartFullCostUpdates REWB.MaskedAllStartFullCostErase
    lake build REWB.MaskedAllStartFullCostCollect REWB.MaskedAllStartFullCostExecuteBand REWB.MaskedAllStartFullCostExecute

After actual compiler errors are resolved:

1. Run principal #print axioms checks on the new files and the full dependent execution family.
2. Compare old/new actual results and counters on bounded empty and nonempty fixtures.
3. Inspect generated C for repeated report transactions or retained whole-array aliases.
4. Compose root's full-cost initialization and shared cut construction with the actual full executor.
5. Add the exact source-fanout delta once and reuse the published global Execute cost bound.
6. Freeze only after those checks pass.

No proof escape declarations or native proof shortcuts were introduced. A text scan for the project's forbidden proof-escape tokens passed before submitting this tree; that scan is not a substitute for Lean kernel validation.

## First CI result and next proof patch

GitHub Actions run 45592541855, full-executor job 139130180987, checked commit 3334873b9287c8836c880ab547ed5455d3d4a715. The build log confirmed Bank, Updates and Erase compiled, together with the dependent recovered local family and MaskedAllStartFullCostExecuteBand (411/412 targets). The axiom step was skipped because the last Execute target failed, so no final axiom/freeze claim is made.

The three reported Execute proof errors were:

- initial_credit attempted to unfold an original function already unfolded by apply unification.
- bands_credit required normalization of the accumulator's leading zero.
- the leaf case of plan_credit required identifying the local seeded result in hseed before arithmetic reasoning.

The accompanying Execute patch changes only these proof scripts. It changes no executable definitions. A fresh CI result is required for the patched top-level plan.
