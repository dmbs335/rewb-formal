# REWB Formal

Lean 4 formalization of fixed-pattern, dynamically at-most-two-use, single-register regular expressions with backreferences.

**The complete semantic compiler and matcher are now verified. The proposed strongly subquadratic running-time theorem is still open.** The project distinguishes a correct executable decision procedure, accelerated branches with measured operation counts, and the remaining global complexity obligations.

## Semantics and target

The register stores the most recently closed capture. Opening a capture preserves its previous value; nested captures include recalled text; the initial register is empty. A successful trace executes at most two references. This is a precisely defined theoretical semantics, rather than a specification of a particular regex engine.

For a fixed expression over a fixed finite alphabet, the research target is soft-O(n^(25/13)) decision time. The P1 target is soft-O(n^(19/10)); the P2 target is soft-O(n^(25/13)). These remain **targets**, not the running-time guarantees of `FullMatcher`.

## What is proved

### Arbitrary expressions: complete compilation and decision

`CompleteNormalization.normalization` constructs a finite list of concrete DFA normal forms and proves exact language preservation for every source expression. DFA closure, marker-boundary factorization, control-shape classification, unused captures, and initial empty references are included. There is no supplied normal-form or DFA-existence premise.

`FullMatcher.compile_correct` and `FullMatcher.correctMatcher` prove the original `Spec.CorrectMatcher` contract for an actual executable matcher. Compile the fixed pattern once with `FullMatcher.compile`, then reuse `FullMatcher.run` on input words. This correctness result does not establish a subquadratic bound. Pattern preprocessing can be very large.

### Generated periodic branches

- `SmallPeriodRuns` constructs all maximal runs with least period at most Q, without taking a run list or an LCE oracle as input. It proves exact membership, uniqueness, and an O(nQ^3) comparison count.
- `RunBudget` proves total run mass at most `2*n*(Nat.log2 n+1)` by injectively charging primitive-square occurrences. `PeriodicBudgets` derives cubic-run phase budgets.
- `BoundaryContexts`, `PeriodicCache`, and `PhaseEqualityCache` materialize exterior DFA states, periodic transfers, and short equality tests. They avoid rescanning the text prefix, suffix, or period word at every phase.
- `ExactKeys` implements a deterministic finite-alphabet trie with stable collision-free ranks, shared per-run phase arrays, and polynomially bounded integer join keys.
- `SmallPeriodP2` constructs and evaluates the five-phase branch. It is sound for all generated candidates and complete for its stated cubic-run, long-outer witness class. Its actual projection/decision counter is at most `C_P * Q^4 * (2*n*heightFor n)`.
- `P1Events` constructs actual cached source and target events and runs the chronological DFA-gap join. `SmallPeriodP1.solve_sound` proves unconditional soundness. `solve_complete_long` proves completeness for long inner sources. `P1ShortBranch` handles arbitrary earlier short sources with full-word trie keys. `P1Cubic` and `CountedP1Cubic` combine both branches, proving completeness for the entire stated cubic-run, long-outer target class without an inner-length restriction. The long-branch source and target counts are at most `3*Q*mass` and `3*Q^3*mass`, where `mass = 2*n*heightFor n`.
- `CountedProjection` instruments the structural work inside integer projection. `PhaseMagnitude` and `P1Magnitude` bound every projection stage's affine constants by `C_P*(n+2)`, hence O(log(n+2)) bits for a fixed pattern.
- `CountedSort` and `CountedJoin` measure stable sorting inside the actual chronological join. `ActualModulus` computes an LCM from emitted formulas, keeping finite-family proof envelopes out of the executable path.
- `ThresholdBudget.ledger_target` verifies integer-rounded thresholds and the exponent of the explicit numeric phase ledger. It does not establish a matcher running time.
- `PeriodicAccounting.measured_target` now applies the target exponent to the sum of the **actual returned counters** of both cubic P1 paths and the P2 phase matcher. Formula assembly and a complete machine-cost semantics remain separate.
- `ArrayText` supplies a materialized-array input adapter with defined out-of-range reads, and transfers P2 correctness and measured bounds to finite input words.

### Concrete global indexing and coverage

`RankIndex` constructs exact rank-doubling arrays by binary-trie interning. `LCEIndex` and `LCEIndexArray` implement logarithmic LCE/LCS queries, including finite-word correctness and counters for the actual descent. `IndexedGrid` uses one shared forward/reverse preparation and covers every outer-copy pair of length at least the grid stride.

`RankIndexDivisors`, `RankIndexPeriod` and `RankIndexRuns` enumerate sampled runs of **all periods**. A minimum-period test checks only precomputed divisors of the equality-strip displacement, using an indexed LCE for each. `RunDedup` removes duplicate run triples with a fixed-width binary trie; it never scans the growing output list. `RankIndexSchedule` proves validity, uniqueness, long-run coverage and the actual low-start/large-period schedule bounds. These operations do not scan the total lengths of arbitrary runs.

`IndexedGlobalCoverage.p1_cover` and `p2_cover` start from the original matching semantics. Each match is accepted by the implemented small-period branch or enters a residual class with membership in the **actual generated** strip/run schedule. The residual matching queries remain to be connected. `RankIndexScheduleAccounting.measured_target` proves the target exponent for the index preparation, divisor, query, probe and deduplication counters, at the integer-rounded stride.

### Persistent boundary and masked-index components

`BoundaryIndex` materializes finite DFA-state/color tables. Its persistent balanced tree supports arbitrary noninjective color maps, earlier-prefix queries, insertion and replacement. The counted small-to-large merge schedule imports only the light child's listed endpoints and shares one prepared static text tree. Boundary-cut and fixed-end modules include exact endpoint and reversed-label semantics; no inverse DFA transition is assumed.

`BoundaryIndexMixed` includes silent source leaves when selecting the heavy child, while importing only target endpoints. It proves the total-mass light-path bound and the corresponding transfer/operation bounds. This removes the mismatch between target-only merging and a trie containing both sources and targets; building the trie application is still separate.

`MaskedReporting` proves exact output-sensitive reporting, including failed existence queries and output copying. Its source deletions preserve the supplied target mask. `MaskedEventBudget` verifies small-to-large endpoint transfers and bounds the creation and retirement of local density/overlap threshold records; the bound requires one-shot event processing. These components are not yet the complete arbitrary-mask index.

`MaskedFiniteAction` and its persistent tree implement vectors of finite-state matrix summaries with lazy noninjective precomposition. `MaskedFiniteActionMaps` constructs the full finite DFA-map universe of size `m^m` and proves the common-prefix shortening action for different local anchors. The vector size depends only on the DFA, not the input length or a run period. Applying those summaries to the actual cluster geometry and arbitrary-mask predicates remains open.

The [proof ledger](docs/PROOF_MAP.md) records exact scopes, new modules, and remaining obligations. Earlier milestone notes are preserved in [the historical ledger](docs/PROOF_HISTORY.md).

## Reproduce

Pinned toolchain: `leanprover/lean4:v4.19.0`. No Mathlib dependency.

```sh
bash scripts/check.sh
bash scripts/audit.sh
bash scripts/index-audit.sh
```

`check.sh` builds the umbrella module, executes regressions, prints principal theorem dependencies, and rejects proof placeholders and custom assumptions. The nine Python audits are independent finite reference tests. `index-audit.sh` exercises the compiled persistent trees, reporting, LCE/LCS, grid and sampled-run/dedup paths. Finite audits do not prove asymptotic complexity.

The current continuation is checked locally. Remote CI for the new continuation is a separate publication step; do not infer that it ran from an older PR's status.

## Remaining global work

The final matcher instance of `Spec.Target25Over13` needs the remaining masked-cluster algorithm and its event scheduler, the boundary index's compressed-trie/heavy-path construction, the residual matching-query dispatch, and a unified worst-case machine-cost proof. Global geometric coverage and sampled all-period run generation are now implemented and verified. The primitive data structures still need their complete application invariants and aggregate query counts. A semantic reference implementation that enumerates lengths or occurrences does not provide those bounds.

The general Presburger implementation can still create large fixed-pattern DNFs; small text size alone does not imply fast execution. Correctness and finite worst-case bounds do not constitute a practical performance guarantee. See [the recorded runtime probes and limits](docs/RUNTIME_LIMITS.md), including both completed probes and interrupted runs.

Operation counters currently describe specified abstract work. Integer arithmetic is charged as a primitive operation; cached descriptor assembly, runtime allocation, reference counting, garbage collection, and full word-RAM execution are separate obligations. No headline speedup, novelty, priority, or optimality is asserted.
