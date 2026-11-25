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
- `ArrayText` supplies a materialized-array input adapter with defined out-of-range reads, and transfers P2 correctness and measured bounds to finite input words.

The [proof ledger](docs/PROOF_MAP.md) records exact scopes, new modules, and remaining obligations. Earlier milestone notes are preserved in [the historical ledger](docs/PROOF_HISTORY.md).

## Reproduce

Pinned toolchain: `leanprover/lean4:v4.19.0`. No Mathlib dependency.

```sh
bash scripts/check.sh
bash scripts/audit.sh
```

`check.sh` builds the umbrella module, executes regressions, prints principal theorem dependencies, and rejects proof placeholders and custom assumptions. The nine Python audits are independent finite reference tests; they do not prove asymptotic complexity.

The current continuation is checked locally. Remote CI for the new continuation is a separate publication step; do not infer that it ran from an older PR's status.

## Remaining global work

The final `Spec.Target25Over13` theorem needs the actual masked all-start and boundary-aware indexes, complete non-small-period dispatch and coverage, and a unified worst-case machine-cost proof. In particular, arbitrary masks and output extraction must be included in the index amortization. A semantic reference implementation that enumerates lengths or occurrences does not provide that bound.

The general Presburger implementation can still create large fixed-pattern DNFs; small text size alone does not imply fast execution. Correctness and finite worst-case bounds do not constitute a practical performance guarantee. See [the recorded runtime probes and limits](docs/RUNTIME_LIMITS.md), including both completed probes and interrupted runs.

Operation counters currently describe specified abstract work. Integer arithmetic is charged as a primitive operation; cached descriptor assembly, runtime allocation, reference counting, garbage collection, and full word-RAM execution are separate obligations. No headline speedup, novelty, priority, or optimality is asserted.
