# REWB Formal

Lean 4 formalization and reproducibility repository for a proposed strongly subquadratic algorithm for fixed-pattern, dynamically 2-use, single-register regular expressions with backreferences.

**Research in progress. The headline complexity bound is not a kernel-verified theorem.** This public repository records proof attempts, reference audits, and precise unresolved obligations. No novelty, priority or optimality is asserted.

## Research question

For a fixed expression over a fixed finite alphabet, with at most two executed references on each successful trace, decide whether a word of length n is accepted. The register stores the most recently closed capture; starting another capture does not clear it. Nested captures include recalled text, and the initial register is empty. This is a theoretical semantics, not a claim about all regex engines.

| Shape | Candidate upper bound |
| --- | --- |
| Independent captures | soft-O(n) |
| P1: A(B)x C(D\\x F)x G\\x H | soft-O(n^(19/10)) |
| P2: A(B(C)x D\\x F)x G\\x H | soft-O(n^(25/13)) |
| Fixed 2-use 1-REWB | soft-O(n^(25/13)) |

Soft-O hides polylogarithmic factors. Constants depend on the fixed pattern.

## Layout

- REWB/Core.lean: DFA composition and transition preimages.
- REWB/Semantics.lean: event traces, nested capture stack, dynamic use count.
- REWB/NormalForms.lean: exact four fixed forms and conditional supplier interval classification.
- REWB/Reductions.lean: disjoint identical-region reduction.
- REWB/Cost.lean: exponent arithmetic only.
- REWB/Specifications.lean: open matcher, normalization and index contracts.
- REWB/Reference.lean: executable split-enumeration reference matchers and correctness statements.
- REWB/MarkedDP.lean: marked-end absorption and single-switch dynamic programming.
- REWB/TraceFacts.lean: balance and dynamic-use invariants for arbitrary traces.
- REWB/OuterColumn.lean, REWB/NestedColumns.lean: common-suffix transport and exact nested endpoint reductions.
- REWB/RangeProducts.lean, REWB/MarkedTransfer.lean, REWB/MatrixTable.lean: executable ordered range products and materialized Boolean transition relations.
- REWB/DyadicIndex.lean: arbitrary interval index with logarithmic routing, at most one monoid multiplication, and checked construction counts.
- REWB/LCSTable.lean: quadratic-space common-suffix table with checked comparison count and clipped maximum.
- REWB/IndexedMarked.lean: P2 indexed query, conditional on its First2 mask.
- REWB/OrderedExit.lean, REWB/P1Index.lean: P1 two-range indexed query, conditional on its Ready mask.
- REWB/MaskScan.lean: materialized forward and backward DFA scans, with correctness of Ready and First2 given correct input masks.
- REWB/IntervalDFA.lean, REWB/SeedBuckets.lean, REWB/OuterTables.lean: executable LCS-derived outer seeds and complete Outer/Ready tables.
- REWB/Integrated.lean: complete executable P1 and P2 decisions with unconditional correctness against MatchesWithin.
- REWB/EndpointCounts.lean: instrumented endpoint loops with verified quadratic candidate-test bounds.
- REWB/FlatIndex.lean, REWB/Microblock.lean, REWB/BlockIndex.lean, REWB/BlockMatcher.lean: direct-addressed range products and complete nested matchers with checked correctness.
- REWB/LiveCapture.lean, REWB/PrunedSkeletons.lean, REWB/LiveLanguage.lean, REWB/LiveCompiler.lean, REWB/CodeInterpretation.lean: exact dead-capture elimination and regular marked-code compilation with at most 3k retained markers.
- REWB/Periodic.lean, REWB/PeriodicFactor.lean: Fine–Wilf, maximal equality regions, phase block and DFA transfer compression.
- REWB/FiniteOrbit.lean: executable finite-state cycle search and ultimately periodic exponent sets.
- REWB/ClusterGeometry.lean, REWB/PeriodicCoordinates.lean: dense occurrence gaps, long-factor phase alignment, quotient/phase coordinates, and regular factor descriptors.
- REWB/PeriodicSystem.lean: joint regular/equality constraints over shared periodic endpoints (check current CI).
- REWB/Tests.lean: regression examples and theorem dependency reports.
- audits/: nine Python reference audits.
- docs/PROOF_MAP.md: proof obligations and dependency map.

## Reproduce

Pinned toolchain: leanprover/lean4:v4.19.0. No Mathlib dependency.

```sh
bash scripts/check.sh
bash scripts/audit.sh
```

The complete nested-form matchers and endpoint-test bounds passed Lean 4.19 kernel checks and all nine Python reference audits at PR #6 (Actions run 45401399876). Their correctness theorems do not require externally supplied masks. PR #7 additionally verifies direct-addressed block range queries and both blocked matchers. PR #8 verifies the regular marked-code compiler, but the final finite union of DFA normal forms is still an obligation. The periodic core through PeriodicCoordinates passed CI at 624c2c4c407258d25499b8ca6c3ccc878fcf7418 (run 45410262387). A full machine-level cost proof, general normalization into the concrete normal forms, the global run and boundary indexes, Presburger projection, and the headline exponent remain open. No unresolved proof placeholders or custom axioms should be used to bypass the proof obligations. Python audits are independent finite tests; they do not validate the claimed asymptotic bounds.

## Next milestones

1. Complete the machine-level cost proof for the verified blocked matchers.
2. Convert the verified regular marked-code syntax to finite DFA factor languages and finish the normal-form coverage theorem.
3. Use the verified periodic geometry and exponent descriptors to build the actual small-period P1/P2 solvers; prove joint integer projection, source/target joins, and run-count bounds.
4. Verify the masked all-start and boundary-aware indexes, including dynamic cluster maintenance and amortization.
5. Combine correctness, coverage, and actual cost inequalities into the final theorem.

See [the proof ledger](docs/PROOF_MAP.md).
