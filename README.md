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
- REWB/Tests.lean: regression examples and theorem dependency reports.
- audits/: nine Python reference audits.
- docs/PROOF_MAP.md: proof obligations and dependency map.

## Reproduce

Pinned toolchain: leanprover/lean4:v4.19.0. No Mathlib dependency.

```sh
bash scripts/check.sh
bash scripts/audit.sh
```

The core modules and both indexed endpoint-query reductions have passed Lean 4.19 kernel checks in GitHub Actions (see the PR and CI history). The reference audits also pass. Check CI for the precise revision. These results do not yet prove a complete quadratic-time matcher or the headline exponent. No unresolved proof placeholders or custom axioms should be used to bypass the proof obligations. Python audits are independent finite tests; they do not validate the claimed asymptotic bounds.

## Next milestones

1. Implement and verify the outer-copy seed table from the LCS and DFA indices, then connect the two nested indexed queries to a complete matcher.
2. Verify direct-addressed interval products, actual cost bounds, and the desired space bounds.
3. Extract selected suppliers from arbitrary traces and prove full normalization.
4. Verify the subquadratic masked all-start and boundary-aware indexes, periodic projection, and concrete word-RAM implementation.
5. Combine correctness, coverage and actual cost inequalities into the final theorem.

See [the proof ledger](docs/PROOF_MAP.md).
