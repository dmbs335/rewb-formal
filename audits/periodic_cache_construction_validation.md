# Periodic cache construction validation

The new files refine the actual periodic DFA tables, equality tables, exterior-context builder and per-run shared-cache builder. Every public wrapper preserves the entire original value and its legacy counter. Its second component adds a concrete structural-operation ledger, including source reads, DFA transitions, list cells, state domains, row traversal, list-to-array materialization and scalar assembly.

## Status

These sources and validation files are submitted for fresh CI; no successful kernel or runtime result is asserted yet. The first core build exposed the reserved identifier `prefix` and an unnecessary post-simplification tactic; the submitted source uses `prefixScan` and guarded arithmetic cleanup.

## Reproduce

```sh
lake build REWB.PeriodicConstructionCacheRegression
lake env lean audits/periodic_cache_construction_axioms.lean
lake env lean --run audits/periodic_cache_construction_smoke.lean
```

The axiom report covers 49 named theorems across the five new Lean modules.

## Public interfaces

Namespace: `REWB.PeriodicConstruction.Cache`.

- `transitions`: exact replacement of `PeriodicCache.build`, retaining its whole pair.
- `equality`: exact replacement of `PhaseEqualityCache.build`, retaining its whole pair.
- `contexts`: exact replacement of `BoundaryContexts.build`, retaining its whole pair.
- `prepareAt`: exact replacement of `BoundaryContexts.countedPrepareAt`, retaining its whole pair.
- Each has a `*_value` theorem and an exact `*_work` formula.
- `contexts_work_le_old` bounds new work by 64 times the old boundary-entry counter.
- `prepareCoefficient P = 1024 * (FullyCachedP2.stateSum P + 1)`.
- `prepareAt_work_le_old` bounds new work by that coefficient times the old preparation counter plus one. The positive-period version `prepareAt_work_le_old_pos` uses twice that coefficient times the old counter.

The transition table bound is quadratic in the period, the equality table bound is cubic, and exterior contexts are linear in text length. The preparation bound covers zero period explicitly; its old counter is zero while the actual empty construction still performs 72 structural operations.

## Audit coverage

The program uses all Boolean words of lengths zero through three and four one/two-state automata, including noninjective transitions. Every transition-table entry is compared with a DFA run on an independently materialized literal factor. Every equality-table entry is compared with literal word equality, including empty and final prefixes.

Shifted source readers include positions beyond the text, with an explicit false fallback. Shared exterior contexts are compared in full and checked against literal prefix/suffix DFA execution. Prepared seven-DFA cache values, both contextual automata, every table, every legacy counter, every exact new work formula and every closed bound are compared.

A separate deep profile uses length 1024 and period 17. Only audit reference code scans literal factors.

## Scope

Symbol reads, DFA transitions and scalar arithmetic use the unit-operation model. Actual production callers provide a shifted `ArrayText.read` closure, so a source read is direct array access. Allocation/GC, reference-counting effects and bit complexity are outside this ledger. Integration into external P1/P2 branch callers is a separate follow-up; these primitive wrappers alone do not claim a complete public solver bound.
