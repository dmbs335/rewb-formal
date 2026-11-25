# Periodic cache construction validation

The new files refine the actual periodic DFA tables, equality tables, exterior-context builder and per-run shared-cache builder. Every public wrapper preserves the entire original value and its legacy counter. Its second component adds a concrete structural-operation ledger, including source reads, DFA transitions, list cells, state domains, row traversal, list-to-array materialization and scalar assembly.

## Verified status

Verified commit: `8614bf808df5bbb5f73bd629951f01617923fa6c`.

[Recovery CI run 45601488591, periodic-cache job 139161245512](https://github.com/dmbs335/rewb-formal/actions/runs/45601488591/job/139161245512) completed successfully. All five modules built, all 49 principal reports used only standard Lean axioms where required, and the actual runtime audit passed in 1,601 ms.

The final source keeps the original executable/counter definitions. Follow-up corrections repaired the reserved helper identifier, arithmetic proof association, an explicit identity-function reflexivity step, and a regression-only finite-state numeral elaboration. These are recorded in the recovery branch history.

The successful job printed:

```text
periodic cache small: transition tables=1200, literal transition cells=16800, equality tables=300, literal equality cells=7800, contexts=60, preparations=1500
periodic cache deep: n=1024, period=17, transition cells=612, equality cells=5202, old preparation=8670, construction work=114567
periodic cache wide: states=64, zero preparation=72, literal transition cells=128
periodic cache construction audit passed in 1601 ms
```

Selected exact CI output is preserved in `audits/periodic_cache_construction_verified.log`.

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

A separate deep profile uses length 1024 and period 17. A 64-state profile checks that zero-period table/preparation construction retains constant work (6/72), while period one materializes and checks its actual state rows. This exercises the absence of accidental finite-map/template enumeration in the real builder path. Only audit reference code scans literal factors.

## Scope

Symbol reads, DFA transitions and scalar arithmetic use the unit-operation model. Actual production callers provide a shifted `ArrayText.read` closure, so a source read is direct array access. Allocation/GC, reference-counting effects and bit complexity are outside this ledger. Actual installation and the explicit primitive-LCM model are reviewed in `docs/PERIODIC_CONSTRUCTION_AUDIT.md`. These primitive wrappers alone do not claim a complete public solver bound.
