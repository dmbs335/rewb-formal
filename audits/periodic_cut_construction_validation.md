# Cut construction validation follow-up

These files are new validation work, distinct from the source-only recovery recorded in `docs/RECOVERY_CUT_CONSTRUCTION.md`.

## Status at submission

The execution environment remains unavailable. This audit and the four kernel regressions have been written for fresh CI execution; their results are pending at the time this tree is submitted. No runtime counts or successful audit outcome are asserted here.

Root reported that the recovered `PeriodicConstructionCutPhase` module passed dedicated CI at commit `3334873b9287c8836c880ab547ed5455d3d4a715`. That CI exposed a final `buildDFA_work` proof-normalization failure in `PeriodicConstructionCutBuild`. The separate follow-up adds only:

```lean
dsimp only [summaryProducts] at hb
```

after `rw [hlen2,enum_cardinality] at hb`. This unfolds the same structure in the existing bound hypothesis and the goal. It does not change any executable value or returned counter. A fresh build must verify the correction.

## Reproducible commands

```sh
lake build REWB.PeriodicConstructionCutRegression
lake env lean audits/periodic_cut_construction_axioms.lean
lake env lean --run audits/periodic_cut_construction_smoke.lean
```

The principal report covers all 108 named theorems in the nine Cut construction modules plus the four new regressions. It is intended to be checked for standard Lean axioms only.

## Runtime coverage

The bounded smoke program checks:

- All Boolean words of lengths zero through three, with universal automata and a two-state noninjective automaton placed independently in B, C or E.
- Entire materialized dyadic trees, including every stored summary/table, against the original builder; the old product counter and new construction bound are checked separately.
- Every bounded range and two deliberately invalid ranges, preserving the complete old answer/products/visits record and satisfying the new cost bound.
- Every closed cut window `l <= a <= b <= r <= n`, including epsilon cuts and empty text. Every finite matrix cell is checked against independently enumerated literal text cuts.
- Full, interior and constrained ending tuple outputs, including original list order and counters, plus their construction bounds.
- Full periodic phase records and guarded text queries against the original execution, using empty, short, sparse and all-true target masks. Actual text witnesses are checked independently where the periodic source contract holds.
- A 257-symbol repeated-word build and selected deep partial/endpoint windows.

Only the audit enumerates text positions or literal cuts. The production functions remain the measured implementations in `PeriodicConstructionCut*.lean`.

## Remaining review

Generated-code inspection and integration into the full public solver still need their own recorded outcomes. Structural-operation counters are not native CPU, allocation/GC or bit-complexity measurements.
