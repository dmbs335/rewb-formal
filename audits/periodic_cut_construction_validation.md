# Cut construction validation

These validation files are follow-up work, distinct from the source-only recovery recorded in `docs/RECOVERY_CUT_CONSTRUCTION.md`. Original filesystem byte/hash identity remains unverified; the recovered GitHub sources themselves have now passed fresh validation.

## Verified source and execution

Verified commit: `cfead9ae7031656d8ec5e89b9872f6a4ba020f1f`.

- [Recovery CI run 45594456698](https://github.com/dmbs335/rewb-formal/actions/runs/45594456698).
- [Finite-cut job 139136754568](https://github.com/dmbs335/rewb-formal/actions/runs/45594456698/job/139136754568): success.
- All nine `PeriodicConstructionCut*.lean` implementation modules and `PeriodicConstructionCutRegression.lean` built successfully.
- All 112 principal reports passed with only `propext`, `Classical.choice` and `Quot.sound` where required.
- The actual `lake env lean --run` audit completed successfully in 107,149 ms.

The final `buildDFA_work` proof needed only the separately recorded normalization `dsimp only [summaryProducts] at hb`. No executable definition or counter changed. The regression target also explicitly imports the two additional audit dependencies, so the reproducible build command below creates every required object file.

## Reproducible commands

```sh
lake build REWB.PeriodicConstructionCutRegression
lake env lean audits/periodic_cut_construction_axioms.lean
lake env lean --run audits/periodic_cut_construction_smoke.lean
```

The principal report covers all 108 named theorems in the nine Cut construction modules plus four kernel regressions.

## Runtime results

The successful job printed:

```text
cut small: builds=60, ranges=564, windows=1404, literal cells=17199, tuple queries=1280
cut phases: guarded=241, full phases=24, accepted=39
cut deep: n=257, products=2313, construction work=485646, windows=5
periodic cut construction audit passed in 107149 ms
```

The bounded audit checks:

- All Boolean words of lengths zero through three, with universal automata and a two-state noninjective automaton placed independently in B, C or E.
- Entire materialized dyadic trees, including every stored summary/table, against the original builder. The old product counter and new construction bound are checked separately.
- Every bounded range and two deliberately invalid ranges, preserving the complete old answer/products/visits record and satisfying the new cost bound.
- Every closed cut window `l <= a <= b <= r <= n`, including epsilon cuts and empty text. Every finite matrix cell is checked against independently enumerated literal text cuts.
- Full, interior and constrained ending tuple outputs, including original list order and counters, plus their construction bounds.
- Full periodic phase records and guarded text queries against the original execution, using empty, short, sparse and all-true target masks. Actual text witnesses are checked independently where the periodic source contract holds.
- A 257-symbol repeated-word build and selected deep partial/endpoint windows.

Only the audit enumerates text positions or literal cuts. The production functions remain the measured implementations in `PeriodicConstructionCut*.lean`.

## Scope

These results certify the local Cut construction/query replacement and its returned structural-operation bounds. They do not, by themselves, certify the complete public solver's combined ledger. Caller integration and other primitive ledgers have their own modules and reports.

This finite-cut job did not perform a standalone generated-C inspection. Structural-operation counters are not native CPU, allocation/GC, reference-counting or bit-complexity measurements.
