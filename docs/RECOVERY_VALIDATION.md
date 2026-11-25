# Remote recovery validation

## be6c2e1933a5311764459fd22ff8d0fb9e6135f8

The dedicated [remote kernel run](https://github.com/dmbs335/rewb-formal/actions/runs/45590727589)
rebuilt the reconstructed snapshot.

- Initial/join: **438 targets PASS**, **58 principal axiom reports PASS**.
  Every reported dependency is drawn from propext, Quot.sound and
  Classical.choice.
- Periodic actual: the first 111 targets, including P2Cost, passed.
  PrepareCost failed only because an extra tactic followed a goal already
  discharged by definitional simplification (line 176, "no goals to be
  solved"). The redundant tactic is removed in the next revision.
- These are kernel/axiom results. The new chronological-join execution
  comparison is added in the next revision; it has not run at this entry.

Historical workspace results remain documented in the family recovery
records. The CI result above validates the reconstructed GitHub snapshot
directly and does not establish byte identity with the unavailable
workspace.

## cfead9ae7031656d8ec5e89b9872f6a4ba020f1f

[Construction workflow](https://github.com/dmbs335/rewb-formal/actions/runs/45594456698):

- Public measured all-start solver: build and 24 principal reports PASS.
  This includes the actual prepare/plan composition, entire-old-result
  equality, unconditional correctness, and the concrete O_P(n log^3 n)
  ledger bound.
- Full executor: build, 90 principal reports and the first generated-C
  diagnostic PASS. Stronger per-return-path checks are added next.
- Finite Cut: build, 112 standard-axiom reports and executable checks PASS:
  60 builds, 564 ranges, 1,404 windows, 17,199 literal cells, 1,280 tuple
  queries, 241 guarded queries, 24 full phases, 39 hits and the n=257
  deep fixture. Runtime 107,149 ms.
- Actual periodic branches: build and 34 principal reports PASS.
- Actual periodic residual constructors: build and 38 principal reports PASS.
- Full-row table: one dependent-vector normalization failed; the next
  revision contains a proof-only correction and the full row/input family.
- The first periodic runtime diagnostic was left unfinished after it
  mistakenly evaluated proof-only uniform coefficients and their enormous
  finite families. Those computations are not part of the production
  matcher. The next diagnostic keeps the actual value/counter/event/literal
  checks and removes only execution of proof-only bounding constants.
  The unfinished diagnostic is not a runtime PASS or a production
  algorithm timeout.

The parent 0f4ef40 serial full CI jobs were cancelled at about the
configured 40-minute limit after successful kernel/axiom and Python
checks, while the 83-probe runtime list was still executing. The recovery
workflow now partitions that unchanged, 83-unique-name list into
28/28/27 probes after the kernel gate. Default local script execution
still runs every probe. Generated-code routing runs in shard 0.
