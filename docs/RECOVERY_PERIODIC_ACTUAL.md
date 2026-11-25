# PeriodicActual source recovery — 2026-11-25

This snapshot preserves the eight new PeriodicActual modules owned by
`/root/all_start_index` when the execution environment became unavailable.
It is source recovery, not a validated publication checkpoint.

## Provenance and limits

The source was reconstructed from the complete apply_patch contents and
subsequent edits retained in the active conversation. No new proof edits
were made during recovery. The unavailable environment prevented reading
the current local files or comparing their hashes, so byte identity with
the inaccessible working tree is **unverified**.

The statuses below describe the local build outcomes observed before the
outage. They do not certify this reconstructed remote snapshot: it must
be rebuilt after checkout. No runtime regression or principal-axiom audit
was completed for this new eight-module family.

Only a Git tree object was requested from this recovery agent. It did
not modify a reference, branch, commit, pull request, or the existing
validated head. The coordinating agent owns subsequent recovery-branch
assembly.

## File status

| File | Last observed local status |
| --- | --- |
| `REWB/PeriodicActualChoices.lean` | Kernel build PASS. |
| `REWB/PeriodicActualP2.lean` | Kernel build PASS, including the later proved csimp folds. |
| `REWB/PeriodicActualP2Cost.lean` | Kernel build PASS. |
| `REWB/PeriodicActualEvents.lean` | Kernel build PASS. |
| `REWB/PeriodicActualMeasures.lean` | Kernel build PASS. |
| `REWB/PeriodicActualShort.lean` | Kernel build PASS. |
| `REWB/PeriodicActualPrepare.lean` | Kernel build PASS as a dependency of the subsequent PrepareCost build. |
| `REWB/PeriodicActualPrepareCost.lean` | Last revision UNCONFIRMED. The preceding revision had explicit proof errors and an elaboration heartbeat timeout. Those sites were edited, then build session 13792 was started; the environment failed before its final output was obtained. |

None of the new family is labelled runtime PASS. The draft PrepareCost
proofs must not be cited as kernel-verified until a new build succeeds.
There is no `sorry`, `admit`, custom axiom, or `native_decide` in the
reconstructed source; a formal audit is still pending.

## What the locally checked modules establish

- Choices executes the actual P2 five-phase and P1 three-phase schedules
  using counted range/map/flattening operations. For positive q the P2
  schedule work is at most 39 q^5; the P1 phase schedule is at most
  23 q^3. No exponent-value loop is introduced.
- P2 replaces each phase's unmeasured initial formula with the actual
  `PeriodicConstruction.Formula.solveP2`. Its answer equals the existing
  `SmallPeriodP2.solve` answer.
- P2Cost proves the newly returned work is bounded by a pattern-only
  coefficient times the existing `PeriodicAccounting.p2Expr` and height
  factor. This is a theorem about the returned unit-operation ledger.
- Events constructs actual long P1 sources and targets, prepares each
  run cache once, and charges formula construction, projection, schedules,
  list maps and concatenation. Its event lists equal `P1Events`.
- Measures proves uniform formula-measure bounds for actual long events
  and measure exactly 1 for actual short events. These are the inputs to
  the independently owned measured chronological join.
- Short projects once per anchored target phase and tests precisely
  exponents 0, 1, 2, with measured decisions and event construction.
- Prepare builds text, shared contexts, actual run list, keys and events
  once per P1 branch. Short source key creation also charges actual word
  materialization while preserving the complete existing registry result.

Run-discovery, cache-transition and exact-key primitive ledgers retain
their existing scope. These files do not claim machine bit complexity,
GC costs, or an already-integrated replacement of the entire matcher.

## Principal entry points

`REWB.PeriodicActual.P2.solve_value`,
`REWB.PeriodicActual.P2.solve_work`,
`REWB.PeriodicActual.P2.solve_expr`,
`REWB.PeriodicActual.P2.solve_rounded`.

`REWB.PeriodicActual.Events.run_sources`,
`REWB.PeriodicActual.Events.run_targets`,
`REWB.PeriodicActual.Events.runs_sources`,
`REWB.PeriodicActual.Events.runs_targets`,
`REWB.PeriodicActual.Events.runs_work`.

`REWB.PeriodicActual.Short.choice_value`,
`REWB.PeriodicActual.Short.choice_work`,
`REWB.PeriodicActual.Short.runs_value`,
`REWB.PeriodicActual.Short.runs_work`,
`REWB.PeriodicActual.Short.sourceKeys_value`,
`REWB.PeriodicActual.Short.sourceKeys_work`.

Both `REWB.PeriodicActual.Long` and `REWB.PeriodicActual.Short` export
`prepare_text`, `prepare_sources`, `prepare_targets`,
`prepare_modulus`, and `prepare_work`.

## Resume sequence

1. Rebuild all eight modules, starting with the unconfirmed
   `PeriodicActualPrepareCost` target. Recover the local logs if available.
2. Run the new family's principal axiom audit and bounded executable
   comparisons; do not silently replace a timed-out test with PASS.
3. Add the planned new branch wrapper invoking the coordinator's
   `PeriodicActual.Join.run`. That wrapper had not been written at the
   time of the outage.
4. Prove actual P1 branch answer preservation and combine preparation,
   existing join counters, and the measured join's extra work.
5. Connect the new periodic branch executables into the residual matcher
   through value-preserving new modules; the frozen old matcher was not
   changed by this work.

The intended join API is
`PeriodicActual.Join.run d K N w es fs : CountedJoin.Result × Nat`,
with full-result preservation and an additional construction ledger.
Long uses a common formula bound
`p1SourceBudget P + p1TargetBudget P` and modulus upper bound
`p1Modulus P`; short uses bound 1 and modulus 1.

## Local log names (not recovered as files)

- `/tmp/rewb-periodic-actual-choices.log`
- `/tmp/rewb-periodic-actual-p2.log`
- `/tmp/rewb-periodic-actual-p2-cost.log`
- `/tmp/rewb-periodic-actual-events.log` (also includes the Measures build)
- `/tmp/rewb-periodic-actual-short.log`
- `/tmp/rewb-periodic-actual-prepare.log`
- `/tmp/rewb-periodic-actual-prepare-cost.log` (last revision unconfirmed)

The transport failure was reported as
`exec-server transport disconnected; recovery timed out after 45s`.
The single follow-up process request reported
`No usable execution environment is available`.
