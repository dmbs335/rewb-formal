# Construction-cost proof continuation

The validated parent checkpoint is
`0f4ef40210db753fe143046bf7312ce7b619aaaf`, published in draft PR #14.
Its actual six-form matcher correctness and concrete returned-ledger
25/13 target are kernel-checked. This is not a machine-running-time theorem.

## Recovery and validation

The execution environment became unavailable on 2026-11-25. Complete
retained tool payloads and reads were used to preserve 33 in-progress
Lean modules. Their inaccessible working-tree hashes could not be
compared. Historical PASS observations and later fresh remote checks are
distinguished in the records linked below.

The first recovery commit `be6c2e1` preserved 24 modules. Its
initial/join CI job passed 438 targets and 58 principal axiom checks.
The next commit `41bcc9b` removed a redundant tactic in the periodic
preparation proof and added an actual-join executable comparison; its
dedicated recovery workflow passed.

The following integration preserves the remaining nine Cut modules,
adds three explicitly **new implementations** of unavailable original
Bank/Updates/Erase sources, installs finite Cut operations in a new
three-module initialization path, and adds two actual P1 branch modules.
These additions require their own kernel/runtime results; writing them
does not count as validation.

## Dedicated build groups

The **Construction recovery kernel checks** workflow builds explicit
targets and prints their principal theorem dependencies:

- initial-and-join: the recovered initial path and actual chronological
  join; also runs its bounded full-counter/work/literal-witness comparison.
- periodic-actual: choices, P2, events, measures, short events, and preparation.
- finite-cut: all nine measured Cut modules.
- finite-initial: the new initial path using measured Cut build, tail and
  whole periodic queries.
- full-executor: actual bank compilation, repair, clipping, erase, window
  queries, reporting, and the complete band/edge/plan traversal.
- periodic-branch: actual long/short P1 preparation plus chronological join,
  the cubic branch, and their concrete ledger target.

The unchanged parent workflow also runs on pushes. The dedicated groups
do not yet establish installation throughout the full matcher.
Axiom audits and bounded executable comparisons have different scopes;
neither is described as a machine-cost refinement.

## Records

- [Remote validation](RECOVERY_VALIDATION.md)
- [Initial and join source provenance](RECOVERY_ROOT.md)
- [Periodic actual source provenance](RECOVERY_PERIODIC_ACTUAL.md)
- [Cut construction source provenance](RECOVERY_CUT_CONSTRUCTION.md)
- [Full-cost executor source provenance](RECOVERY_FULL_COST_EXECUTION.md)
- [Fresh dependency implementations](REIMPLEMENTATION_FULL_COST_DEPENDENCIES.md)

The draft PR head remains at the validated parent while this continuation
is checked. No merge is performed.
