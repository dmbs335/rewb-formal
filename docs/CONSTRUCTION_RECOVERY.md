# Construction-cost proof recovery

This branch continues from the validated checkpoint
`0f4ef40210db753fe143046bf7312ce7b619aaaf`. It preserves in-progress
construction-accounting sources after the execution environment became
unavailable on 2026-11-25.

## Validation boundaries

The parent checkpoint has a successful local 694-target kernel gate,
2,343 principal axiom reports and 83 completed compiled probes. Its actual
six-form matcher correctness and concrete returned-ledger target are
published in draft PR #14. This is not a machine-running-time theorem.

The newly preserved source texts were reconstructed from complete retained
tool payloads and reads. The inaccessible original working-tree hashes
could not be compared. Historical local PASS records are listed in the
family documents; they do not certify the reconstructed snapshot.
This branch's dedicated **Construction recovery kernel checks** workflow
rebuilds its explicitly named modules and prints principal axiom
dependencies. The unchanged parent workflow also runs on branch pushes.

The first recovery commit contains 24 Lean modules:

- Initial scan, runs, and start accounting: 3 modules.
- Actual chronological join, split, DFA cut, and extra-work bound: 5 modules.
- Periodic choices, P2, events, measures, short branch, preparation:
  8 modules.
- Full-cost window/report/repair/clip/collect/execution source: 8 modules.

The first two groups are built in the `initial-and-join` CI job. The
periodic group is built in `periodic-actual`. The executor group is not
yet a complete build target: the original Bank/Updates/Erase texts were
not available in retained context, and the Cut family is being preserved
separately. Missing originals must not be guessed and called recovered.
Fresh replacements will be separately identified and kernel-checked.

## Family records

- [Initial and join provenance](RECOVERY_ROOT.md)
- [Periodic actual provenance](RECOVERY_PERIODIC_ACTUAL.md)
- [Full-cost executor provenance and missing APIs](RECOVERY_FULL_COST_EXECUTION.md)

The source ledger still needs installation into the full matcher, followed
by kernel, axiom, generated-code, and bounded executable comparisons.
No merge is performed by this recovery work. The validated draft PR head
remains at the parent checkpoint while the recovered work is checked.
