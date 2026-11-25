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
