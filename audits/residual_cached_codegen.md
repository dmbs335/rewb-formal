# Residual cache execution audit

The production definitions are `ResidualCached.P1/P2.build`, `query`, and
`execute`. The smoke audit supplies the pending finite all-start rows by an
independent cut enumeration. That fixture is deliberately outside the claimed
production ledger and is not an implementation of the missing fast row producer.

## Reproduction

From the repository root, run:

```sh
lake build REWB.ResidualCachedRegression
lake env lean --run audits/residual_cached_smoke.lean
lake env lean -c /tmp/residual_cached_variants.c REWB/ResidualCachedVariants.lean
lake env lean -c /tmp/residual_cached_p1.c REWB/ResidualCachedP1.lean
lake env lean -c /tmp/residual_cached_p2.c REWB/ResidualCachedP2.lean
lake env lean -c /tmp/residual_cached_dispatch.c REWB/ResidualCachedDispatch.lean
```

## Generated execution paths

`P1.execute` and `P2.execute` each convert the materialized input array to a list
once, then execute the periodic branch, the short-outer solver, the concrete
residual schedule, and one cache-bank build. The final window loop closes over
that already-built bank. Its callback is `P1.query` or `P2.query`; it does not
call the bank builder.

`P1.queryState` makes three `Table.get` calls, and `P2.queryState` makes four.
Each reads the concrete DFA variants stored in its cell and invokes the frozen
boundary or one-use cache query. These function bodies contain no DFA `join`,
`meet`, `reverse`, cache build, `List.length`, or substring construction call.

The shared `select` body invokes two stored `Range.query` indexes and the stored
`FarSelection.key` index. Its suffix endpoint is the cached length field. It
does not traverse the original word. The actual finite G-state list is stored
by preprocessing and reused by every query.

The checked compiler simplification replaces `any` with `anyTail`. The generated
loop has one `lean_apply_1` before its accumulated-answer branch and then a tail
`goto` in both branches. Thus every callback is executed exactly once, including
after an earlier positive result, and every returned work count is added.
`Regression.any_all_called` checks this behavior in the kernel.

## Audit coverage and scope

The smoke audit compares both cache-query results with an independent absolute
cut search on every separated equality window of every binary word of length
at most two, at two cache widths. It also checks full residual dispatch against
independent P1/P2 matching cuts, every bank/query/residual work bound, an empty
input, zero-length windows, a positive-only regular factor, rejecting suffixes,
and noninjective DFA transitions. A repeated word of length eight exercises
the actual combined pipeline. A separate two-state A/G/H selector audit checks
the shared range maps and final-subset selection, avoiding an unnecessarily
huge nested reversal state universe in the complete bank fixture.

The completed run checked 112 small-input bank builds, 718 independent
P1/P2 window-query comparisons including the repeated-word profile, 22
noninjective selector cases, and 58 complete P1/P2 dispatcher executions.
The small-input comparisons included 168 positive and 360 negative answers.
All returned build, query, and residual-work inequalities passed. The run
took 206,446 ms in the recorded environment. The principal manifest contains
61 kernel axiom reports, each using only Lean's standard axioms.

`Ready` remains a necessary hypothesis on the finite input rows. The automatic
25/13 theorem concerns the actual returned `accountedWork` fields: it includes
all residual cache, short-outer, schedule, and selector ledgers, plus the existing
periodic counters. It does not yet include the external all-start row producer
or the older periodic formula/window construction operations excluded by
`PeriodicAccounting`. The next measured construction family addresses the
latter separately; this checkpoint does not relabel those missing operations
as already measured.
