# Short outer P1/P2 consumer audit

The consumer family reuses the frozen nine-module short-outer band index.
It constructs actual factor-state rows, actual backwards F-ready rows,
concrete source/target event lists, and the existing concrete dyadic join.
There is no supplied query function or supplied cost function.

## Reproduction

```sh
lake build REWB.ShortOuterCost REWB.ShortOuterRegression
lake env lean --run audits/short_outer_solver_smoke.lean
lake env lean -c /tmp/short_outer_p1events.c REWB/ShortOuterP1Events.lean
lake env lean -c /tmp/short_outer_p2events.c REWB/ShortOuterP2Events.lean
lake env lean -c /tmp/short_outer_ready.c REWB/ShortOuterReady.lean
lake env lean -c /tmp/short_outer_regular.c REWB/ShortOuterRegular.lean
lake env lean -c /tmp/short_outer_p1.c REWB/ShortOuterP1.lean
lake env lean -c /tmp/short_outer_p2.c REWB/ShortOuterP2.lean
```

The same C generation was also run for `ShortOuterPrepared` and
`ShortOuterJoin`. All eight files compiled successfully.

## Runtime coverage

The independent reference enumerates literal outer-copy starts, lengths,
second-copy starts, and all inner cuts. It runs each DFA directly on the
resulting slices and compares actual words. It does not use the key
dictionary, suffix table, F-ready table, event generator or join.

The run passed 63 binary texts and 16,320 P1/P2 comparisons, across
sixteen deterministic patterns and every tested short-length limit,
including zero and limits larger than the text. There were 1,660
positive P1 results and 1,229 positive P2 results. All explicit solver
work bounds passed. Total measured audit time was 65.55 seconds.

Deep repeated-input executions also passed:

| Text length | Limit | P1 work | P2 work |
| --- | --- | --- | --- |
| 512 | 16 | 106,879,097 | 122,891,175 |
| 1,024 | 8 | 73,014,891 | 66,352,474 |

A separate length-1,027 input has its earlier P1 source at position zero
and the target outer copy near the end. With limit two, the actual P1
solver accepts and the P2 solver rejects. This checks that the P1 source
list is global even though target outer windows are short.

Kernel regressions cover empty text, empty outer captures with a
nonempty G gap, empty P2 inner capture, strict outer-length limits, zero
limit and the distant earlier P1 source.

## Generated execution shape

- Neither P1 nor P2 event predicates contain a text-segment constructor,
  a list-length traversal, or a direct DFA word run. They call the
  materialized regular/ready tables and the direct exact-key lookup.
- Regular rows and F-ready rows construct one word of the cached bounded
  width per physical start. These scans are preprocessing costs.
- `Ready.query` reads the outer array and one backwards answer array;
  its returned work is at most seven.
- P1 performs one join on the complete original word, retaining every
  admissible earlier source. P2 performs one join on a word of the
  bounded width per accepted outer-prefix position.
- P2's final list-length traversal is over its one-Boolean-per-start
  result list. The solver explicitly charges both this traversal and
  the final Boolean scan. It does not scan the whole text per event.
- The join ledger retains actual sorting, comparison/scan, event, text
  and node counters. Its fixed coefficient charges DFA cut-vector work
  and the fixed `[[]]`, modulus-one, exponent-zero formula conversion.
  Height times visited nodes covers its power/split control. The final
  cost theorem is about this concrete word-RAM ledger; it is not a
  formal accounting of allocator, garbage collector or bit-level costs.

## Closed bound

Let `b = min L (n+1)` and `S = (n+1)*(b+1)^2`. For P1 use the C DFA's
state count `k`; for P2 use the D DFA's state count. Both executed solver
ledgers are bounded by

```
(preparationConstant P + joinConstant k + 200)
  * S * (log2(n+1)+2) * (log2((k+1)*S)+1).
```

The proof includes key preparation, all regular/F-ready rows, list/event
construction and joins. The residual-dispatch substitution theorems
replace the short-witness branch with these actual solver answers.
Other scheduled boundary/one-use branches retain their existing exact
interfaces and separate row-construction obligations.
