# Complete boundary cache execution audit

The ten new modules are `BoundaryRangeFarRight{Requests,Rows,Index,Correct,Cost}`
and `BoundaryRangeCache{Grid,,Correct,Cost,Regression}`. They consume the
previously verified near, border, far-left and immutable endpoint
aggregate indexes.

## Exact construction scope

`Cache.prepare` builds every clipped block's three near indexes,
far-left index and actual finite target-mask requests. One shared
same-block border index is built for the entire cache. A request mask is
materialized from a shared K range index and satisfies
`prepare_request_mask`, including the strict condition `g < a`.

`Cache.assemble` consumes a finite vector of all-start output arrays for
those requests. For each block and K entry state it materializes the OR
over the K exit states, builds one backwards aggregate for reversed E,
and retains its endpoint answers. The request's already charged work is
subtracted from the aggregate's cumulative counter, so the two-stage
cache bound charges mask construction once.

The online query chooses one block by division using cached lengths,
queries the two far indexes, and runs the bounded near scans. The
far-right branch makes one K range query to select its entry-state row
and one backwards-aggregate array read at `n-r`. `FarRight.query_correct`
matches the exact original far-right region, and `Cache.query_correct`
matches all of `Spec.boundaryRange`, including invalid ranges, terminal
epsilon captures and first copies beginning before the left boundary.

`Ready` is an explicit provenance premise for the finite all-start
output arrays. This family does not produce those arrays by the proposed
general fast all-start algorithm. Their construction cost is excluded
from `prepare_work`, `assemble_work`, `build_work` and `query_work`.
Those bounds otherwise come from the actual stored objects and returned
counters, and the cost theorems need no `Ready` premise. Fixed DFA
compilation is a pattern parameter. The primitive model is the existing
fixed-pattern scalar/range/matrix model, not a full bit-complexity or
allocator theorem.

## Generated-code checks

Lean 4.19.0 generated the following hot paths. Their full balanced C
function bodies contain no reverse-DFA construction, text reverse,
length/take/conversion, array materialization, logarithm/power, range
index build, color table build, or request preparation call.

| Function | Generated body lines |
| --- | ---: |
| `FarRight.readMask` | 31 |
| `FarRight.query` | 106 |
| `Cache.queryValid` | 221 |
| `Cache.query` | 58 |

The cached mask read does two finite table accesses and a bounded array
read. The backwards aggregate's own construction and query code was
checked in `one_use_far_aggregate_smoke.lean`; its input text is reversed
and materialized during construction, not passed as a computed phantom
argument to an online query. All finite factories are evaluated during
the two construction stages.

## Reproduction and results

```sh
lake build REWB.BoundaryRangeCacheRegression
lake env lean --run audits/boundary_range_cache_smoke.lean
```

The build completed 292 targets. The independent 54-principal axiom
manifest reports only `propext`, `Classical.choice` and `Quot.sound`, or
no axioms. The new Lean source has no admissions, custom axioms or
alternate executable implementations.

The bounded runtime test supplies rows by an independent, deliberately
slow enumeration of masked cuts in the reversed word, using the actual
prepared target-mask arrays and actual compiled reverse automata.
It compares the complete cache and, separately, the far-right branch
against original-coordinate cut enumeration. This test fixture is not
a production all-start row constructor.

Three DFA patterns, all binary words of lengths zero through two,
widths 1 and 3, and targeted noninjective and same-block copies produced
44 actual caches. All 958 mask comparisons, 577 full queries and 211
independent far-right queries agreed. There were 93 full positive
answers and 7 positive far-right answers; the largest small query
counter was 4,398. The tests include first-copy starts before the query
left boundary, invalid ranges and clipped terminal blocks.

For the length-32, width-8 case, the all-word automata admit an exact
special input constructor: the output row is its downward-closed
prepared mask. `Cache.Regression.copiedMasks_ready` proves this
provenance in Lean for every text. The deep audit copies those actual
arrays into the finite input vector; it does not posit their answers.
All 1,156 complete queries and 561 separate far-right checks passed.
The far-right criterion is exactly `g < r` for this all-word fixture.
There are six stored grid slots; the observed preparation counter was
1,756,703, total build counter 1,762,960, and maximum query counter
140,116. The final audit exited zero after 77.537 seconds.
