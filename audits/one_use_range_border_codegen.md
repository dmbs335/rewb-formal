# One-use midpoint query: generated-code inspection

Reproduce the inspected translation with:

```sh
lake build REWB.OneUseRangeBorderRegression
lake env lean --run audits/one_use_range_border_smoke.lean
```

## Shared finite-state transition trees

`OneUseRangeBorderVariants` changes only initial/final acceptance data.
The generated `changeRanges___rarg` returns the existing range-index
record when it is exclusive, and otherwise creates a four-field record
that shares the same tree reference. `startRanges___rarg` and
`stopRanges___rarg` call that adapter. No transition-map tree is copied
or rebuilt. In Lean, each corresponding
adapter applied to `Range.build C w` equals the appropriate variant's
builder by `rfl`.

## Actual near query

`state___rarg` reads the cached size and height from the index, creates
the fixed-pattern initial/final variants, computes the midpoint, and
calls the offset-prefix dyadic query using the shared C tree twice.
The A context of that regular query starts at the midpoint. Its E
context ends there. Both use the same C state.

`Regular_maps___rarg` makes exactly the six materialized range queries
specified in Lean. The first starts at the supplied base. The other
five obtain the periodic steps and tails. `Regular_dyadic___rarg` calls
the existing suffix-class dyadic query and the counted row traversal.
The dense case reuses the existing materialized finite-orbit solver.

`inner___rarg` traverses the stored finite C-state list and makes the
single regular query for the empty capture. `queryAt___rarg` checks all
four endpoint guards, then combines that result with the two actual
outer A/E range queries. `row___rarg` and `query___rarg` call the existing
counted scan over the two short endpoint blocks.

The inspected query bodies contain no `lean_array_mk`, word-length
traversal, logarithm, power, class-index preparation, or range-index
builder. There is no loop over capture lengths or all source ends.
The repeated capture lengths are represented by the existing AP/point
choices derived from the actual text index.

## Scope of the work theorem

The builder is actual text preprocessing. The near query has no answer,
matching relation, periodic certificate, or supplied program input.
Its exact result preserves the requested first-source lower bound.
The complete range-query partition still contains two explicit far
predicates. Those require the separate actual all-start caches; this
family does not assert that they have already been constructed.

The counters retain the established scalar, materialized-map, and
matrix primitive model. This source/C inspection checks the stated
sharing and calls, not allocator or bit complexity. The runtime audit
caches fixed-pattern budget coefficients once so evaluating the test's
upper bounds does not dominate the measured query executions.
