# Same-block border: cached executable indices

Reproduce the inspected C translation with:

```sh
lake build REWB.BoundaryRangeNearIndexBorderRegression
```

The relevant generated files are
`.lake/build/ir/REWB/BoundaryRangeNearIndexBorder.c` and
`.lake/build/ir/REWB/BoundaryRangeNearIndexBorderAll.c`.

## Cached generic indices

`Border.Index` stores a natural-number size and height. Its suffix-class
index is indexed by those stored values. Proof fields identify the size
with the input array size and the height with the chosen logarithmic
height. The builder takes the height from the prepared class index's
stored `scales` field.

This matters operationally. In an earlier local version, the class
field's type contained `w.toArray.size` and `MaskedSuffixClass.height
w.toArray.size` directly. The generated `Border_copy___rarg` began with
`lean_array_mk` on the word and then called `MaskedSuffixClass_height` to
supply the executable generic indices to `Regular.dyadic`. The final
version reads both numbers from the index. Its correctness and cost
proofs still reduce to the original builder and dyadic theorems in the
kernel. This is an observed difference in this program's generated
code; it is not a general claim about compiler behavior.

## Query calls

The inspected `GapCell_query___rarg` calls the regular range query on
the stored automaton and range index. `gap___rarg` makes the two shared
C/K range queries, reads two dependent table entries, and calls that
stored gap cell. It does not compile a gap automaton during the query.

`copy___rarg` calls `BoundaryBorder_Regular_dyadic___rarg` using cached
size/height and the stored class and A/B/E range indexes. It also makes
the two regular range calls for the empty capture. `queryAt___rarg`
conjoins that copy result with the common-split gap result. `row___rarg`
and `query___rarg` invoke the counted local endpoint scan. The full near
query calls the existing three-branch query and the border query with
cached grid boundaries.

These inspected bodies contain no `lean_array_mk`, word-length
traversal, logarithm, power, text-index builder, or gap compiler call.
The only enumeration added by this wrapper is over the two endpoints
inside the current short block. Capture lengths use the existing
dyadic AP query, and the common split uses the stored finite automaton.

The accompanying work bounds use the established scalar, finite-map,
and matrix primitive model. This inspection checks sharing and call
structure; it does not establish allocator or bit complexity.

## Runtime audit bounds

The runtime audit evaluates its pattern-dependent budget expressions
once per fixture or grid and reuses them for its comparisons. Some
budget expressions construct a finite formula family; repeatedly
evaluating them inside the endpoint loops would measure additional
test-harness work that is absent from the query. The independent raw
slice predicates and the tested endpoint ranges are unchanged by this
caching.
