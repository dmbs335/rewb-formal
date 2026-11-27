# Separated endpoint construction: runtime representation audit

The kernel theorems count the repository's scalar, finite-map, and matrix
primitives. They do not prove a Lean allocator or reference-count cost
model. This additional audit checks that the implementation does not
retain an avoidable alias to the text-sized endpoint vector during its
top-down traversal.

## Thread the endpoint vector through unpacked results

The initial implementation kept the left result pair while executing the
right child, because its cost field was read afterward:

```lean
let left := go ... l ... bits
let right := go ... r ... left.1
(right.1, bottom.work + left.2 + right.2 + 6)
```

Lean 4.19.0 emitted C with this lifetime order:

```c
left = go(...);
leftBits = lean_ctor_get(left, 0);
lean_inc(leftBits);
right = go(..., leftBits);
/* only afterward: read left.cost and lean_dec(left) */
```

The retained `left` pair keeps another reference to `leftBits` at the
start of the right traversal. An array update can therefore copy the
whole vector. This is a representation issue in the implementation, not
a claim about a compiler defect.

`Separated.Pass.go` now unpacks both recursive results explicitly:

```lean
let (leftBits, leftWork) := go ... l ... bits
let (rightBits, rightWork) := go ... r ... leftBits
(rightBits, bottom.work + leftWork + rightWork + 6)
```

All existing correctness and counter proofs remained definitionally
valid. The emitted C now extracts `leftBits` and `leftWork`, releases the
left pair, and then calls the right child:

```c
left = go(...);
leftBits = lean_ctor_get(left, 0);
lean_inc(leftBits);
leftWork = lean_ctor_get(left, 1);
lean_inc(leftWork);
lean_dec(left);
right = go(..., leftBits);
```

`Pass.mark` emits an array read followed by `lean_array_fset` without
retaining the input vector. The complete builder starts from a fresh
false vector. Earlier externally retained vectors remain semantically
immutable; the low-copy observation concerns this single-owner build
path.

## Online query and hot recursion

`Separated.Suffix.Index` stores its length and height. The generated
`Suffix.query` reads the stored height and tree, then calls the existing
`TokenIndex.query`; it neither receives the original word nor computes
its length. The outer `Separated.query` only projects this suffix index.

The generated `Summary.build` and `Pass.go` functions contain no word
slice, leaf-list, tree-shape, or text-length traversal. `Summary.build`
uses cached range-index lengths for its edge queries. `Pass.go` uses the
saved representative start and depth directly. The existing empty-trie
representative fallback is unreachable in the good, nonempty child
calls established by the construction theorems.

The one `List.length` use in `SeparatedSuffix.c` belongs to construction
of the boundary cells. The finite rows, transition tables and accepted
cut matrices retain their inherited fixed-pattern primitive convention.

## Reproduce

```sh
lake build REWB.BoundaryApplicationSeparatedRegression
lake env lean --run audits/boundary_separated_smoke.lean
rg -n 'List_length|shape|slice|leaves' .lake/build/ir/REWB/BoundaryApplicationSeparatedPass.c .lake/build/ir/REWB/BoundaryApplicationSeparatedSummary.c .lake/build/ir/REWB/BoundaryApplicationSeparatedQuery.c
```

Inspect the node branch of
`.lake/build/ir/REWB/BoundaryApplicationSeparatedPass.c` for release of
the left result before the right call, and the body of `Suffix.query` in
`.lake/build/ir/REWB/BoundaryApplicationSeparatedSuffix.c` for its cached
height argument. The smoke test independently enumerates source ends,
repeat lengths, target ends and E suffixes; it also checks all static E
cells, padding, and the actual construction/query counters.
