# Eager near-boundary tables: generated-code inspection

Reproduce the checked C translation with:

```sh
lake build REWB.BoundaryRangeNearIndexRegression
```

The relevant files are generated under `.lake/build/ir/REWB/` for
`BoundaryRangeTable`, `BoundaryRangeTableColor`, `BoundaryRangeNearIndex`,
and `BoundaryRangeNearIndexScan`.

## Dependent cache

`Table_get___rarg` reads the stored vector with one `lean_array_fget`,
projects the payload, and returns it. The equality transport contributes
no executable branch. The stored key remains a scalar cell; lookup does
not compare or search keys.

`Table_build` first calls `Array_ofFn` with the factory wrapper. That
wrapper has exactly one `lean_apply_1` of the factory, then stores its
payload and work. The second pass obtains each stored cell with
`lean_array_fget` and reads its work field. The second pass has no factory
closure and cannot repeat a factory call.

## Subset selection and the three queries

`TableColor_same___rarg` calls the counted Boolean scan over the stored
state list. `TableColor_search___rarg` reads the stored row by array index
and advances through the stored color keys. `TableColor_choose___rarg`
does not invoke `Colors.encode` or construct a subset enumeration.

`NearIndex_cKey___rarg` performs one shared C range query and the counted
selector. `NearIndex_dKey___rarg` performs one shared D range query and an
array lookup for the initial state. `NearIndex_separated___rarg` performs
two dependent table reads followed by the stored separated query.
`NearIndex_fixedEnd` and `NearIndex_fixedStart___rarg` each read one table
entry and call the corresponding existing query. They reconstruct only
the fixed-pattern initial/final DFA variant needed by that query; no
text index is rebuilt.

The inspected executable bodies for these operations, `scan`,
`atEnd`, `atStart___rarg`, and all three outer scans contain no text-index
builder, word-length traversal, logarithm, or power computation. The
endpoint guards read the index's cached length. The two nested scans use
the stored lower/upper boundary and the supplied right endpoint.

The accompanying Lean work theorems use the established scalar, finite
map, and matrix primitive model. This inspection verifies the indicated
sharing and call structure; it is not an allocator or bit-cost proof.
