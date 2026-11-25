# Heavy-path runtime regression

This records a local generated-code observation with the pinned Lean 4.19.0
toolchain. It does not identify a compiler pass or claim a general upstream
cause. No upstream report was sent.

## Observed behavior

The first implementation of `Heavy.go` used whole-pattern aliases such as
`t@(.node _ depth l r)`. The kernel accepted the definition and its correctness,
static-transition, import-count and cost theorems. Running the actual empty-word
construction with two-state DFAs exited with status 139.

The failure was isolated to the parent `Heavy.go` call. The empty word produces
one binary root and two terminal leaves. Separately evaluating its normal D
version, R rows, light import, A preimage map, lazy recolor, full `advance`, and
each child `go` completed. Calling `go` on the binary root failed.

The original alias-based definition is retained as the **non-executed**
`Heavy.Regression.aliased` in `REWB/BoundaryApplicationHeavyRegression.lean`.
`aliased_eq_go` proves equality to the production definition for every input,
including the saved versions and all counters. The reference is deliberately
noncomputable so the observed generated code is not part of the executable
entry point.

## Relevant generated C before refactoring

The following excerpts are from the generated
`BoundaryApplicationHeavy.c` before removal of the aliases, after the separate
cached-height refactor. Unrelated reference-counting lines are omitted.

```c
x_96 = l_REWB_BoundaryApplication_Versions_root___rarg(x_12);
x_104 = lean_ctor_get(x_96, 0);  /* normal.state */

x_122 = l_REWB_BoundaryApplication_Heavy_advance___rarg(
  x_2, x_5, x_6, x_8, x_9, x_90, x_121, x_108);
x_123 = lean_ctor_get(x_122, 1); /* advance work */
lean_dec(x_122);

/* In the branch descending into the heavy right child: */
x_153 = lean_ctor_get(x_104, 0); /* normal.state.tree */
x_154 = l_REWB_BoundaryApplication_Heavy_go(
  x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9,
  x_10, x_92, x_116, x_153);
```

The source expression for that last argument is `next.1`, the **subset State**
returned by `advance`. The displayed generated expression instead obtains
the tree field of the normal D State. This discrepancy is an observation of
this generated function, not a diagnosis of why it happened.

## Production form and verification

The production function now uses ordinary constructor patterns and explicitly
reconstructs the node passed to `RTable.node`. All existing proofs recompiled.
The corresponding generated code retains `advance`'s first projection and
passes it to the selected heavy-child recursive call:

```c
x_140 = l_REWB_BoundaryApplication_Heavy_advance___rarg(...);
x_141 = lean_ctor_get(x_140, 1);
/* heavy child branch */
x_191 = lean_ctor_get(x_140, 0);
x_142 = x_191;
/* recursive go receives x_142 */
```

The permanent minimal executable regression is:

```sh
lake build REWB.BoundaryApplicationHeavyRegression
lake env lean --run audits/boundary_heavy_empty.lean
```

Observed output:

```text
emptyHeavyNodes=3 emptyImports=1 emptyQuery=true emptyVisits=2
```

The larger `audits/boundary_heavy_smoke.lean` independently compares complete
fixed-end answers against explicit target/length enumeration, verifies source
addresses and strictly decreasing head-jump ranks, and checks the measured
construction/query bounds. Length enumeration appears only in the audit.

## Runtime length caching

A separate generated-code inspection found avoidable `List.length w` calls
inside the initial heavy construction and query definitions. `Heavy.go` and
`advance` now receive a generic cached tree height. The public query passes
`Index.cachedLength` to `probeAt` and uses proof-erased casts for the source
and store. Generated production query code projects the cached length from
the index; it does not scan the word. Remaining length calls over the finite
color enumeration are pattern-dependent work.
