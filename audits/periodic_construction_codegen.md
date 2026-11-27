# Periodic construction execution audit

This audit covers the 15 `PeriodicConstruction` modules owned by the
periodic-construction track, from `Windows` through `Regression`.
`PeriodicConstructionPattern` is a separately reviewed fixed-pattern
preparation module and is used by the runtime audit.

## Kernel and execution results

The 15-module build passed with a 213-target dependency closure.
All 95 selected principal theorem reports use only the standard
`propext`, `Classical.choice`, and `Quot.sound` axioms, or no axioms.
The source scan found no proof placeholders, custom axioms, or unsafe
evaluation declarations in this family.

Reproduce the runtime comparisons with:

```sh
lake env lean --run audits/periodic_construction_smoke.lean
```

The successful run reported:

- 682 materialized finite-orbit inputs and 16,368 independent exponent checks.
- 96 formula-to-window comparisons, including zero modulus, empty formulas,
  negative coefficients, and a physical coefficient of 1,048,576.
- 36 P1/P2 formula-assembly cases and four actual empty P2 searches.
- 120 actual shared-index periodic queries, of which 33 accepted; all old
  values/counters and the tested literal witnesses agreed.
- 9 dense banks rebuilt across persistent source erases, with 28,800 full
  cell comparisons and 1,800 independent literal stage-transition checks.
- Every evaluated construction bound passed. The run took 3,982 ms.

The kernel regressions separately cover disabled source windows, equal
window endpoints, source erase with target retention, a zero-period guard,
and coefficient-independent traversal counts.

## Generated-code checks

The generated C in the build output was inspected for `ClusterQuery`,
`ClusterCell`, `ClusterMatrix`, `ClusterBank`, and `MaskedPhase`.

`Cluster.materialize` constructs the result table once. The Boolean
matrix and both counter passes read that stored result table. The output
and counter closures contain array reads and projections; they do not
invoke the cell compiler again.

The replay-key closure in `Cluster.tabulate` performs one map composition,
one block compiler invocation, and one flatten operation. Its later
table/counter passes read the stored triple. `compileDenseBank` calls
`prepareRows`, `replay`, and the measured dense-bank compiler once each.

`Cluster.sourcePairQuery` tests the enabled flag before constructing its
formula or windows. The disabled branch returns its constant result.
The enabled branch calls `sourceWindows` once and the persistent AP
window query once. The concrete cell has one of two active paths:
waiting-to-C materializes the always/exit acceptance vectors; C-to-E
materializes the entry/exit acceptance vectors. Invalid stage pairs
return immediately.

`Masked.phaseQuery` reads the contexts once, constructs the zero tuple
once, obtains each positive-cut tuple list once, and invokes the zero,
interior, and ending compilers once each. The outer guarded query calls
this phase routine once. No construction bound, syntax budget, or
inflation coefficient is evaluated by these query bodies.

## Exact substitution interfaces

`Cluster.compileDenseBank_value` preserves the entire old table/counter
pair. `compileDenseBank_extra` and `compileDenseBank_inflate` charge the
additional materialized acceptance maps, finite-orbit searches, DNF
construction, residue-window construction, and matrix/table passes by
an explicit coefficient depending only on C/E state counts and cached K.
The physical period and source-window endpoints do not enter that
coefficient.

`Masked.query_value` preserves the entire old indexed answer.
`query_extra` and `query_inflate` include the descriptor, formula,
projection, and interval construction for all three periodic branches.
They also preserve the old products/visits/mask ledger, allowing a later
primitive-substitution trace to combine the counters without executing
the old query a second time.

## Accounting scope

These are structural-operation ledgers with scalar arithmetic and DFA
primitives counted in the same model as the existing projection and AP
modules. They are not a count of native CPU instructions, garbage
collection, or arbitrary-precision arithmetic bit operations.

The masked phase wrapper still inherits abstract shared cut-index
products and the fixed-universe tuple-extraction primitives. Their
finite monoid/table expansion needs its own measured coefficient.
Pattern preparation and action-map construction have separate concrete
modules. The global all-start install/repair/erase/report substitution
trace is a separate obligation. The earlier P1/P2 formula constructors
are measured here; this audit does not claim that all old periodic
event-generation and join-allocation counters have already been replaced.
