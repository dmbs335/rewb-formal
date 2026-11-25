# Runtime probes and practical limits

These observations were made on 2026-11-25 using Lean 4.19's interpreter. They are separate from the kernel's verification of termination, semantic correctness and abstract operation counts. They are not a benchmark claim or a complete implementation-level complexity proof.

## Reproduce the small probes

Build the current code first:

```sh
lake build
lake env lean --run audits/lean_runtime_smoke.lean p2
lake env lean --run audits/lean_runtime_smoke.lean modulus
timeout 55s lake env lean --run audits/lean_runtime_smoke.lean p1
```

The P1 timeout is intentional in this diagnostic command; it is not an assertion that the computation must finish in that time.

| Probe | Observed result |
| --- | --- |
| Full finite-word P2 branch, three zero symbols, Q=1, seven all-accepting single-state DFAs | `(true, 65627, 7)`: accepted, measured projection operations, run comparisons |
| Actual-modulus scan over 30,000 empty conjunctions | `60001` measured traversal operations; completed |
| Moduli 6, 6 and 4 in one conjunction | Exact shared modulus `12`; completed |
| One P1 target formula for n=3, q=1 and the same one-state DFAs | 20,176 projected branches; 15,182,855 measured projection operations; evaluation at m=0 accepted |
| Full measured long-source P1 pipeline on the same length-three input | Did not finish within the final 55-second interpreted probe; timeout exit 124 |
| Full short-source P1 pipeline on the singleton-DFA `babaaaa` regression | Interrupted during a multi-minute interpreted run; no successful executable result is claimed |

The isolated-source regression nevertheless has a kernel-checked concrete witness and derives acceptance through `P1ShortBranch.solve_complete`. That is evidence of semantic correctness, not a completed execution of the large generated formula.

## Defects repaired during these probes

1. Multiplying duplicate coefficient factors and guard moduli made a period-1 P1 target produce a candidate period of 262,144. Using LCM reduced that stage to period 2 while preserving the elimination proof.
2. Deep recursive list operations caused interpreter stack failures. Kernel-checked compiler simplification equalities supply tail-recursive implementations and preserve both results and counters. The executable entry points must be compiled after those replacement equalities; direct helper tests alone do not establish that callers use them.
3. The original long-source join evaluated a huge finite-family modulus intended as a proof bound. `ActualModulus.build` now computes the shared LCM from the actual emitted formulas. Its compatibility, positive value, fixed-pattern upper bound and traversal count are proved.
4. P2's decision path formerly materialized all projected branches. The measured depth-first search now stops on a successful branch and is proved equivalent to the full decision, with a pattern-dependent worst-case bound.
5. A later audit found deep recursion in the outer P2 phase/run traversals. Kernel-proved `foldr` compiler replacements now preserve the complete `Work` record and its eager counters. A 100,000-row test passes for each loop. Those deliberately inexpensive zero-period rows test traversal depth; they are not valid-run semantic examples.
6. Shared text-context preparation also had text-depth recursion. `IntervalDFA.countedPrefix_eq_countedPrefixTR` and `BoundaryContexts.suffix_eq_suffixTR` now preserve the full lists/rows and counters with stack-safe folds. The actual 100,000-symbol build produced 100,001 prefix boundaries and suffix rows; every prefix state and all 300,003 suffix-state cells matched independent arithmetic references, with exactly 400,004 measured entries.

## Remaining limits

P1 must produce unary formulas for the offline join, so its current generic projection still materializes a large DNF. Formal fixed-pattern constants can be very large, and negative P2 cases can also be expensive. Successful kernel checks should not be described as a practical speedup on ordinary inputs.

The counters distinguish preparation, symbol comparisons, equality-array reads, formula operations, modulus traversal, sorting, interval tests and event/text visits. Allocation, runtime stack representation, garbage collection, bit-level arithmetic and a single complete word-RAM cost semantics are not verified by these probes. Large-input runtime readiness is not asserted.

## Index and reporting continuation probes

After `bash scripts/check.sh`, run `bash scripts/index-audit.sh` for the new compiled paths. The independent small-word comparisons check runtime behavior in addition to the universal kernel theorems; their finite ranges are not asymptotic evidence.

| Probe | Observed result |
| --- | --- |
| Masked reporter, one immutable target shared by three sources | Sources `[0,1,2]`, 9 existence-query calls, 20 scan-query work, 7 copied cells, 36 total tracked work |
| Empty reporting mask | One failed existence query; total tracked work 2 |
| Four-leaf ordered small-to-large event sample | 4 transfers, 5 created and 2 retired edges, 10 threshold records |
| Unary event-reset regression at N=100 | 4,950 recreated records versus 99 retained adjacencies |
| Persistent endpoint tree on 30,000 cells | Build 1,351,320; root recolor 28; fresh insertion 1,592; prefix query 460; earlier version retains its old colors |
| Cut-window index on n=512 | Build 10,240 matrix products; sampled query 6 products and 24 node visits; exact endpoint and fixed-end checks passed |
| Balanced 512-leaf persistent merge | 2,304 light transfers; 3,644,333 tracked steps; coalesced active states and original static transitions preserved |
| Mixed 512-leaf source/target schedule | Total mass 512, 256 target records, 1,024 transfers, 1,688,236 tracked steps; silent sources remain inactive and static transitions are preserved |
| Finite-action lazy tree | Explicit three-state map universe has 27 entries; build 18, two reindexes 7 each, replacement 20, prefix query 5; noncommuting/noninjective tag order and fresh-cell behavior pass |
| Ordered finite-action interval products | 768 matrix-entry checks after noninjective root action and fresh replacement; exact order, empty ranges and clipping passed |
| Immutable-mask stepped arrays and AP queries | 17 masks, 6,426 actual reused builds, 3,373,650 queries, 53,560 hits, zero mismatches; query maxima two array reads and 37 scalar operations |
| Shared-cut interval/rotation index | 127 binary words, 18,943 interval queries, 75,772 map-pair checks and 642 rotations; all matched direct common-cut enumeration |
| Constrained DFA tuples | Four joint transformations from a noncommuting two-state map example; 672 B-prefix/C-full-suffix/E-short-suffix checks passed |
| Doubled-period shared preparation, q=4,096 | 4,096 result tables; 114,688 preparation products, 8,192 query products and 131,074 visits; no quadratic phase/cut list was materialized |
| Descriptor-only compressed trie | 8,193 nested prefix records representing 33,558,528 characters produced 16,385 nodes with work 27,943,104; the CI probe uses 2,049 records and retains empty/duplicate/prefix regressions |
| Actual suffix-class dense-pair discovery | n=512, 513 suffixes, preparation work 1,798,605; a 253-occurrence complete locus produced `(0,512,2)` with work 190; equal-depth refinement gate cost 2 and skipped discovery |
| Constructed fixed-end application | All 204 saved local versions checked at g=0, middle, g=n and empty text; every position/color/state and exact E right boundary agreed. n=512 build: 514 records, 257 targets, 1,027 nodes, 427 light transfers, work 1,817,325 |
| Real periodic phase compiler | 11 exact actual-index cases, 5 hits, zero mismatches. Combined B/C/E state counts (2,1,2) required about 6.7 seconds preparation plus 17.2 seconds for one q=1 query; positive-cut cases used separate two-state B or E |
| Real periodic-text/full-suffix bridge | 48 actual-index queries versus direct capture/gap/suffix slices, 22 hits, zero mismatches, two full-vs-in-run suffix differences. Arbitrary source phases/masks, clipping, empty windows and too-short/after-end sources included |
| Boundary accepted-cut/subset import | All 35 actual node R tables versus explicit closed-cut enumeration; heterogeneous subset queries passed, 4 subset colors, import work 60,060 |
| Fast sparse occurrence sets | 4,096 positions in capacity 1,048,576: 24,576 imports, 41,570 fresh and 37,475 retired edges, work 15,786,735. A height-40 singleton completed with work 413 |
| LCE/LCS exhaustive binary test | 127 words of lengths 0–6, 4,861 endpoint pairs; results match direct list-prefix/suffix reference |
| LCE/LCS on n=4,096 | 14 rows in each direction; 18,133,870 preparation work; sampled extension 4,034 with 7 pair comparisons and 13 visited levels |
| Grid candidates versus direct extension | 189 word/stride cases, 278 positive-copy coverage checks; all passed |
| Grid n=1,024, stride=32 | 33,825 probes, 8,449 raw strips; preparation 3,287,378; query work 4,173,783 |
| Sampled all-period runs and exact dedup | 127 binary words, 769 schedules; soundness, required coverage, dedup membership/uniqueness and counter bounds passed; stride 1 agrees exactly with the independent full-run reference |
| Minimum-period recovery | Alternating word of length 12 with displacement 4 returns minimum period 2; selector work 139 |
| Sampled unary runs, n=256, stride=8 | 8,481 probes, 3,120 raw records, exactly one deduplicated run `(0,256,1)`; query 629,056; period tests 1,564,428; preparation 533,022; divisor insertion 4,398; dedup 589,680 |

These probes cover the named index components. They execute the local constructed boundary application and periodic phase compiler, but not the missing complete heavy-path boundary query or masked-cluster event application, and they do not remove the P1 projection limits above.

The index counters are also partial accounting. For example, `RankIndex.keyCells` counts produced key bits but does not separately charge every append traversal; divisor construction counters do not enumerate all scalar guards; and APIs accepting `f : Nat → Fin σ` do not charge arbitrary computation hidden in f. A complete interpretation must use materialized text and compose all schedule, list/array and arithmetic costs. The finite-word LCE adapter supplies that input representation for its own entrypoints. The targeted loop repairs are not a blanket stack-safety claim for all existing helpers.

### Periodic compiler audit scope

The default `audits/masked_periodic_smoke.lean` deliberately bounds interpreted work while checking zero/positive remainders, interior/ending families, eta=0, both rotations and irregular/empty masks. Larger combined two-state B and E positive-cut sweeps are retained behind `--extended`. Broad and ten-case combined probes were manually interrupted after several minutes; they did not report a mismatch, and no completed result is claimed. The default's passing cases do not establish practical scalability. The universal kernel correctness theorem is independent of those finite runtime limits.
