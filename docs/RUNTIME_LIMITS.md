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
| Complete cubic-run enumerator | All 1,023 binary words through length 9 and 1,093 ternary words through length 6 match an independent full-run reference. n=2,048/period=2: 4,097 nodes, 4,094 events, work 13,417,677; stale equal-depth gap rejected |
| Cached heavy-path fixed-end query | 901 complete-answer comparisons, 24 accepts, zero mismatches; at most 3 jumps observed. n=512: 1,027 nodes, 513 imports, work 1,741,630. Empty input: 3 nodes, 1 import, true query, 2 visits |
| Actual dense/singleton cluster matrices | 30 matrices / 750 cells, 62 true cells, zero mismatches against literal physical skips. Noninjective two-state automata, phase offsets, unequal masks and nonperiodic singletons included; maximum 8 range products, 42 visits, 434 AP+matrix work |
| Complete periodic all-source batches | 149 materialized-text batches, 46 accepted sources, zero mismatches; includes 127 binary texts through length 6, empty/truncated masks, source filtering, multiple runs, phase shifts and full-input suffixes. Local run took about 24.5 seconds |
| LCE/LCS exhaustive binary test | 127 words of lengths 0–6, 4,861 endpoint pairs; results match direct list-prefix/suffix reference |
| LCE/LCS on n=4,096 | 14 rows in each direction; 18,133,870 preparation work; sampled extension 4,034 with 7 pair comparisons and 13 visited levels |
| Grid candidates versus direct extension | 189 word/stride cases, 278 positive-copy coverage checks; all passed |
| Grid n=1,024, stride=32 | 33,825 probes, 8,449 raw strips; preparation 3,287,378; query work 4,173,783 |
| Sampled all-period runs and exact dedup | 127 binary words, 769 schedules; soundness, required coverage, dedup membership/uniqueness and counter bounds passed; stride 1 agrees exactly with the independent full-run reference |
| Minimum-period recovery | Alternating word of length 12 with displacement 4 returns minimum period 2; selector work 139 |
| Sampled unary runs, n=256, stride=8 | 8,481 probes, 3,120 raw records, exactly one deduplicated run `(0,256,1)`; query 629,056; period tests 1,564,428; preparation 533,022; divisor insertion 4,398; dedup 589,680 |

These probes cover the named index components. They execute constructed heavy-path fixed-end queries, complete cubic-run enumeration, periodic all-source batches and local cluster matrices. The full boundary-aware assembly and masked-cluster event/update application remain separate, and these checks do not remove the P1 projection limits above.

The index counters are also partial accounting. For example, `RankIndex.keyCells` counts produced key bits but does not separately charge every append traversal; divisor construction counters do not enumerate all scalar guards; and APIs accepting `f : Nat → Fin σ` do not charge arbitrary computation hidden in f. A complete interpretation must use materialized text and compose all schedule, list/array and arithmetic costs. The finite-word LCE adapter supplies that input representation for its own entrypoints. The targeted loop repairs are not a blanket stack-safety claim for all existing helpers.

### Periodic compiler audit scope

The default `audits/masked_periodic_smoke.lean` deliberately bounds interpreted work while checking zero/positive remainders, interior/ending families, eta=0, both rotations and irregular/empty masks. Larger combined two-state B and E positive-cut sweeps are retained behind `--extended`. Broad and ten-case combined probes were manually interrupted after several minutes; they did not report a mismatch, and no completed result is claimed. The default's passing cases do not establish practical scalability. The universal kernel correctness theorem is independent of those finite runtime limits.

### Heavy-path generated-code regression

The initial dependent whole-pattern-alias implementation passed kernel proofs but crashed on the empty-input execution audit. The production definition uses ordinary constructor patterns and explicit node reconstruction; a kernel theorem proves equality to a non-executed reference. The fixed version passes the permanent empty case and all 901 full-answer comparisons. [The diagnostic record](../audits/boundary_heavy_codegen.md) preserves the generated-code observation and explicitly leaves the compiler-pass cause unproven. Cached height/length arguments also remove input-length scans from the recursive heavy path and actual query.

### Mutable-source and empty-capture continuation

The following probes exercise actual source deletion, rebuilding and initialization. Their bounds retain the declared unit array/Nat operation model; they do not account for all reference counting, allocation, garbage collection or bit complexity.

| Probe | Observed result |
| --- | --- |
| Mutable progression index | 1,261 builds, 6,305 erases, 71,470 membership checks, 528,570 grid checks and 847,392 AP checks; exact physical witnesses and old versions preserved |
| Sparse progression with n=4,096 and step 1, 3 or 1,000,000,007 | Height 26 and capacity 67,108,864 in every case; no residue enumeration or allocation proportional to the step |
| Reverse source/run addresses | 256 texts and 2,402 rows; exact IDs and one-shot delivery. Unary n=2,048 delivers 2,049 memberships despite 4,098 requests |
| Actual mutable run batch | 765 preparations, 14,583 requests and 395,712 exact run-query witnesses; 2,388 delivered memberships |
| Actual cluster-leader execution | 4,682 streams and 18,069 state checks; n=4,096 consumes all 16,338 generated records exactly once |
| Actual cluster descriptor queries | 770 streams, 10,779 states and 456,081 queries; height-20 deep split preserves the previous dense version and returns all 1,024 singleton descriptors |
| Rebuilt mutable dense/singleton banks | 23 rebuilt banks; 10,400 physical and 12,800 shortening/action cells; 28 shared-cut queries; no mismatch |
| Actual run-ID-to-bank adapter | Six actual erase requests, 14 rebuilt banks, 5,600 physical cells and 14 invalid-ID/modulus rejections; no mismatch |
| Empty-capture backwards scan | 65,984 scans and 446,272 brute boundary comparisons; n=100,000 produces all 100,001 bits with work 10,000,100 |
| Empty reports into actual source batch | 837 builds and 5,157 checked positions; unary n=512 reports and deletes all 513 source boundaries with total work 2,730,498 |
| Separated-boundary primitive | 257 small builds, 1,007 endpoint-bit and 1,007 E-query comparisons; n=512 build work 1,043,820 and query work 37 |
| Periodic border component selector | 53,112 calls and 405,880 physical membership comparisons; 44,092 AP bands, 4,880 exceptional points and 4,140 empty exceptions; no mismatch |
| Border selector at n=4,096 | q=1,2,1,024,2,048 gives work 342,328,202,188; the selector never enumerates q residues or candidate lengths |

The mutable-bank probes deliberately rebuild after deletion. Persistence means the old bank still holds its old summary; these passing probes do not demonstrate automatic dirty-bank ownership or global cluster repair. The actual run batch updates only source indexes, and its immutable targets remain separate.

The separated-index audit exposed avoidable copy-on-write pressure from retaining the left recursive result pair while building the right result. Explicit pair destruction removes that alias in the generated path; [the code-generation record](../audits/boundary_separated_codegen.md) records the observation. Full runtime allocation analysis remains separate.

### Shared-cut finite-universe limit

`audits/masked_cluster_cut_smoke.lean` passes its default small-universe full-index queries and its 256-cell stored-relation correlation check. The actual full-index mixed-cut rejection is also kernel-proved. The optional `--full-correlation` probe uses the larger joint universe J=16 and exceeded a 30-second external timeout, exiting 124. That optional execution is not a passing gate and is not presented as one. The result illustrates the fixed-pattern table-materialization cost; it does not invalidate the universal kernel theorem or establish practical scalability.

### Actual suffix/store/border/edge and cached-boundary continuation

| Probe | Observed result |
| --- | --- |
| Actual suffix class | 511 binary texts, 41,983 queries, including 5,934 interior-edge cutoffs; unary n=1,024 uses 2,049 owner nodes and maximum query work 79 |
| Fixed-partition mutable bank store | 115,200 replay cells, 7,200 physical checks, 83,200 untouched-slot checks; seven owned repairs and four no-owner requests; no mismatch |
| Complete short-window and dyadic equality | 255 texts, 13,053 queries, 47,305 rows and 513,916 physical checks; additional 13,274 arbitrary-window probes and deep n=1,024 cases |
| Actual regular border query | 45,360 AP alignment checks, 1,536 finite-orbit cases, and 46,324 actual queries over 63 texts; 3,835 positive and 42,489 negative answers; no mismatch |
| Large regular exponents | Exponent 100,000,000 uses unchanged finite-orbit traversal work; n=512/period1 and n=513/period3 each pass 48 full-slice queries |
| Compressed-edge scheduler | 14,592 schedules, 66,816 literal-length checks and 35,389 actual pops; a billion-long singleton edge has one band, zero pops and work 42 |
| Boundary automata and actual reversed mask | 87,023 mask builds, 713,711 physical comparisons, 2,555 DFA reversal checks and 504 shared-gap checks; no mismatch |
| Cached three-near-case index | 71 eager builds, 319 complete region triples (957 raw-cut comparisons), 175 key-bit checks; deep n=128 passes 645 triples with maximum work 9,775 |
| Cached far-left index | Default: 85 eager builds and 425 direct comparisons, maximum query work 76; n=128 passes 8,385 endpoint queries, build work 294,105 and query work 120 |

All default probes above completed. The near-case default includes every binary text through length two, seeded mixed two-state examples, explicit branch fixtures and the deep path. Its larger diagnostic completed 222 eager builds and 1,554 queries before a later mixed phase was manually interrupted; the whole diagnostic is not a passing test. The separate broad far-left probe completed 645 builds and 8,025 comparisons plus its deep case in about five minutes; the default keeps the smaller complete mixed-state sweep because the underlying separated primitive is already tested independently at n=512.

These are checks of the stated abstract operation counters and returned answers. Fixed-pattern automata, finite maps and projection formulas may have large constants. They do not imply a practical speed claim or an allocator/bit-cost theorem. The scheduler's bank/query callback work and the store's changing-partition repair policy remain outside their respective bounds.

The exact `14ff501` push CI passed. Its PR workflow passed the build/dependency stage but was cancelled at the previous 20-minute job limit during the separated n=512 runtime probe, with no recorded semantic mismatch. The Lean job limit is increased to 40 minutes; the Python job retains its existing limit. This configuration change does not count the cancelled run as successful.

### Complete traversal, catalog and residual-window continuation

| Probe | Observed result |
| --- | --- |
| Actual full suffix traversal | 511 texts, 10,080 complete band/length classes and 14,846 unique source/length covers; 3,133 equal-depth skips and 4,542 light imports; zero mismatches |
| Deep geometric traversal | n=512: unary work 1,264,594; period-three work 2,012,733; actual pop/discard/pending conservation checked |
| Shared run catalog | 255 texts, 168 actual runs, 16,254 ID lookups, 1,132 target-count checks and 13,608 AP queries; exact IDs and immutable counts |
| Dense catalog discovery | n=1,024 period-one lookup/discovery work 270/491; n=513 period-three with K=1,000,000,007 uses 249/444; no K-sized allocation |
| Fourth near case and all-near assembly | 23 eager builds, 335 copy checks, 261 common-gap checks, 571 region queries and 97 all-four queries; n=128 build work 390,491 and 16 full queries, maximum 49,173 |
| Separated residual P1/P2 reductions | 2,085 valid windows, 4,170 independent language checks and 204 actual run-window checks; zero mismatches; source-before-window P1 and source-inside-window P2 included |
| Actual strip schedule | 127 binary texts and 3,429 configurations; 2,724 distinct long strips, 2,178 emitted jobs and 2,428 covered copies; independent character and global-grid comparisons agree |
| Deep strip schedule | n=1,024 emits 3,841 jobs from 992 strips with 4,599 local cut probes; n=513 emits 75 jobs from 160 strips with 85 probes |
| Automatic bank preparation | Four real fixtures, 83 preparations, 16,600 literal physical cells, 297,600 replay cells, 29 source erases and four retired-slot clears; zero mismatches |

The near-border generated-code inspection found that dependent query arguments were recomputing a text array and height. The index now caches both, and the corrected query path has no such hidden preparation. The catalog lookup likewise caches key width and avoids text/run scans. The strip schedule's proof-only cell-packing list is absent from executable construction; local cut ranges and cached counts are used.

The residual language tests use bounded independent cut enumeration as references. They validate the exact reductions, not an unimplemented fast range query. Automatic bank preparation uses actual current source histories, discovered catalog IDs and predecessor metadata, while retaining an explicit neighbor-anchor invariant. The geometric driver and band-count proofs still exclude complete bank repair, aggregate query and reporting work.

Both exact `88959f2` GitHub CI runs passed. That result validates the preceding published checkpoint; later additions require their own exact-head remote runs.


### Repairs, physical-window aggregates and short-outer construction

| Probe | Observed result |
| --- | --- |
| One-use near border | 47 eager builds, 23,408 point checks and 7,542 region comparisons; 696 positive answers; n=256 and mixed n=129 deep fixtures passed |
| Actual residual dispatcher | 508 schedules, 3,802 selectors and 930 independent complete P1/P2 union comparisons; zero mismatches; deep n=512/period1 and n=384/period3 schedules passed |
| Backward far bit aggregate | 68,580 builds and 661,104 comparisons over 127 texts; deep n=200,000 passes 200,003 queries; build work 3,600,013 and query work at most four |
| Dirty requests and two-pass reset | 18,432 insertion patches, 11,520 crossings, 35,093 live records; 73,937 deduplicated keys, 165,679 unchanged descriptors and 33,361 captured changes; two actual bank-reset fixtures add 1,200 physical cells |
| Retained-anchor successor refresh | 20,480 cases, 7,968 successor keys, 28,128 unchanged incoming contexts; 800 physical cells and 25,600 untouched replay cells, including simultaneous resets and an empty refresh |
| Assembled one-use cache | 181 builds, 3,457 raw-cut comparisons and 346 positive answers, including 40 near-only; deep n=128/width8 passes 780 queries with build work 505,406 and max query work 152,403 |
| Exact short-outer table | 127 texts, 6,900 real builds and 390,078 queries; deep n=4,096/L=32 uses 261,216 touches and work 52,704,855 |
| Actual aggregate/window query | 483 independent comparisons, 152 positive answers and zero mismatches; 201 queries clip actual physical source windows, including dense interiors, erased sources and overshoot |
| Actual driver repair chronology | 255 texts, 1,930 complete bands, 1,860 imports and 2,392 pops; 3,480 reset keys, 9,686 safe unmarked clusters and 10,386 retained-copy checks; zero mismatches; unary/period-three n=128 cases also pass |

The one-use cache audit supplies its finite all-start input rows by bounded reference computation. This checks the actual assembled cache, not the missing fast row constructor. The residual audit likewise uses independent bounded endpoint scans for the still-pending query predicates. The short-outer table itself is the actual proved producer, using exact keys and chronological finite-state rows.

The aggregate audit uses automatically discovered/prepared banks, actual mutable source erases and persistent replacements. It compares different-cluster ordered-copy witnesses; pairs within one dense cluster belong to the separate periodic branch. The full shared-cut index executes for the smaller finite map universes. The J=16 negative correlation fixture scans actual-word stored tuples. An optional attempt to build the full J=16 index was manually interrupted; it is excluded from successful runtime evidence. This is a fixed-pattern constant limitation, not evidence for a completed fast matcher.

Generated query code was inspected. The one-use cache's hidden word reversal was removed from its selector wrappers. Aggregate wrappers now call two-boundary clipping and one common cut with no text/length-band enumeration. Pattern-size table construction, allocation/reference-counting and bit arithmetic remain outside this inspection. Full traversal coherence and the complete machine-cost theorem are still open.


The repair chronology audit follows the actual geometric driver's order,
keeps one global anchor array, carries only the retained heavy frontier's
pending marks and defers final-floor/equal-depth repair until a complete
band. Descriptor locality and pending anchor-bound transition theorems
are kernel checked. Its extra retained-word/overlap checks are bounded
runtime evidence; their whole-execution theorem remains open.
