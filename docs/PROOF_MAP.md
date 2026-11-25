# Proof map and current verification ledger

Updated 2026-11-25. This page describes the current code, superseding the milestone-by-milestone statements in [PROOF_HISTORY.md](PROOF_HISTORY.md).

**Two different goals must remain separate.** Complete source-language correctness is proved. The proposed soft-O(n^(25/13)) running-time bound for every fixed two-use pattern is not proved.

## 1. Complete semantic pipeline

The semantics in `Semantics.lean` uses one register, initially empty, overwritten when a capture closes. Nested captures include recalled text. `MatchesWithin p w 2` bounds executed references on the accepting trace.

| Step | Implementation and checked result |
| --- | --- |
| Remove irrelevant captures | `LiveCapture`, `PrunedSkeletons`, `LiveLanguage`: exact backward liveness, with at most 3k retained control markers |
| Compile regular marked code | `LiveCompiler`, `CodeInterpretation`: exact regular syntax and interpreter |
| Classify possible control orders | `ControlShapes`: ten shapes covering empty, one-use, same-value, independent, P1 and P2 cases |
| Construct ordinary finite automata | `RegularDFA`: explicit state enumeration and DFA closure for union, concatenation and Kleene star |
| Factor at marker boundaries | `MarkedFactors`: finite lists of ordinary DFA factors, preserving the fixed marker skeleton |
| Assemble concrete normal forms | `CompleteNormalization.normalization`, `pieces_normal`: actual finite union of six DFA form constructors |
| Execute a decision procedure | `FullMatcher.compile_correct`, `correctMatcher`: original `Spec.CorrectMatcher` for arbitrary expressions |

The normalization does not require an externally supplied automaton or an operational-code coverage hypothesis. Its constants may be enormous; the fixed-pattern model allows pattern-dependent preprocessing but does not make it practical by itself.

`FullMatcher` dispatches the regular, once, same-value, independent, nested1 and nested2 forms. Its nested branches use the previously verified blocked matchers; other branches use DFA acceptance or exact split enumeration. Its correctness theorem makes no strongly subquadratic time claim.

## 2. Periodic geometry and aggregate budgets

`Periodic.fineWilf` is proved by Euclidean subtraction. The verified consequences include minimum-period displacement divisibility, maximal equality-run geometry, phase block decomposition, and exact finite-state exponent descriptors.

For a maximal run R of least period q, define

```
mass R = R.hi - R.lo - 2*q + 1.
```

`RunBudget.totalMass_bound` proves, for a valid duplicate-free run list,

```
totalMass runs <= 2*n*DyadicIndex.heightFor n
heightFor n = Nat.log2 n + 1.
```

The proof charges primitive-square **occurrences**, not distinct strings. `ThreeSquares` gives at most two least-period square prefixes per dyadic period scale and start position. Maximality makes the charge injective across runs.

For cubic runs (`3*q <= length`) with q <= Q, `RunBudget.cubic_phase_bound` proves

```
sum_R q_R^(k+1) <= Q^k * (2*n*heightFor n).
```

`SmallPeriodRuns.enumerate` is now a concrete bounded-period generator. Membership is exactly `R.Valid f n` and `R.period <= Q`; the list has no duplicates. Its measured comparison count is at most

```
Q * (n + (n+1)*(2*Q*(Q+1)+1)).
```

It computes backwards equality endpoints once per period and tests candidate primitive squares. This is O(nQ^3); it is not the fast all-period LCE/run index needed elsewhere in the full algorithm.

## 3. Cached phase solvers

One `BoundaryContexts.build` scans the whole text and writes `(n+1)*(1+|H|)` context entries. Each run reads its two boundary rows. Its periodic/equality cache construction count is

```
q*(stateSum(P)*q) + q^3.
```

The seven DFA transfer tables and equality table are materialized arrays. Per-event formulas use these tables; they do not traverse a q-character block or the full external prefix/suffix.

`UniformProjection` and `UniformPhaseBounds` prove finite literal-erased shape families for the actual compilers. The sizes, coefficients, moduli and projected branch counts depend only on the pattern. P1 uses one positive common modulus `p1Modulus P` for every actual source and target event.

`CountedProjection` performs measured list/AST traversals, coefficient products, normalization, candidate construction, substitution, repeated elimination, environment reads and final decisions. Exact-value theorems relate these implementations to the uninstrumented specifications. Unit integer arithmetic is the explicitly stated abstract model.

`ProjectionMagnitude`, `PhaseMagnitude` and `P1Magnitude` prove literal preservation and bounds through **every** elimination stage. Evaluated affine constants have magnitude at most `C_P*(n+2)` and logarithmic magnitude-bit length. This does not by itself formalize the runtime's integer representation or garbage collection.

## 4. Concrete small-period P2 branch

`SmallPeriodP2.solve` generates the cubic runs, shares text contexts, prepares each run once and enumerates the actual five-phase family. Let `M = 2*n*heightFor n`.

| Measured quantity | Bound |
| --- | --- |
| Run comparisons | `Q*(n+(n+1)*(2*Q*(Q+1)+1))` |
| Context entries | `(n+1)*(1+|H|)` |
| Run-cache work | `(stateSum(P)*Q+Q^2)*M` |
| Phase calls | `Q^4*M` |
| Equality-cache reads | `6*Q^4*M` |
| Projection/decision operations | `CountedProjection.p2Steps P * Q^4*M` |

`solve_sound` has no witness assumption. `solve_complete` assumes a valid generated cubic run, period at most Q, a local P2 witness with correct exterior context, and outer-copy length at least q. It does not assert that every accepted word has such a witness.

`ArrayText.solveWord` materializes the finite input once. Its totalized array reader is defined even for the speculative out-of-range probes used by discarded run candidates; `segment_full` proves that the in-bounds text is the original word. Correctness and measured P2 bounds transfer to this wrapper.

## 5. Concrete P1 events and exact keys

`ExactKeys` is an actual deterministic trie over `Fin σ`. Child slots are finite lists, rather than accumulated function-update closures. Inserting many keys costs at most

```
(3*σ+1)*totalKeyCharacters + numberOfKeys.
```

Stable ranks are shared by all runs in one final registry. `buildRunTables` returns one phase-rank array per run, so an event reads one rank cell. Equality of encoded `(period,rank,residue)` keys is equivalent to equality of periods, residues and actual phase words. The integer encoding is less than `(Q+1)^2*(next+1)`, and `next <= M` from the empty registry.

`P1SourceFamily` creates one source record for every run boundary and source phase. `P1PhaseFamily` creates one target record for every anchor and the three remaining phases. The same variable represents the inner length in all constraints.

`P1Events.generated` is the cached executable event construction. `P1EventCounts` proves:

| Quantity | Bound |
| --- | --- |
| Source events | `3*Q*M` |
| Target events | `3*Q^3*M` |
| Trie work | `((3*σ+1)*Q+1)*M` |
| Cache construction | `(stateSum(P)*Q+Q^2)*M` |
| Equality reads | `9*Q^3*M` |
| Target projection operations | `CountedCachedP1.targetSteps P * 3*Q^3*M` |

A source formula describes the earlier capture and A prefix. The chronological join, not that source formula, verifies the actual C gap to the chosen target. This removes the invalid dependence of a reusable source event on a target-specific gap.

`SmallPeriodP1.solve_sound` connects actual generated-key joins to the original nested1 semantics. `solve_complete_long` uses `P1GlobalJoin.LongWitness`: the target is in a small-period cubic run, the inner source has length at least 3q, and the ordinary A/C conditions and equality hold. `LongSourceCoverage` then guarantees a generated source run of the same minimum period.

`P1ShortSources`, `P1ShortKeys`, `P1ShortTargets` and `P1ShortBranch` now implement the separate short-source dispatch. They intern all input factors of length less than 3Q and precompute each run's full-word keys for phase, residue and exponent m=0,1,2. Every target event reads its precomputed rank. Sources need not lie in a run.

The source count is at most `(n+1)*3Q`, the target count at most `9*Q^3*M`, source-trie work is O_σ(nQ²), and target-trie work is O_σ(nQ² log n). `CountedShortTargets` measures the actual target projection, three decisions and rank reads. `CountedShortBranch` includes the chronological join and sorting. `P1Cubic.solve_complete` and `CountedP1Cubic.solve_complete` now cover **all inner-source lengths** for their cubic, small-period, long-outer target witness class. `CountedP1Cubic.solveWord` transfers this to finite array-backed words.

`ShortSourceRegression` supplies a kernel-checked isolated-source witness on `babaaaa`: the earlier source `a` is outside the target cubic run. This is a semantic regression through the completeness theorem, not a claim that evaluating the full Presburger implementation on that pattern is fast.

## 6. Sorting and cost scopes

The old `OfflineJoin` counts interval tests, event visits, text visits and recursion nodes. Those counters do not count sorting comparisons.

`CountedSort` implements a measured stable merge sort, exactly equal to `List.mergeSort`, with at most `8*m*(Nat.log2 m+1)` measured sorting operations. `CountedJoin` uses it in the actual chronological recursion. With

```
W = K * (sourceFormulaWeight + |C|*targetFormulaWeight),
```

its measured sort work is at most

```
(heightFor n+1) * 10*W*(Nat.log2 W+1).
```

`ActualModulus.build` scans the formulas that were actually emitted and computes their positive shared LCM. It proves compatibility and divisibility into the fixed-pattern proof modulus. The large finite family used to prove a uniform bound is therefore not enumerated by the measured long-source matcher. The extra traversal is counted and bounded by formula sizes and event counts.

The projection compiler uses LCMs for coefficient scaling and guard periods. The previous product construction amplified duplicate factors: in one n=3, q=1 target, a candidate period of 262,144 fell to 2 after this change. Exact, kernel-checked compiler simplification equalities also replace deep list recursion with tail-recursive code. These changes preserve the semantic and counter theorems.

This closes the separate sorting-comparison obligation for that implementation. Formula/descriptor assembly, window conversion, cut-row construction and the various preparation counters must still be combined into a single specified machine-cost semantics. Array access, unit integer operations and fixed DFA sizes are explicit model assumptions, not an automatically proved property of compiled Lean machine code.

## 7. Actual global strips, sampled runs and schedule coverage

`GlobalCoverage` proves that every positive nonoverlapping outer-copy pair falls into six geometric cases: short, separated maximal equality strip, long-gap grid cut, low-exponent run, large-period cubic run, or small-period cubic run. The P1/P2 modules preserve the exterior DFA contexts when rebasing to a run. P1 keeps the earlier source in global coordinates, including sources outside every target run.

`GlobalSemanticCoverage.p1_cover` and `p2_cover` derive the absolute witness from `MatchesWithin` itself. No externally supplied layout or geometric coverage premise is required. Empty captures enter the short branch; the small-period branch concludes actual executable acceptance.

The global geometric lemmas are now connected to concrete index construction:

| Construction | Checked behavior and counted scope |
| --- | --- |
| `RankIndex` | Recompressed bounded ranks in arrays, using fixed-width exact binary-trie keys; no collision assumption |
| `LCEIndex`, `LCEIndexArray` | Maximum common prefix/suffix, with explicit text bounds; at most `13*(log2 n+1)+1` scalar-slot/array-read work per measured query |
| `IndexedGrid` | Shared forward/reverse preparation; every outer copy of length at least s is covered by an actual generated maximal strip |
| `RankIndexDivisors` | Actual divisor buckets; exact membership and at most `n*(log2 n+1)` cells, generated through multiples rather than testing all divisors per displacement |
| `RankIndexPeriod` | True minimum period of an overlapping maximal strip, found by LCE tests on its displacement's divisor bucket |
| `RankIndexRuns` | Valid maximal runs of arbitrary period; covers every run with `s <= hi-lo-period`, including exponent exactly two |
| `RunDedup` | Exact triple-key trie deduplication, membership preservation, no duplicates, at most `(26*(log2(n+1)+1)+5)*m` tracked work for m input records |
| `RankIndexSchedule` | Actual duplicate-free run list, total mass bound, generated low-start and large-period schedules |
| `IndexedGlobalCoverage` | Original P1/P2 matching implies small-period acceptance or a residual class carrying membership in those actual generated structures |

Let `H=log2 n+1`, `W=log2(max(n+1,σ+1))+1`, and `A=n/s+1`. Before deduplication, run generation returns the following counters:

| Counter | Bound |
| --- | --- |
| Two rank-index preparations | `2*(n+1)*(H*(16*W+4)+1)` |
| Divisor bucket insertion | `3*n*H` |
| Probes and raw run records | `A*(n+1)` |
| LCE/LCS extension work | `A*(26*H+2)*(n+1)` |
| Minimum-period work | `A*n*H*(13*H+6)` |

The divisor bound is summed across all displacements per anchor, so the minimum-period implementation does not scan all possible q at each strip. It also avoids scanning the total spans of arbitrary runs. That distinction matters: total run length can be quadratic, as shown by [Glen and Simpson, The total run length of a word](https://arxiv.org/abs/1301.6568). The existing cubic-run mass charging is used only where its hypotheses apply.

For the concrete generated list, `RankIndexSchedule.low_bound` is `(D+1)*2*n*H`. Filtering to cubic runs of period greater than Q gives `large_bound <= 3*n*(2*n*H)/(Q+1)`. These are generated candidate-list bounds; the matching queries performed for each candidate still need implementation and accounting.

## 8. Persistent boundary-index primitives

`BoundaryIndex` combines an ordinary DFA transition with active `(color,state)` cells. Its product carries left endpoints through the right word and unions them with right endpoints. The table representation is materialized finite vectors. Arbitrary color maps use existential images, so noninjective maps coalesce colors without discarding states.

`BoundaryIndexTree` stores these tables in a persistent balanced tree. A root recoloring costs a pattern-only constant; prefix queries, point reads, replacement and insertion cost a pattern-only constant times the height. Lazy maps are materialized finite vectors, not function-update chains. Pending maps are pushed before inserting a fresh endpoint, and earlier versions remain usable. DFA subset preimages in `BoundaryIndexColors` handle transitions that have no inverse.

`BoundaryIndexCuts` prebuilds all-open and all-closed switch-matrix indexes. An allowed-cut interval is answered by three range products, including the epsilon cut at the right endpoint. Its query uses at most six matrix multiplications and `3*(log2 n+2)` node visits. `BoundaryIndexFixedEnd` supplies the product-DFA and reversed-label interpretation required by the fixed-end construction.

`BoundaryIndexMerge`, `MergeSchedule` and `MergeBuild` implement persistent small-to-large merging. Each imported light endpoint is read from both versions, its active cells are ORed, and the destination point is persistently replaced. The heavy list is retained; only imported records are prepended. The schedule constructs its lists and cached sizes, and all leaf versions share one prepared static text tree. The checked transfer count equals the merge tree's light volume and is at most `N*log2 N`; each transfer costs O_P(height). Regressions cover duplicate positions, noninjective maps, static transitions and retained old versions.

The target-only merge schedule is not used as a substitute for mixed source/target heavy selection. `BoundaryIndexMixed` supplies silent source leaves of mass one, stores total mass separately from target-list size, and actually selects the retained child by total mass. Only target records move. Its transfers are bounded by the full merge tree's light volume, and `lightHeight_bound` proves at most `log2 N` light edges for total source/target mass N. A regression forces the heavier child by total mass to be the lighter child by target count, checking the distinction explicitly.

`BoundaryTrieKeys`, `BoundaryTrieSort`, `BoundaryTrieSearch`, `BoundaryTriePrepare`, `BoundaryTriePartition`, `BoundaryTrieEntries`, `BoundaryTrieTree` and `BoundaryTrieBuild` now construct the compressed source/target descriptor trie. One exact rank index serves every capped LCE comparison. Measured merge sort materializes one sorted descriptor array; each recursive interval uses an endpoint LCE and monotone binary search to partition by the next symbol. Words represented by keys are specification-only values and are not copied by the builder.

`Build.run_correct` proves record permutation, exact common-prefix/branch semantics and the explicit work bound. `run_nodes` gives `2*N-1` nodes for nonempty input; `run_paths` gives exact record/path membership; `run_path_lcp` identifies the stored LCA depth with the actual descriptor LCP. The work is `O(n polylog n + N log N log n)` in the returned rank/query/comparison counter model.

Empty keys, duplicate keys and proper-prefix terminals have distinct record leaves, with zero-length binary refinement edges. Such a binary node need not contain every occurrence of its prefix. `BoundaryTrieLocus.locate` follows a terminal path and stops at the first requested depth threshold. `locus_complete` and `Build.run_locus_complete` prove precisely the whole-root prefix-class membership at that selected locus, excluding later equal-depth refinements.

`BoundaryApplication` constructs the complete fixed-end color-index input: reversed descriptors for all source a<=g and target t>=g, exactly n+2 records, one materialized D range index, one static E tree, actual trie-edge maps, mixed program and persistent snapshots at every node. `build_work` composes these component counters. `queryPath_correct` identifies exact target positions, D colors and E acceptance on w[t:r]; cell 0 is identity and cell t>0 carries w[t-1]. Empty and terminal intervals are included. Lookup costs path.length+1, in addition to the logarithmic aggregate query; no logarithmic bound on an arbitrary raw trie path is asserted. `BoundaryApplicationRTable` now materializes the closed accepted-cut D-to-A-subset rows from actual shared finite-state queries. `Lift` imports only listed light endpoints across heterogeneous color spaces, preserving static E cells; `Subset` proves exact selected union and noninvertible edge preimages. `BoundaryApplicationHeavy*` now builds the actual cached-total-mass heavy subset versions, with exact static E preservation and light-import bounds. `Address`, `Jump` and `HeavyIndex` materialize one address cell per saved node, direct source slots and strictly decreasing head-jump ranks. The real query visits at most log2(n+2)+1 entries and uses a cached text length; it does not rescan the word or follow a raw trie path. `Locate.query_route_iff` (in the HeavyIndex namespace) proves correspondence to an actual source route, including duplicate-label last-write semantics. `BoundaryApplicationCoverage*` now closes source/target coverage through actual saved-route induction, light-list import semantics, A preimage propagation and LCA cut bounds. `Coverage.query_iff_cuts` states the expanded repeated-slice/A/B/D/E predicate with only valid endpoint assumptions. No trie/path/occurrence oracle remains. The C gap from the source end to g and original `Spec.boundaryRange` assembly remain outer integration obligations.

## 9. Masked reporting and event accounting

`MaskedReporting` recursively searches a balanced partition with an existence query that returns its own cost. If there are k outputs at height h, it proves at most `1+2*h*k` query calls, including unsuccessful calls, and at most `h*k` copied output cells. If each supplied query has a separately established bound A, total tracked work is at most `(A+1)+(2*A+3)*h*k`. The existence-query contract and its bound are explicit premises; this theorem does not create a fast masked predicate by itself.

`MeasuredMaskQuery` is an actual array-scan query and demonstrates the reporting path. Constructing the array of source truth values from arbitrary REWB masks is not provided by that demonstration.

`MaskedFiniteAction` materializes a vector of Boolean transition matrices and proves that pointwise multiplication commutes with uniform precomposition, even for noninjective index maps. `MaskedFiniteActionTree` implements persistent root reindexing, point replacement and prefix products, with exact semantics and bounds O_P(1), O_P(height) and O_P(height), respectively. This action uses precomposition, whose order differs from the boundary index's existential-image recoloring.

`MaskedFiniteActionMaps` enumerates all materialized m-state maps, proves its size is `m^m`, and supplies exact encode/decode and composition. `localAnchor_shortening` proves that prepending one common word segment to tails with different local anchors induces one common action on their finite summary banks. This closes the finite algebra/data-structure part; it does not construct the correct cluster matrices or prove the local geometric repair invariant. The remaining construction proposal is recorded in [MASKED_INDEX_NEXT.md](MASKED_INDEX_NEXT.md).

`MaskedFiniteActionRange` supplies suffix and arbitrary interval products. Only the two boundary paths are visited; whole subranges use caches. Its correctness theorem preserves chronological matrix order, including pending noninjective maps, and the general query costs at most `2*(h+1)*queryBudget(k,m)`. Noncommuting reset/swap matrices and fresh point replacements exercise both branches and clipping.

`MaskedProgression`, `MaskedProgressionQuery` and `MaskedProgressionAP` construct one actual `Array Nat` for an immutable mask on `[base,base+len)`. For step `K*q`, each position stores its mask bit plus the earlier count one step away. Exact construction charges are `3*len+(len-step)` array slots and `8*len+(len-step)` scalar operations; the combined bound is `13*len`. Every stored count is at most `len`.

`ap_build_correct` proves existence exactly for `j=s+k*q`, `lo<=k<=hi`, `k%K=r`, with physical-window clipping and an arbitrary mask. The executable query rejects zero q/K and invalid residues, and handles empty intervals, starts before the physical window and inclusive endpoints. It uses at most two array reads and 37 scalar operations. There is no preprocessing loop over q or K residues.

`MaskedCut` is a finite-monoid summary of all strict cuts, with a proved associative materialized product. Its two transformations always arise from one cut. `MaskedCutIndex` composes three indexed ranges to allow any closed cut interval; the terminal cut is included explicitly. One query uses at most three summary products and `3*(log2 n+2)` hierarchy visits. `MaskedCutRotations.batch` builds one doubled-period index and emits q result tables: preparation is `(log2(2q)+1)*2q` summary products; queries use at most `3q` further products and `3q*(log2(2q)+2)` visits.

`MaskedCutDFA` instantiates the monoid with materialized B/C/E transformation tuples, with universe size `b^b*(c^c*e^e)`. `MaskedCutTuples.queryConstrained_correct` retains B's prefix, C's suffix to the full period end and E's suffix to the run-end residue from one common cut. The common tail comes from a fourth range query, not a per-phase substring scan. An explicit lower cut bound handles positive remainders, including empty positive windows. Tuple table size depends only on the automata. These counters cover actual summary products and visits; finite-state operations remain a pattern-only factor, and the complete periodic branch ledger is a separate integration step.

`MaskedPeriodic` compiles the zero-remainder, positive interior and positive ending cases into finite-orbit formulas, projects to target block indices, and queries the real stepped mask array. `phaseQuery_correct` uses actual whole-period/fragment range maps and shared joint-cut tuple queries. Its common modulus is a cached pattern-only LCM; no loop enumerates all rho, lengths or target positions. Physical disjointness/end-bound arithmetic is separately proved. `MaskedPeriodicText` now supplies real periodic-text transport: `query_full_run_correct` uses an actual run and arbitrary source phase, and concludes exact source/gap/full-input suffix factors, repeated-copy equality and original target-mask reads. The current tail map is obtained once per run by `prepareTail`, with at most one summary product and log2(n)+2 visits. Too-short and after-end sources return false through an explicit guard. Descriptor/window construction and tuple materialization are still not included in the mask-query-only counters.

`MaskedEventBudget` constructs the small-to-large insertion schedule and proves exact local adjacency replacement. Each insertion creates at most two edges and removes at most one destination edge; absorbing the light child also retires its old edges. The accounting identity includes those retired light edges. There are at most `4*N*log2 N` generated density/overlap threshold records. The one-shot processing theorem requires processed and pending records to be a permutation of the generated records; rebuilding unchanged events is excluded. The separate unary regression proves that unconditional rebuilding creates `N*(N-1)/2` records.

The old ordered-list implementation remains a semantic reference. `MaskedOrdered` now constructs a sparse fixed-height position tree with cached counts/first/last, exact membership and strict predecessor/successor queries. An insertion performs one membership query, both neighbors and one path copy, using at most 28*h+18 counted slots. Duplicates preserve the existing tree and emit no records. `insert_reference` relates actual position/fresh/retired results to reference insertion for fresh keys.

The actual `MaskedOrdered.execute` threads one reverse ledger through its recursion, retains the larger cached-count tree and iterates only the maintained light list. There is no heavy-position scan, old-log copying, repeated power computation or repeated list-length heavy choice. `execute_imports` equals lightVolume, `execute_reference` identifies sorted final entries, and `run_work_bound` gives h+1+40*N*(log2 N+1)*(h+1) for bounded distinct leaves. Actual fresh and retired counts are at most 2*N*log2 N each; `run_balance` states fresh=live+retired. `discarded_positions` accounts for every old light adjacency exactly once, and `merge_new_edge` proves fresh provenance independently of import ordering. The complete owner validation below now uses this actual structure. Threshold cancellation and charged cluster repair remain later execution obligations.

The remaining masked-index amortization needs more than a bound on successful outputs. The supplied target mask must remain immutable; reported source starts are removed from a separate unresolved-source set. In `aaaa` with a one-character capture, unrestricted gap/suffix languages and target mask `{3}`, the same target occurrence witnesses starts 0, 1 and 2. Removing that target after the first report would lose valid outputs. Removing only sources avoids this specific defect, but unsuccessful searches, structural repairs and recreated threshold events still need a charged bound.

`MaskedRunDiscovery` now obtains the true minimum-period run directly from a dense consecutive pair in a complete occurrence class. `dense_least` forces the gap to be the word's minimum period; `candidate_dense` verifies the actual LCE/LCS extension, maximality and cubic span. Each discovery costs at most `26*(log2 n+1)+14` counted work, using shared rank indexes and no divisor search.

`MaskedRunDiscoveryEvents.first_live_generation` identifies the first binary coexistence and the actual insertion record that created a later surviving adjacency. It makes no least-period claim at the earlier partial merge. `MaskedRunDiscoveryLocus.prepareSuffixes` constructs n+1 suffix descriptors, builds the actual trie once and shares forward/reverse ranks. Its complete-class theorem follows from the first-threshold locus property. `discover_locus` therefore no longer assumes an externally supplied complete occurrence set. Equal-depth refinement queries are explicitly skipped. The complete owner traversal below now assigns the required first-threshold owners and processes/deduplicates the emitted records. Threshold scheduling for the dynamic matcher remains separate.

`MaskedRunCoverage.actual_suffix_coverage` starts with any valid cubic run and obtains actual descriptor paths for (lo,lo+q), their LCA depth H>=2q, the complete first-threshold owner with depth exactly H, true adjacency at that class, and an indexed discovery result exactly equal to the input run. `MaskedRunTrieBridge.compile_suffixes` constructs the binary merge schedule from that actual trie, rejects empty nodes, proves its leaf permutation is range(n+1), and bounds its tracked construction work by 8*(n+1)+1. The new owner enumerator uses this coverage to prove completeness of an actual emitted run list.

`MaskedLocalAnchor.reset` and `reset_terminal` derive actual H=L anchor certificates from complete occurrence classes. Only the final member can cross the next cluster boundary; its endpoint lies before the next cluster's second occurrence, or the subsequent singleton boundary, and remains in text bounds. `shorten` preserves fixed-neighbor certificates when overlap mode stays unchanged. `reset_square` derives the minimum-period square certificate at every copy from a dense gap. The dynamic constant-radius reset implementation and injectivity of charges along its execution remain open. `MaskedClusterStage` constructs an actual finite DFA with 1+|C|+|E| states, materialized marked jump vectors, exact arbitrary-code reading semantics and strict stage progression. `anchored_exact` proves that replaying a cluster representative's local tail yields precisely the true copy skip, even for noninjective transitions. `twoJumps_correct` gives the exact source mark, target mark, C-gap and E-suffix predicate. The new cluster cell compiler below constructs one-jump matrices. Whole cursor-block composition and changing cluster/overlap families remain separate from those local cells.


`MaskedOrdered.Owner.enumerateAuto` is a complete cubic-run enumerator on materialized finite-alphabet input. It prepares shared forward/reverse ranks and the suffix trie once, executes cached-count light merges, stores persistent node snapshots in an array, and tags only locally fresh adjacency events with their first equal-depth owner. The owner record is complete even when the emitting binary refinement was partial. Every event is checked against the final owner membership/successor relation before indexed extension and exact binary-key deduplication. `enumerateAuto_mem` is iff valid and cubic; `enumerateAuto_nodup` proves uniqueness. `MaskedRunEnumerationCost.enumerate_work` includes all returned preparation/execution work and bounds it by `(32*(sigma+2)+800)*(n+1)*(log2(n+1)+1)^2`. Exhaustive enumeration agrees on all 1,023 binary texts of length at most 9 and 1,093 ternary texts of length at most 6. A permanent equal-depth regression rejects a temporary gap-two pair while preserving the partial snapshot and accepting the true gap-one pair.

`MaskedPeriodic.Batch.solve` constructs the complete within-run all-start branch from that enumerator, one shared joint cut index and one cached pattern modulus. For each actual run it builds one target-mask prefix array and one real suffix map, then scans eligible sources and unions successful positions into a separate output array. `solve_correct` is exact for `Covered`: two nonoverlapping equal captures of length at least twice the actual run period, with all B/C/E conditions and the original target mask. `solve_sound` implies `Spec.maskedStart`. No external run list or query-answer function occurs at this entry point. `enumerated_span` bounds every visited source and every prefix-array cell by `6*n*(log2 n+1)`. `solve_work` includes enumeration, index products, mask preparation, loops and the existing query counters. It retains the explicit finite-compiler construction exclusions.

`MaskedCluster` derives two actual finite orbits for the positions before/after a candidate jump. Their one-variable formula uses a fixed LCM and compiles to at most K*|C|*|E| progression windows, without existential projection. Source and target arrays remain immutable and independent. Six range queries obtain real context maps, and two obtain the representative replay tail. `cell_direct_first` equates every dense cell with a literal physical copy skip; `certificate_onPeriod` derives its periodicity from an actual nonsingleton local-anchor certificate. `matrix_get`/`matrix_state` and `matrix_work` verify the materialized finite vector matrix. `pointCell_direct` supplies an independent constant-point singleton path without a false periodicity premise. Runtime comparison passed 30 complete matrices / 750 cells, including noninjective automata. Source-only reporting-window clipping, zero-jump and two-cursor block assembly, dynamic updates and full compiler accounting remain separate obligations.

## 10. Remaining obligations and the target exponent

1. **Complete masked all-start index.** Connect the finite-state summaries to the actual dense-cluster geometry, arbitrary-mask queries, local resets, source deletion and one-shot event scheduler. Count all repairs and failed searches.
2. **Complete boundary-aware range index.** Assemble `Spec.boundaryRange` from the now-complete fixed-end query and the remaining fixed-start, partial-edge and boundary-block components.
3. **Residual matcher dispatch.** Execute the short, separated, long-gap, low-exponent and large-period queries on the now-generated schedules. Prove their acceptance equivalence and aggregate work, then connect all six normal-form constructors to the accelerated implementation.
4. **Unified deterministic cost model.** Sum preparation and execution work, account for omitted fixed-shape assembly, specify word widths and memory operations, and connect those actual costs to the matcher target. A supplied unconstrained cost function cannot witness this goal.

The conditional phase ledger is

```
n^2/s + n*L^2 + n^2*s^2/L + n^2*s^2/D0 + n^2*s^2/Q
  + n*D0*s^2 + n*s^2 + n*Q^k.
```

P1 uses k=3, s=n^(1/10), Q=n^(3/10); P2 uses k=4, s=n^(1/13), Q=n^(3/13); both use L=D0=n^(1/3). `Cost.lean` checks the scaled exponents. `ThresholdBudget` now handles integer rounding for every n: let k=floor(log2(n+2)/39)+1 and t=2^k; choose s=t³, Q=t⁹ and L=D0=t¹³. The explicit ledger, with each quotient rounded upward, is at most 12*t^75. Its thirteenth power is at most `12^13*(2^39)^25*(n+2)^25`.

`ThresholdBudget.ledger_target` proves `Spec.Target25Over13` for that explicit numeric ledger. Two subsequent results now connect actual returned counters to it:

- `PeriodicAccounting.measured_target` sums the implemented long-source P1, short-source P1 and P2 periodic counters. Its thirteenth-power bound has logarithm exponent 13 and a fixed-pattern coefficient.
- `RankIndexScheduleAccounting.measured_target` sums the concrete rank preparation, divisor insertion, equality queries, minimum-period tests, probes and deduplication counters. Before taking powers, its bound is `[2*(16*(σ+2)+5)+240]*ledger(n)*(log2(n+2)+1)^2`; the target's logarithm exponent is 26.

`IndexedGridAccounting.measured_target` also covers the standalone strip generator's counters. These results are stronger than an arithmetic ledger alone, but they do not account for the missing matching queries or establish a complete matcher machine cost. The matcher instance of the target remains open.

## 11. Verification and publication

Use `bash scripts/check.sh`, `bash scripts/audit.sh` and `bash scripts/index-audit.sh`. The first checks the complete import closure and principal axiom reports; the second runs nine independent finite Python audits; the third runs twenty-four compiled-path audits. No proof placeholders, custom assumptions or native-evaluation proof shortcuts are permitted.

The initial published 2026-11-25 checkpoint passed the 153-target local build and all 307 principal axiom reports, using only standard `propext`, `Quot.sound` and `Classical.choice` where required. All nine Python audits and ten then-present compiled-path audits passed. The descriptor-trie, mask/cut and dense-discovery follow-up passed 179 build targets, 366 principal axiom reports and all fourteen compiled-path audits. Its exact local evidence is in [lean-build-status.txt](lean-build-status.txt), [audit-run.txt](audit-run.txt) and [index-audit-run.txt](index-audit-run.txt).

The subsequent real-text/constructed-index checkpoint `217237c` passed 221 build targets, 467 principal reports, nineteen compiled-path audits and both remote CI jobs in [run 45538726536](https://github.com/dmbs335/rewb-formal/actions/runs/45538726536). The current constructive continuation passes 262 build targets, 529 principal reports, all nine Python audits and all twenty-four compiled-path audits; its exact local evidence is recorded in the companion logs. No earlier CI run is presented as validation of later additions.

The previous run-coverage work in PR #13 passed remote CI and was merged. The original three-commit continuation was published in [PR #14](https://github.com/dmbs335/rewb-formal/pull/14) through the connected GitHub API. Its three file trees exactly match the original local commits; the publication metadata changed their commit IDs to `59c6403`, `971c238`, and `d3ef34a`. The last passed both remote jobs in [run 45531815252](https://github.com/dmbs335/rewb-formal/actions/runs/45531815252). Later additions require their own checks; the evidence logs and Git history identify the current local checkpoint.

Interpreted execution probes, repaired stack/candidate-growth defects, and practical limits are recorded separately in [RUNTIME_LIMITS.md](RUNTIME_LIMITS.md). In particular, the kernel-verified isolated-source regression must not be mistaken for a completed run of the full large P1 formula.
