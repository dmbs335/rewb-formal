# Proof map and current verification ledger

Updated 2026-11-25. This page describes the current code, superseding the milestone-by-milestone statements in [PROOF_HISTORY.md](PROOF_HISTORY.md).

**Current result:** `ResidualActual.FullCost.Matcher` is correct for the original bounded-use source semantics, and its concrete returned operation ledger satisfies `Spec.Target25Over13`. Measured initialization, finite cuts, repair/reporting, row production, periodic caches, run/key construction, event generation, and joins are installed through the actual six-form execution. The remaining machine-cost boundaries are stated below; the numerical target is a theorem about the explicit primitive-operation ledger.

## 0. Construction integration checkpoint

The unified code checkpoint is `8614bf808df5bbb5f73bd629951f01617923fa6c`. Its [main kernel job](https://github.com/dmbs335/rewb-formal/actions/runs/45601488688/job/139161244767) passed 772 build targets and exactly 3,017 distinct selected principal dependency reports: 54 without axioms, 2,963 using only `propext`, `Classical.choice`, and `Quot.sound`. The 78 new Lean modules add 674 distinct selected reports to the earlier checkpoint. The allowlist checker also rejects missing, repeated, or unexpected reports.

| Installed layer | Implementation and exact scope |
| --- | --- |
| Finite cuts and initialization | `PeriodicConstructionCut*` and `MaskedAllStartFullCostFiniteInitial*` preserve literal cut tables, starting state and old counters while measuring actual materialization and selection. |
| Traversal execution | `MaskedAllStartFullCost*` installs measured bank, repair, clip, query, report, erase and collection calls, preserving the complete previous result. |
| Rows and retained inputs | `MaskedAllStartFullCostRows*` and `ResidualActualFullCostInputs*` materialize actual tables, transfer Ready from value equality and charge every actual factory. |
| Primitive periodic preparation | `PeriodicConstructionCache*`, `Runs*` and `Keys*` build actual contexts, transition/equality arrays, run lists, words, tries and rank tables. |
| Periodic branches | `PeriodicActualFullCost*` composes those constructors with the measured formula/event/project/join paths and proves the rounded bound. |
| Cached dispatch and six forms | `ResidualActualFullCostCached/Dispatch/Independent/Matcher*` uses the refined branch costs and actual row production through the original source expression. |

The detailed installation and validation records are [Full construction execution](FULL_CONSTRUCTION_EXECUTION.md), [Periodic construction audit](PERIODIC_CONSTRUCTION_AUDIT.md), and [Full matcher construction](FULL_MATCHER_CONSTRUCTION.md). They distinguish kernel contracts, executed probes, generated-C inspection, and unsuccessful diagnostics.

Sections below retain useful earlier local interfaces and milestone evidence. An earlier statement that an interface consumer remained pending describes that checkpoint; this section and Section 10 give the current end-to-end scope.

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
| Execute a semantic reference | `FullMatcher.compile_correct`, `correctMatcher`: original `Spec.CorrectMatcher` for arbitrary expressions |
| Execute the actual constructed matcher | `ResidualActual.FullCost.Matcher.solve_correct`, `correctMatcher`: all six forms use the measured construction paths |
| Bound its returned ledger | `ResidualActual.FullCost.Matcher.Cost.correctMatcher_with_accounting`: correctness plus the 25/13 target, including installed row/periodic construction and fixed action charges |

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

`BoundaryApplication.StartIndex.build` now closes the fixed-second-copy-start primitive. For `g <= j <= r <= n`, `query_iff_cuts` is exactly the existence of `i,L` with `i+L <= g`, `j+L <= r`, equal slices `w[i:i+L] = w[j:j+L]`, and A/B/C/E acceptance on the actual prefix, capture, source-to-g gap and target-to-r suffix. The builder constructs forward descriptors, shared DFA ranges, one B-to-(C,E) cut matrix index, source summaries, both trie passes and the target locator. There is no externally supplied trie, program, path or cut-answer function.

`BoundaryApplicationStartLocate*` materializes one cached parent-doubling row per node in one preorder traversal. Actual target slots and cached depth rows choose the first threshold ancestor, crossing zero-depth refinements correctly. `StartPartial` then handles one closed compressed-edge cutoff, including a cutoff strictly inside an edge. The query never scans raw path lists or text lengths. `StartIndex.build_work` bounds the full returned construction work by an explicit `O_P((n+2)*(log(n+2)+1)^2)` expression; `query_work` is at most `6*levels(n)+StartStep.budget(B,C,E,n)+E.stateCount+10`. There are exactly `2*(n+2)-1` addresses. This remains the fixed-pattern matrix/array counter model, not a runtime allocation or bit-complexity proof.

The independent locator audit checks 30,733 cutoffs and 18,144 cached jump cells. A 16,385-node spine has 15 cached levels and query bound 96. The complete fixed-start audit checks 535 queries, including 114 strict interior compressed-edge cutoffs, with no reference mismatch. A length-512 case builds 1,027 nodes using returned work 1,392,948 and answers with work 354. Empty captures and noninjective E images have kernel regressions.

`BoundaryApplication.Separated` now closes the separated-endpoint primitive. For `g0<=g1`, its actual `build/query` accepts exactly when there are `a,L,t` with `a<=g0`, `L<=a`, `g1+L<=t<=right`, equal slices `[a-L,a)` and `[t-L,t)`, and A/B/C/D/E accepting `[0,a-L)`, `[a-L,a)`, `[a,g0)`, `[g1,t-L)`, `[t,right)` respectively. No supplied source summary, target bitset or acceptance predicate is used. Bottom-up C filtering and top-down D preimages are connected to actual trie cuts; the final E aggregate includes both the empty prefix and the terminal boundary. The full returned construction work has an explicit `O_P(n log² n)` bound and each E query an `O_P(log n)` bound.

Its bounded suite checks 1,007 endpoint bits and 1,007 E queries in 257 small builds, including distinct boundaries and noninjective A/D transitions. The 512-symbol case checks all 513 endpoint bits, builds with work 1,043,820 and queries with work 37. The generated-code record documents why the left result pair is destructured before descending right: otherwise a retained alias forces avoidable array copying. The same-block positive border primitive is completed in the continuation below. Full `Spec.boundaryRange` assembly still needs its remaining case integrations.

`BoundaryBorderGeometry/Select/Seed` now implement the equality selector on one supplied periodic AP component. `extend` obtains the maximal q-periodic prefix by the actual query `q+LCE(start,start+q)`. If the source end lies within that periodic interval, `inside_iff` reduces equality to the target periodic prefix being long enough. If the source end passes the first failed q-period comparison, `copy_past_break` forces the target failure at the same relative offset, leaving only the source `right-targetExtent`; a final actual LCE validates it. The selector returns one AP window, one point or empty, with work at most `39*(log2 n+1)+34`. It has no loop over lengths, source positions, periods or residues. `select_from_seed` derives every AP seed from one first-source/target prefix equality and the measured source extension, rather than taking a per-source equality family. The continuation below supplies complete short-window extraction and A/B/E filtering from the actual suffix index.

The independent selector audit compares 53,112 calls and 405,880 physical memberships: 44,092 AP bands, 4,880 exceptional points and 4,140 empty exceptions, with no mismatch. The n=4,096 probes use q=1,2,1,024,2,048, with returned work 342,328,202,188. Kernel regressions prove an actual indexed exceptional point and an actual clipped AP, through the indexed correctness theorems rather than a native-evaluation proof shortcut.

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

The actual `MaskedOrdered.execute` threads one reverse ledger through its recursion, retains the larger cached-count tree and iterates only the maintained light list. There is no heavy-position scan, old-log copying, repeated power computation or repeated list-length heavy choice. `execute_imports` equals lightVolume, `execute_reference` identifies sorted final entries, and `run_work_bound` gives h+1+40*N*(log2 N+1)*(h+1) for bounded distinct leaves. Actual fresh and retired counts are at most 2*N*log2 N each; `run_balance` states fresh=live+retired. `discarded_positions` accounts for every old light adjacency exactly once, and `merge_new_edge` proves fresh provenance independently of import ordering. The complete owner validation below now uses this actual structure. The queue family below now performs stale-adjacency validation; integration with charged cluster repair remains an execution obligation.

`MaskedThresholdQueue` is an actual persistent sparse maximum queue with cached counts and arbitrary duplicate-key buckets. `insert_spec` costs at most `12*h+5`, `takeMax_spec` at most `10*h+6`, and `drain_work` at most `(10*h+12)*(popped+1)`. The returned due list is in descending threshold order, is exactly the old records with key at least the new length, and leaves the complementary records pending. `drain_twice_bound` and `drain_no_replay` count consumed records once without reinsertion; both the stopping search and duplicate thresholds are included.

`MaskedThresholdEvents.add` combines actual position-tree insertion with queue insertion of only its locally fresh edges, generating at most four records and charging at most `76*h+110`. `shorten_correct` filters consumed records by current membership and strict successor, so stale adjacencies are excluded. Its work is at most `(10*queueHeight+11*positionHeight+31)*(popped+1)`. The audit checks 3,410 partition cases, duplicate thresholds, subsequent draining, 30 actual generated/consumed records with 14 cancelled pairs, and a 20,000-record height-20 queue. These theorems do not implement cluster repairs or prove the scheduler's global ordering. Crossed thresholds on a compressed edge must be processed before a lower-endpoint occurrence merge can cancel an intervening live adjacency; equal-depth refinement nodes cannot supply complete-class density charges.

`MaskedDensityCharge` assigns primitive-square records to actual suffix-trie preorder IDs. `locus_id_unique` and `locus_parent` prove that a fixed start/period uses the unique first `2q` threshold locus, with strictly smaller parent depth; a later equal-depth refinement cannot receive the same charge. `certify_completed_reset` derives the primitive-square condition from actual suffix-locus completeness and the local reset theorem. `actual_record` resolves this canonical ID to the real saved `Owner.run` record. `certified_budget` bounds any duplicate-free list of these actual certified records by `2*n*(log2 n+1)`. Kernel regressions retain a stored equal-depth child containing the same start while excluding its charge. The concrete repair execution must still prove that its generated records satisfy these certifications and are emitted once; the counting theorem does not assume that implementation invariant implicitly.

The remaining masked-index amortization needs more than a bound on successful outputs. The supplied target mask must remain immutable; reported source starts are removed from a separate unresolved-source set. In `aaaa` with a one-character capture, unrestricted gap/suffix languages and target mask `{3}`, the same target occurrence witnesses starts 0, 1 and 2. Removing that target after the first report would lose valid outputs. Removing only sources avoids this specific defect, but unsuccessful searches, structural repairs and recreated threshold events still need a charged bound.

`MaskedRunDiscovery` now obtains the true minimum-period run directly from a dense consecutive pair in a complete occurrence class. `dense_least` forces the gap to be the word's minimum period; `candidate_dense` verifies the actual LCE/LCS extension, maximality and cubic span. Each discovery costs at most `26*(log2 n+1)+14` counted work, using shared rank indexes and no divisor search.

`MaskedRunDiscoveryEvents.first_live_generation` identifies the first binary coexistence and the actual insertion record that created a later surviving adjacency. It makes no least-period claim at the earlier partial merge. `MaskedRunDiscoveryLocus.prepareSuffixes` constructs n+1 suffix descriptors, builds the actual trie once and shares forward/reverse ranks. Its complete-class theorem follows from the first-threshold locus property. `discover_locus` therefore no longer assumes an externally supplied complete occurrence set. Equal-depth refinement queries are explicitly skipped. The complete owner traversal below now assigns the required first-threshold owners and processes/deduplicates the emitted records. Threshold scheduling for the dynamic matcher remains separate.

`MaskedRunCoverage.actual_suffix_coverage` starts with any valid cubic run and obtains actual descriptor paths for (lo,lo+q), their LCA depth H>=2q, the complete first-threshold owner with depth exactly H, true adjacency at that class, and an indexed discovery result exactly equal to the input run. `MaskedRunTrieBridge.compile_suffixes` constructs the binary merge schedule from that actual trie, rejects empty nodes, proves its leaf permutation is range(n+1), and bounds its tracked construction work by 8*(n+1)+1. The new owner enumerator uses this coverage to prove completeness of an actual emitted run list.

`MaskedLocalAnchor.reset` and `reset_terminal` derive actual H=L anchor certificates from complete occurrence classes. Only the final member can cross the next cluster boundary; its endpoint lies before the next cluster's second occurrence, or the subsequent singleton boundary, and remains in text bounds. `shorten` preserves fixed-neighbor certificates when overlap mode stays unchanged. `reset_square` derives the minimum-period square certificate at every copy from a dense gap. The dynamic constant-radius reset implementation and injectivity of charges along its execution remain open. `MaskedClusterStage` constructs an actual finite DFA with 1+|C|+|E| states, materialized marked jump vectors, exact arbitrary-code reading semantics and strict stage progression. `anchored_exact` proves that replaying a cluster representative's local tail yields precisely the true copy skip, even for noninjective transitions. `twoJumps_correct` gives the exact source mark, target mark, C-gap and E-suffix predicate. The new cluster cell compiler below constructs one-jump matrices. The cursor family below now composes normal/overshoot blocks. Changing cluster and overlap families remains separate from those local semantics.


`MaskedOrdered.Owner.enumerateAuto` is a complete cubic-run enumerator on materialized finite-alphabet input. It prepares shared forward/reverse ranks and the suffix trie once, executes cached-count light merges, stores persistent node snapshots in an array, and tags only locally fresh adjacency events with their first equal-depth owner. The owner record is complete even when the emitting binary refinement was partial. Every event is checked against the final owner membership/successor relation before indexed extension and exact binary-key deduplication. `enumerateAuto_mem` is iff valid and cubic; `enumerateAuto_nodup` proves uniqueness. `MaskedRunEnumerationCost.enumerate_work` includes all returned preparation/execution work and bounds it by `(32*(sigma+2)+800)*(n+1)*(log2(n+1)+1)^2`. Exhaustive enumeration agrees on all 1,023 binary texts of length at most 9 and 1,093 ternary texts of length at most 6. A permanent equal-depth regression rejects a temporary gap-two pair while preserving the partial snapshot and accepting the true gap-one pair.

`MaskedPeriodic.Batch.solve` constructs the complete within-run all-start branch from that enumerator, one shared joint cut index and one cached pattern modulus. For each actual run it builds one target-mask prefix array and one real suffix map, then scans eligible sources and unions successful positions into a separate output array. `solve_correct` is exact for `Covered`: two nonoverlapping equal captures of length at least twice the actual run period, with all B/C/E conditions and the original target mask. `solve_sound` implies `Spec.maskedStart`. No external run list or query-answer function occurs at this entry point. `enumerated_span` bounds every visited source and every prefix-array cell by `6*n*(log2 n+1)`. `solve_work` includes enumeration, index products, mask preparation, loops and the existing query counters. It retains the explicit finite-compiler construction exclusions.

`MaskedCluster` derives two actual finite orbits for the positions before/after a candidate jump. Their one-variable formula uses a fixed LCM and compiles to at most K*|C|*|E| progression windows, without existential projection. Source and target arrays remain immutable and independent. Six range queries obtain real context maps, and two obtain the representative replay tail. `cell_direct_first` equates every dense cell with a literal physical copy skip; `certificate_onPeriod` derives its periodicity from an actual nonsingleton local-anchor certificate. `matrix_get`/`matrix_state` and `matrix_work` verify the materialized finite vector matrix. `pointCell_direct` supplies an independent constant-point singleton path without a false periodicity premise. Runtime comparison passed 30 complete matrices / 750 cells, including noninjective automata. The following cursor family now closes source-window clipping and local block assembly. Dynamic updates and full compiler accounting remain separate obligations.

`MaskedClusterSource*` clips only source jumps by a half-open physical reporting window; C-to-E target jumps retain the entire target mask. `MaskedClusterPass` adds exact no-jump reading. `MaskedClusterCursor*`, `PointCursor` and `Blocks*` construct the four normal/overshoot blocks, including incoming skips, empty normal ranges, skipped singleton points and outgoing overshoots. `compileDense_correct` and `compilePoint_correct` prove their actual materialized matrices denote the real zero/one-jump paths; `composeBlocks_denotes` preserves the intermediate cursor mode and waiting/C/E state. Source and target masks remain independent. Runtime comparisons cover 144 four-block compilers and 32 compositions, 17,600 matrix entries with no mismatch. One complete class `[0,3,8,11]` checks that a source at 3 skips target 8 but may use 11.

For `M=1+|C|+|E|` and `D=log2(n)+2`, `compileDense_work` bounds returned work by `15|C|+9|E|+192D+87+4M²(rowBudget+1)`, and singleton compilation by `7|C|+5|E|+96D+43+84M²`. Matrix composition charges both flattening copies and the full matrix product. Finite-orbit/formula construction, shared-index/mask preparation, global repair and reporting remain excluded from these local counters. In particular, the stepped source-count arrays are immutable: arbitrary removal of already reported starts needs a separately constructed maintained source structure. Query-time interval clipping alone does not implement that removal.

`MaskedClusterReplay` constructs the paired C/E replay-map universe of size `c^c*e^e`, with actual counted composition and common-prefix shortening for real slices at different local anchors. `MaskedClusterBank` tabulates the actual dense/singleton cursor blocks in `2*c^c*e^e` components, keeping enabled and disabled source gates. `tabulate_reindex`, `compileDenseBank_reindex` and `compilePointBank_reindex` identify the correct action order; the `_select_shorter` theorems connect a selected component directly to the shorter real-text compiler. The bank is usable by the existing lazy finite-action tree and its chronological products. The audit compares 2,400 real-text selected cells and 9,600 action/product entries, detects two reversed-order errors in noncommuting witnesses, and reports zero mismatches for the implemented order. A 2-state C/E root reindex costs 65 tracked operations. Source masks remain fixed here; global source deletion/repair and finite-compiler, pattern-catalog and action construction retain explicit accounting exclusions. The same-cut length selector and full cluster-sequence witness coverage remain separate.

### Mutable source indexes and actual deletion histories

`MaskedOrderedErase` removes one physical key along one tree path, preserving cached count/extrema and pruning empty nodes. `MaskedMutableProgression` encodes a local position `i` as `(i % step)*(len+1)+(i/step)`. The key is injective on the window and below `(len+1)^2`; the tree height therefore depends on `len`, not the magnitude of `step`. The actual index has cached base/length/step/height/capacity, logarithmic membership and erasure, and one-successor clipped grid/AP queries returning physical witnesses. It never enumerates residues. The bounds are at most `40*(len+1)*(log2(len+1)+1)` for construction, `37*(log2(len+1)+1)` for deletion and `79*(log2(len+1)+1)` for an AP query.

`MaskedSourceFanout.prepare` calls the actual cubic-run enumerator once, stores its run array and builds direct reverse source-to-run-ID rows. Row membership is exact, each row is duplicate-free and cached counts equal list lengths. Taking a row clears it; a repeated deletion cannot redeliver its addresses. All deliveries over any history are at most `6*n*(log2 n+1)`, using the already-proved total-span bound of the actual enumerated cubic runs.

`MaskedMutableProgression.Batch.prepare/eraseSource/run` builds one row index per run plus a global step-1 singleton index. It follows the actual reverse row when erasing a source, updates exactly those direct slots, and erases the global source once per request. `run_valid`, `run_member` and `run_query_correct` express every retained physical source as the original source-mask bit and absence from the actual request history. Targets and unmasked occurrences remain separate. With `L=log2(n+2)+1` and `m` requests, returned update work is at most `46*m*L+258*n*(log2 n+1)*L`. `run_total_work` includes the one enumeration, all source construction and all updates; no run or occurrence scan occurs during an erase.

### Shared-cut selection and banks for mutable sources

`MaskedCluster.Cut.queryBank_correct` ties B's prefix and the C/E replay maps to one and the same length in a closed interval. It uses at most three joint products and `3*(log2 n+2)` visits, then scans the stored finite joint relation once with at most `J^2` tuple probes. `CutRegression.rejects_mixed_cuts` rejects an actual query when the separate B and E successes occur at incompatible lengths. The default runtime suite uses bounded finite map sizes; its optional larger full-correlation run timed out and is recorded in the runtime limits.

`MaskedCluster.Mutable` replaces only the source-side AP and singleton membership operations with actual persistent index queries. Its snapshot array is a proof transport and is never built by the executable compiler. Dense/singleton banks, physical cursor correctness, uniform shortening and same-length cut selection all hold at the current source snapshot. A source erase cannot remove a target use, and the previous persistent bank remains unchanged. The `Mutable.Batch` adapter selects the row and actual run period by two direct run-ID reads; `compileRun_current` and `compileSingleton_current` conclude original-source-minus-history semantics. The adapter adds nine and one tracked operations respectively. Updating an old cached bank still requires a separate rebuild/ownership operation; these theorems do not silently turn old banks into new snapshots.

### Actual cluster leaders and empty-capture initialization

`MaskedClusterLeaders` defines a leader using the full occurrence set: no earlier occurrence is within half the current copy length. An insertion can change old leader status only at its strict successor. `add` queries that successor and repairs the inserted point and successor using actual tree insertion/erasure. `Future` proves that every still-needed threshold record is present in the actual queue. `changed_leader_record` then finds a live density record for every leader newly exposed by shortening. `shorten` drains and validates actual queued records, repairs their endpoints and preserves both invariants.

`execute_valid` initializes those invariants from empty trees and proves them through the actual guarded insertion/lowering loop. `execute_leaders` gives exact final component starts, including partial insertion states; no periodicity is attributed to such partial classes. Generated records are at most four per insertion and popped records are bounded by actual generation. Full loop work is at most `h+1+(305*h+416)*operations.length`. This closes the local leader/queue execution, but not the suffix traversal's intermediate queries or radius-two anchor repair. The independent stream audit compares 18,069 steps in 4,682 streams; a 4,096-position execution consumes all 16,338 generated records once.

`MaskedClusterDescriptor.locate/describeLeader/describe` now query the actual occurrence and leader trees with a constant number of bounded membership/predecessor/successor calls. They never scan entries. `locate_none_iff` and `describe_none_iff` prove totality exactly on actual occurrences. From a complete class, `describe_geometry` derives the least-period step, exact AP membership, penultimate/following positions and the actual `H=L` local reset certificate; the executable receives none of those certificates as inputs. Singleton descriptors use q=1,m=0, and L>0 yields a genuine last-start-before-n terminal bound. Costs are at most `11*h+9`, `39*h+39` and `50*h+50` respectively. Equal-depth refinement subsets are still insufficient for periodic geometry. `MaskedSuffixClass` now supplies the complete class from the actual first-threshold locus. These descriptor theorems still do not implement the global bank-repair traversal.

The descriptor audit checks 456,081 queries over 10,779 states in 770 operation streams, including incomplete temporary classes without assuming AP geometry. A height-20, 1,024-occurrence example splits one q=2 component into 1,024 singleton leaders, consumes 2,045 records and preserves its old persistent version. The complete-periodic kernel example connects the real descriptor to its derived geometry and terminal anchor certificate.

`MaskedEmpty.solve` materializes C/E Boolean vectors in one backwards pass and produces all `n+1` answer bits. `solve_correct` is exact for B accepting the empty word and a marked split `s<=j<=n` with C on `[s,j)` and E on `[j,n)`. Missing mask entries mean false. A proved compiler replacement uses a stack-safe fold, and returned work is exactly `(12*C.stateCount+6*E.stateCount+64)*(n+1)` in the stated unit-operation model. `maskedStart_partition` proves that every original masked witness is either this empty case or has strictly positive capture length.

`MaskedEmpty.SourceBatch.start` executes that scan, filters its actual answer array to a duplicate-free report list, and invokes the real source batch once with those deletions. `start_member` and `start_partition` prove that unreported original matches are precisely live-source positive witnesses. The full initialization bound includes array conversion, report creation, one run enumeration and all mutable-source updates. The empty scan passes 446,272 brute boundary comparisons over 65,984 inputs and a 100,000-symbol depth probe. Its actual source-batch connection passes 837 builds and 5,157 physical position checks, plus a 512-symbol exhaustive-source deletion run.

## 9a. Actual suffix classes, local repair and boundary cases

`MaskedSuffixClass` prepares the actual suffix trie, cached owner IDs, direct terminal slots and parent-doubling rows. `query_complete` gives the complete prefix class at the actual first-threshold locus; it takes no completeness premise. Length zero, the terminal suffix, strict interior compressed-edge cuts and equal-depth refinements are included. Full preparation costs at most `(32*(sigma+2)+830)*(n+1)*(log2(n+1)+1)^2`; an online query costs at most `6*(log2(n+1)+1)+15`.

`MaskedCluster.Mutable.Store` adds leader-keyed bank ownership to the mutable source batch. `eraseSource_coherent` and `eraseSource_complete` preserve exact stored banks for the fixed partition, while `eraseSource_other` shares every untouched slot. An occurrence deletion requires at most one slot write and compilation; a nonoccurrence inside a dense hull causes neither. The work theorem includes the actual descriptor lookup, mutable source/run fanout and the affected bank compiler. `describe_reset_geometry` supplies the actual H=L reset certificate. Cluster insertion/splitting, catalog lookup, immutable target preparation and global anchor updates retain separate obligations.

`MaskedTraversalEdge.run` consumes the real threshold queue in descending order and emits stable closed length bands. `run_valid`, `Chain.coverage` and `Chain.unique` prove exact coverage of the child-to-parent interval. Occurrences are retained, stale events are consumed once, parent-depth events are handled before the subsequent parent merge, and equal-depth refinements emit no band. The number of bands is at most pops+1, with scheduler work at most `(98*h+162)*(pops+1)`. This excludes bank/query callbacks. Its audit checks 14,592 schedules, 66,816 literal lengths and 35,389 actual pops; a billion-long singleton edge has one band, zero pops and work 42.

`BoundaryBorder.Window` extracts at most two actual occurrence components from a window shorter than the complete prefix length. Dense components obtain their true least period and maximal extent from the actual class and measured LCE; sparse components are singletons. `WindowIndex` supplies the complete class internally. `Dyadic.query_iff_slices` covers precisely every positive source length whose suffix at a equals a prefix at j, with work at most `317*(log2(n+1)+1)^2+3`.

`BoundaryBorder.Regular.dyadic_correct` adds the actual A-prefix, B-capture and E-suffix conditions and the right endpoint. Its progression path reads six shared range maps, builds the finite forward/backward orbit relation, clips the integer progression and calls the counted projection solver. It never enumerates represented AP positions, capture lengths or a huge exponent. The complete query work, including finite vector/orbit/formula construction, is at most `(2*fixedBudget(A,B,E)+521)*(log2(n+1)+1)^2`. Point candidates and empty choices have separate concrete paths. The positive-length contract is explicit; zero-length captures use the empty branch.

`BoundaryRange.six_cases` partitions the original boundary predicate into farLeft, farRight, nearSeparated, nearEnd, nearStart and nearBorder. All endpoint equalities are assigned explicitly. The automata module constructs initial/final changes, intersection, concatenation and reversal; no inverse transition is used. `split_gap` combines C/K/D with one common split, preventing an invalid combination of different regular-language witnesses.

`BoundaryRange.Table` eagerly builds every finite variant exactly once and stores its dependent payload in a materialized array. `NearIndex` retains the separated, fixed-end and fixed-start variants, shared C/K/D ranges and cached text length. `queryThree_correct` is the exact union of the three corresponding near cases; `queryThree_work` bounds the actual short-block scans by the product of the two relevant block widths and the proved primitive budgets. The generated-code record checks direct array selection and absence of text preparation in the query path.

`BoundaryRange.FarLeft` eagerly builds every finite K/C-state separated index at the grid boundary. A query obtains the K state by one shared range query, reads the stored row and scans only the fixed C-state universe. `query_correct` is exact for the farLeft region. Full preparation includes all actual component work; the query bound is logarithmic for fixed automata. `FarMask.build` constructs the reversed far-right target mask with one shared range read per boundary. `farRight_step` proves the exact reduction to reversed masked all-start outputs followed by an E suffix aggregate. That last fast masked execution and final six-case union remain pending.

### Complete geometric traversal, automatic bank preparation and residual windows

`MaskedTraversalFrontier` and `MaskedTraversalDriver` now implement the whole bottom-up suffix-trie schedule. Both children execute all crossed thresholds down to the parent depth before the light frontier is imported. Equal-depth refinements emit no band. The heavy queue is retained, the light queue is discarded and its entries counted, and only the light occurrence list is traversed. `build_imports` identifies imports with the actual trie light volume. `build_measured` proves generated/pop/discard/pending conservation; `suffix_work` bounds the complete geometric driver, excluding bank callbacks and reporting, by an explicit `O(n log² n)` expression.

`build_band_locus` proves full first-threshold occurrence membership at each emitted length, not merely the final node depths. `suffix_cover` covers all real positive source/length pairs. `MaskedTraversalBandUnique` proves pairwise disjointness of the proof-only flattened band view and `suffix_exactly_once`. Its `DensityAt` requires a source at length `2q` and a genuine full-class adjacency of gap q. `density_square` derives the primitive-square certificate, and `suffix_charges_budget` bounds globally emitted keys by `2*n*(log2 n+1)` using only local emitter distinctness and actual band attribution. The dynamic repair scheduler must still establish those two local hypotheses for its emitted events; no global duplicate-freedom premise is supplied.

`MaskedRunCatalog` creates a direct-ID binary-key index and target-count array once for each run already in `MaskedMutableProgression.Batch`. `ofBatch_exists`, `ofBatch_counts` and `ofBatch_eraseMany` preserve exact run IDs and immutable target counts. Construction costs at most `401*(n+1)*height²` in the local catalog ledger; `prepare_work` also includes the one actual batch preparation. Dense descriptor discovery uses cached key width, obtains the true minimum-period run from the actual complete class, and looks up its exact ID. Generated lookup code performs no run/text scan or power construction.

`MaskedTraversalBankReady` obtains the actual descriptor, current predecessor, stored anchor and incoming cursor, then calls the existing mutable compiler and directly writes the selected leader slot. `compile_reset_current` gives the literal physical `CursorStep` for the actual source deletion history, for dense and singleton cases. `compile_reset_work` is at most `85*h + 52*width(n) + 137 + bankLimit`. It assumes the explicit retained-neighbor `AnchorBounds` invariant and resets the selected anchor to `H=L`. It does not yet prove changing-partition dirty-set completeness, retained-H successor refresh or finite-action aggregate coherence.

`BoundaryRange.NearIndex.Border` finishes the fourth near region. Actual finite C/K-state variants store the common-gap automaton and its range index together. `gap_iff_split` requires one common C/K/D split. The query combines A/E ranges, the positive dyadic selector and an empty-copy case; no capture-length or common-split loop occurs in the query. `NearIndex.Full.query_iff` is exactly the union of all four near regions. The implementation caches text length and height to avoid dependent-argument recomputation in generated queries; the code-generation audit records this repair. The reversed far-right masked path remains outside the near index.

`ResidualSeparated.Window` states equality, text bounds and separation of two aligned windows. `Window.copy` transports every contained interval, while `gap_run` and `outerSuffix_accepts` factor the actual G/H constraints using shared ranges and a finite G state. `p1_iff` is the exact original endpoint predicate for `Spec.boundaryRange`; the earlier first source can precede the window. `p2_iff` uses `Spec.oneUseRange` because its source must remain inside the window. Both witness soundness theorems return the original nested matching semantics. Regressions prove the source-lower-bound distinction, rather than silently substituting the boundary predicate.

`ResidualRunWindows.candidate` selects `[p,min(R.hi-d,p+d)]` for one actual run/start/displacement entry, using at most 11 scalar operations. Validity plus period divisibility gives a true separated equality window; `low_window` and `large_window` connect the actual generated schedule lists. There is no per-entry scan of a period or text segment.

`ResidualStripSchedule` deduplicates actual `IndexedGrid.generate` triples and selects long strips. A proof-only equality-cell packing gives total maximal-strip span at most `n²` and at most `n²/L` long strips. Separated strips emit one bounded window directly. Only overlapping strips enumerate grid cuts; their displacement is smaller than their span, allowing the actual query-count bound `2*n²/D + 3*(n²/L)`. `prepare_existing_cut` covers an already supplied long-gap grid witness without assuming `D` is at most the gap. `prepare_work` includes real generation, deduplication and cut construction. The query predicates still need their complete fast indexes.

### Actual repairs, shared aggregate cuts and residual query caches

`MaskedTraversalDirty` obtains its keys from actual insertion patches and validated live events, with at most nine requests per event. `MaskedTraversalRepair` first resets every selected anchor and then rebuilds the banks, so simultaneous resets read the new predecessor anchors. Its checked reset cost is `(85*h + 52*width(n) + 149 + bankLimit)*dirtyCount + 6`. The prerequisite concerns only unmarked anchors; stale selected anchors are allowed. The new Neighbor family proves descriptor locality and pending anchor-bound propagation through actual insertions, live thresholds and merges; global retained-word/cursor coherence remains separate.

`MaskedTraversalNeighbor.add_describe_away` proves the entire actual leader descriptor unchanged outside the actual insertion keys. `crossing_describe_unmarked` uses the real shortened live records, and `merge_describe_unmarked` accumulates actual heavy-side import patches, including partial equal-depth states. `add_anchorBoundsAway`, `crossing_anchorBoundsAway` and `merge_anchorBoundsAway` propagate the two-pass reset prerequisite from the prior pending state. Thus reset bounds are no longer re-assumed independently at each transition. Retained H-word and overlap certificates, predecessor context and slot/aggregate coherence still need their global execution proofs.

`MaskedTraversalContext` constructs the exact successor set, proves all other incoming records identical and refreshes those successors without resetting their own anchors. `RunBacked` refers to the actual stored run ID and immutable prefix counts. `store_current` derives the physical current-source relation for `H >= L` from real descriptor geometry and the cluster's retained anchored-copy certificate. It does not require different clusters to share their longer H prefixes. The successor selection cost is at most `(39*h+34)*resetCount+1`.

`MaskedTraversalAggregate.prepare` constructs one shared identity tree. Fresh frontiers reuse it in one operation. Actual slot refreshes, lazy shortening, region products and accepting-state closure are proved against the tree leaves. `queryBand_correct` gives one actual length L, a B-accepted prefix, and one chronological product path at the same replay key. `physical_final` and `queryBand_sound` map literal continuous cursor paths back to original C-gap/E-suffix witnesses. Identity leaves are skipped by `Denotes.skip`; they do not require fabricated cluster configurations.

`MaskedTraversalAggregateReplay.store_select_shorter` lifts common-prefix shortening through the real mutable run/singleton adapters, including missing or incompatible run branches. `store_shorter_current` identifies the stored replay cell with the actual shorter-length transition, using current source histories and fixed target masks. Local retained-copy certificates and actual descriptor geometry remain explicit.

`Clip.plan` performs two real predecessor queries and deduplicates their leaders. `plan_selection` proves that widening the gate to the lower boundary leader and clipping these at most two banks selects exactly the physical source positions in the requested window. `queryWindow` recompiles only those banks and makes at most one shared-cut query; unsuccessful compilation rejects the query. Its boundary work is at most `14*h+17+2*(bankLimit+(h+1)*replaceBudget+10)`, in addition to the proved aggregate and shared-cut counters. This is a concrete query operation, not a callback with an assumed cost. Whole-driver stored-bank/anchor preservation and cross-cluster completeness have not yet been proved.

`OneUseRange.Border` uses six actual shared range maps, finite midpoint C states and a positive dyadic border query. Its actual near scan is bounded by the product of the two short-block widths times a fixed-pattern logarithmic-square budget. `OneUseRange.Cache` eagerly prepares forward and reversed far banks, shared near indexes and grid positions. `query_correct` is exactly `Spec.oneUseRange` given finite input rows satisfying `Ready`. `query_bits` is unconditional about the supplied bits. Build/query work is proved without a `Ready` assumption, but those counts exclude production of the all-start rows. A generated-code audit removed a hidden text reversal from the query wrapper by using word-free `keyCore` and `queryCore` selectors.

`OneUseRange.FarAggregate` implements the actual backward DFA row recurrence over an immutable bit array. Build work is at most `(6*A.states+7)*(g+1)` and query work at most four. Its exact witness theorem covers empty and short masks and the terminal boundary. Substitution of a proved all-start bit row is explicit.

`ResidualDispatch.prepare` reuses one actual sampled-run schedule and the deduplicated strip schedule, emitting one concrete separated window per selector. `p1_dispatch_iff` and `p2_dispatch_iff` give the exact source-language disjunction of the real small-period branch, a short-outer witness or a scheduled `boundaryRange`/`oneUseRange` predicate. All query-to-language directions are proved, including the unrestricted earlier P1 source. Selector counts and actual preparation work are bounded. These exact predicates still need the complete fast query execution.

`ShortOuter.Keys` assigns exact bounded-substring keys; `ShortOuter.Sweep` retains a timestamp and a finite G-state vector for each key. `ShortOuter.Band.build` scans backward, inserts every eligible H-suffix target and queries at source-copy ends. `get_iff` is exactly `ell < L`, source bounds and existence of a nonoverlapping equal copy with the original G gap and H suffix. It includes the empty copy. With `b=min(L,n+1)`, actual touches are at most `2*(n+1)*b`, build work is explicitly `O_{sigma,G,H}((n+1)*(b²+b log(n+1)+log(n+1)))`, and queries cost eight. No arbitrary mark/all-start function is supplied to this constructor. P1/P2 nested joins remain to be connected.

### Retained metadata, exact window cells and complete short-outer consumers

`MaskedTraversalRetained` records actual populated anchor slots and local H-word certificates. `add_away`, `merge_away` and `crossing_away` transport them outside the computed dirty keys; `reset_all` derives selected certificates from complete occurrence classes. `band_all` preserves them for every length represented by an actual emitted band. No production loop enumerates those lengths or AP copies.

`MaskedTraversalIncoming.predecessor_preserved` derives the unchanged predecessor outside the actual successor closure. Actual insertion, merge and crossing wrappers preserve both incoming cursor and enablement. `reset_preserves_transport` includes the entire anchor-reset pass; `retained_config_preserved` identifies all fields of a retained configuration after length normalization. Populated anchor reads remove dependence on a default current length.

`MaskedTraversalAggregate.Cells.Coherent` describes this frontier's sparse proof model and its relationship to shared raw slots. Raw slot lengths may remain historical after a lazy tree tag. `store_reindex` proves full stored-bank equality under actual common-prefix shortening. `Coherent.shortened` preserves the current compiler result and the raw-slot normalization invariant.

Source repair now uses `eraseCurrent`: it normalizes the selected configuration to the current length before compiling and replacing its leaf. Reusing the historical raw configuration would restore a stale longer-length bank. `eraseCurrent_ready`, `eraseCurrent_coherent` and `eraseCurrent_complete` prove success, current compilation and continued presence of every actual leader from the prior maintained state. Other banks remain current by actual owner exclusion. The source batch changes; immutable targets, anchors, run IDs and target prefix counts stay intact. `eraseCurrent_linked` preserves the actual metadata links.

`Current.cell_meaning` derives each physical cell from the actual compiler, complete old/current classes, retained anchors and real predecessor/run metadata. `window_ready` proves both boundary compilers succeed from actual complete coherent slots. `clipEntries_current`, `clipEntries_linked` and `clipEntries_complete` describe their exact temporary sparse model. `queryWindow_physical` is an equivalence between the concrete query answer and a literal cursor path at one common B-accepted length. It has no supplied cell-semantics or readiness oracle. `clipped_source_iff` proves exact physical source-window selection, and `windowParts_marks` recovers source-history and unchanged target eligibility. Ordered path completeness and whole-driver execution remain distinct obligations.

`Current.bank_geometry` derives compiler cost preconditions from actual descriptor/anchor/incoming data. `queryWindow_actual_clipping_work` and `eraseCurrent_actual_work` apply the real compiler counters without a supplied bank-cost or geometry function. Per-query aggregate/shared-cut work remains charged by its existing returned counters.

`BoundaryRange.FarRight.prepare` creates the actual reversed E/K-dependent masks. Its `ready_original` theorem translates their finite all-start rows back to original coordinates. `BoundaryRange.Cache` constructs the shared near, left and far-right caches; `query_correct` is exactly `Spec.boundaryRange` under the finite-row `Ready` contract. Preparation, assembly and queries have explicit actual work. This closes cache assembly, but does not construct the missing fast all-start rows.

`ShortOuterP1.solve_correct` and `ShortOuterP2.solve_correct` now recognize exactly `ResidualDispatch.ShortP1` and `ShortP2`. Their actual bounded F-prefix rows, event lists and CountedJoin calls include empty inner/outer copies, unrestricted earlier P1 sources and local P2 inner sources. `ShortOuter.Dispatch` substitutes these real results into both residual language partitions. With `b=min(L,n+1)`, `S=(n+1)*(b+1)^2` and the relevant fixed C/D state count k, both complete work counters are bounded by a fixed-pattern coefficient times `S*(log2(n+1)+2)*(log2((k+1)*S)+1)`. Keys, input preparation, event lists, range maps, sorting and joins are included.

### Complete cross-cluster queries and executable report/repair cycles

`MaskedTraversalCompleteStep/Pass/Path/Order` derive an actual chronological normal/overshoot path from a distinct-owner source/target witness, and recover its exact source, target and gap semantics in the reverse direction. `Geometry/Window/Sound/Correct` supply actual descriptors, owner ordering, physical clipping and the shared B-cut condition. `queryWindow_iff` is exactly the current-source, immutable-target, distinct-cluster repeated-slice predicate at one length in the band. It derives cell readiness and semantics from the maintained frontier and takes no answer oracle.

`MaskedTraversalAggregateEraseMany` proves exact source histories and maintained compiler/aggregate/metadata invariants for actual repeated erases. `Reporting.run` performs real output-sensitive interval queries followed by these erases. `run_correct` proves exact reported starts, `run_exhausts` proves no current witness remains in the band, and `run_charged` includes unsuccessful queries, output copies, current-length bank repairs and the source-delivery potential. `Answers` stores a real bitmap and reverse chronological history, proves duplicate freedom, and bounds the total output by n+1. `Collect` combines reporting with bitmap writes and keeps the source deletion history equal to the output history.

`MaskedTraversalAggregateDisjoint` and `MaskedTraversalSuspended` preserve a saved frontier across another occurrence-disjoint frontier's actual source erases, raw-slot updates and anchor resets. Pending incomplete classes retain the same sparse model and dirty keys. These theorems derive support from real candidate ownership and saved leader reads; they do not copy the entire mutable global state.

`MaskedTraversalRepairCoherence` builds the actual two-pass reset and successor refresh, synchronizes both sparse aggregate update passes, and proves coherent banks, complete leader coverage, linked incoming metadata and populated anchors. `RepairSnapshot` obtains run-backed geometry from the canonical catalog/classes and the actual current source history. `apply_snapshot_work` charges the real selected keys. `RepairTransportShorten` derives the reindexed compiler, unclipped geometry and pending crossing invariant after the actual replay action. An overlap-crossing regression establishes why an omitted reset would be invalid.

`MaskedTraversalPeriodicCoverage` constructs an actual enumerated least-period maximal run for every same-owner nonoverlapping copy pair in a complete class. `same_owner_hit` shows that the real periodic batch reports it. `original_partition` therefore leaves only distinct-owner witnesses for the band query, including arbitrary original cut endpoints.

`MaskedTraversalInitial` executes empty and periodic solvers, constructs their actual union bitmap/history, and deletes those sources from the run/global source batch. Its accounting includes both enumerations, bitmap construction and source fanout; it inherits the stated periodic finite-compiler exclusions. `MaskedTraversalPositiveCoverage` derives complete metadata for a represented band and assigns every surviving original witness to the actual unique source/length band. `PositiveCoverageExhaustion` proves monotonicity under later erases and obtains the full answer contract once every actual band has been exhausted.

`MaskedTraversalExecute` is the concrete chronological consumer of the retained geometric plan. It carries one global source/store/anchor/output state, retains child frames, chooses the actual heavy frontier, and executes dirty repair, reporting, current-source deletion, common-prefix replay and live-event marking. Equal-depth edges do no band query or initial drain. Whole-plan invariant preservation and exhaustion are now proved by the `Invariant`, `Effect`, `Band`, `Edge`, `Plan` and `Suffix` continuation. `MaskedAllStart.solve_correct` constructs all premises internally; `MaskedTraversalExecute.Cost` sums actual repairs, queries, outputs and fanout work.

## 10. Installed construction accounting and remaining machine model

The current public namespace is `REWB.ResidualActual.FullCost.Matcher`. Its `correctMatcher` proves `matchWord p fallback w = true ↔ MatchesWithin p w 2`. The matcher takes the source expression/text/fallback; no Ready, row, answer, split, frontier, exhaustion, or budget premise is supplied by its caller.

`Cost.solve_charged_bound` has the quantifier order

```text
for each fixed p and charge:
  exists coefficient,
  for every text and fallback:
    actualAccountedWork + charge * actualFixedPatternBuilds
      <= coefficient * ThresholdBudget.base(n)^75 * height(n)^3.
```

The coefficient is independent of text length, contents, and fallback. It is obtained from the finite compiled form list and fixed-pattern component coefficients; no such envelope is evaluated by the actual matching path. `Cost.wordWork` uses the concrete `solve` result and adds the linear word-array charge.

`target_of_bound` raises this inequality to the thirteenth power and uses `base(n)^39 <= 2^39*(n+2)`. The selected `Target25Over13` logarithm exponent is 39. A positive target constant is `(coefficient+1)^13*(2^39)^25`. `Cost.correctMatcher_with_accounting` pairs that target with original-source correctness.

The substitution is implemented, not merely supplied as a hypothetical family of fast rows or periodic answers. Public all-start preparation invokes measured finite initial scans, cut construction, modulus/action preparation and execution. Its actual plan invokes the measured repair/report/erase families. Row factories store their produced values and counters. FullCost Cached P1/P2 invokes the measured periodic solver and reads its returned work. Independent forms invoke two actual rows and the regular-gap join. The older functions occur in value/cost comparison proofs where required.

### Explicit accounting boundary

- Pattern compilation is fixed-pattern preprocessing. `compile p = CompleteNormalization.forms p` can be run once and `run compiled` reused. Convenience `solve` calls compilation, but its returned text ledger does not separately meter normalization.
- The alphabet is a fixed nonempty finite type at the public entry point, because `fallback : Fin σ` is required. Empty words are fully included.
- Scalar arithmetic, direct array access, DFA operations, comparisons and the explicitly instrumented list/tree/array operations use their stated primitive costs. `ActualModulus` and `CountedProjection` retain unit-cost `Nat.lcm` calls. These are not replaced by the separately measured Euclidean-loop implementation in `PeriodicConstruction.Pattern`.
- Source-cost equalities for compiler substitutions do not constitute a general cost-preserving compiler theorem. Arbitrary-precision bit work, additional runtime accumulator/reversal passes, reference-counting/copying, allocation, garbage collection and all generated C instructions are outside the final claimed ledger unless separately covered by a named bound.
- Targeted generated-C checks show the inspected paths do not repeat the old public solver, report/erase, or row/input factory. They are scoped compiler regressions, not a universal runtime ownership theorem.
- Conservative sums may count some operations more than once. This is safe for the proved upper bound; the counters are not presented as a bijection with machine instructions.

The former construction-substitution obligation is closed for this model. A full machine-cost refinement and practical implementation/constant reductions are separate work. Actual positive P1 and full expression-composition runtime limits are reported in [RUNTIME_LIMITS.md](RUNTIME_LIMITS.md), and are not promoted to passing executable checks.

## 11. Verification and publication

The current unified kernel checkpoint and exact principal counts are given in Section 0. The legacy 83-probe inventory is preserved and sharded into 28/28/27 cases; the nine Python reference audits are unchanged. New construction probes and the two generated-C inspectors are listed in the linked integration audits. The final PR metadata records the actual published head and exact CI result. A failed, cancelled or optional timed-out diagnostic is never counted as a completed passing probe.

### Earlier verification checkpoints


Use `bash scripts/check.sh`, `bash scripts/audit.sh` and `bash scripts/index-audit.sh`. The first checks the complete import closure and principal axiom reports; the second runs nine independent finite Python audits; the third runs eighty-three compiled-path audits and the public all-start generated-code regression. No proof placeholders, custom assumptions or native-evaluation proof shortcuts are permitted.

The initial published 2026-11-25 checkpoint passed the 153-target local build and all 307 principal axiom reports, using only standard `propext`, `Quot.sound` and `Classical.choice` where required. All nine Python audits and ten then-present compiled-path audits passed. The descriptor-trie, mask/cut and dense-discovery follow-up passed 179 build targets, 366 principal axiom reports and all fourteen compiled-path audits. Its exact local evidence is in [lean-build-status.txt](lean-build-status.txt), [audit-run.txt](audit-run.txt) and [index-audit-run.txt](index-audit-run.txt).

The subsequent real-text/constructed-index checkpoint `217237c` passed 221 build targets, 467 principal reports, nineteen compiled-path audits and both remote CI jobs in [run 45538726536](https://github.com/dmbs335/rewb-formal/actions/runs/45538726536). The constructive checkpoint `11ab511` passed 262 build targets, 529 principal reports, all nine Python audits and all twenty-four compiled-path audits, plus both remote CI jobs in [run 45542428574](https://github.com/dmbs335/rewb-formal/actions/runs/45542428574). The fixed-start/cursor/queue/density/replay-bank checkpoint `e6de9b4` passed 309 build targets, 638 principal axiom reports, all nine Python audits and all twenty-nine then-present compiled-path audits. Both exact-head remote runs passed: [push 45546061432](https://github.com/dmbs335/rewb-formal/actions/runs/45546061432) and [PR 45546067038](https://github.com/dmbs335/rewb-formal/actions/runs/45546067038).

The mutable-source/empty-capture/border-selector checkpoint `14ff501` passed 376 build targets, 870 principal reports, nine Python audits and forty-one compiled-path audits locally. Its [push CI](https://github.com/dmbs335/rewb-formal/actions/runs/45554195132) passed. Its [PR CI](https://github.com/dmbs335/rewb-formal/actions/runs/45554201034) passed build/dependency checking, then reached the old 20-minute timeout during the separated deep probe; it is recorded as cancelled, not passed. The Lean job limit is now 40 minutes.

The suffix/store/border/edge/cached-boundary checkpoint `88959f2` passed 429 build targets, 1,066 principal axiom reports, nine Python audits and forty-nine compiled-path audits. Both exact-head CI runs passed: [push 45559126615](https://github.com/dmbs335/rewb-formal/actions/runs/45559126615) and [PR 45559133020](https://github.com/dmbs335/rewb-formal/actions/runs/45559133020).

The driver/catalog/near-border/residual-window/strip-schedule/bank-preparation checkpoint `9048279` adds 39 modules and 153 principal reports. Its full local gate passed 468 build targets and 1,219 principal reports, all using only permitted standard axioms. Runtime evidence combines the unchanged successful forty-nine-audit prefix with six completed new audits. The nine Python audits are unchanged. Optional interrupted stress runs are excluded and recorded in RUNTIME_LIMITS.md; an earlier remote run does not validate later additions.

Both exact `9048279` remote runs passed: [push 45563760515](https://github.com/dmbs335/rewb-formal/actions/runs/45563760515) and [PR 45563767603](https://github.com/dmbs335/rewb-formal/actions/runs/45563767603). The new repair/context/neighbor/aggregate/one-use/residual/short-outer continuation adds 64 modules and 252 principal reports. Its complete local gate passed 532 build targets and all 1,471 principal dependency reports, using only permitted standard axioms. Runtime evidence combines the unchanged successful 55-audit prefix with nine completed new compiled-path audits, for 64 total. The nine independent Python audits are unchanged. Those earlier remote results do not validate this later tree.

The repair/aggregate checkpoint `1749593` passed both exact-head remote runs: [push 45569570359](https://github.com/dmbs335/rewb-formal/actions/runs/45569570359) and [PR 45569579422](https://github.com/dmbs335/rewb-formal/actions/runs/45569579422). The retained-anchor/current-bank/boundary-cache/short-outer continuation adds 52 modules and 207 principal reports. Its complete local gate passed 584 build targets and all 1,678 principal reports, using only the permitted standard axioms. Runtime evidence combines that successful 64-audit checkpoint with five completed new audits, for 69 total. The independent nine Python audits are unchanged. The complete matcher target remains open.

That retained-bank checkpoint `40d7be9` passed both exact-head remote runs: [push 45575095492](https://github.com/dmbs335/rewb-formal/actions/runs/45575095492) and [PR 45575104815](https://github.com/dmbs335/rewb-formal/actions/runs/45575104815), including the Lean and nine-test Python jobs. The current complete-query/report/repair/coverage continuation adds 45 modules and 234 principal reports. Its full local gate passed 629 targets and all 1,912 principal reports, using only `propext`, `Quot.sound` and `Classical.choice` where required. Nine new compiled-path audits completed; combined with the successful unchanged 69-audit checkpoint, this gives 78 completed probes. The broader interrupted executor diagnostic is excluded. These results do not establish the still-open whole-matcher time theorem.

The complete-query checkpoint `93a67c3` passed both exact-head workflows: [PR](https://github.com/dmbs335/rewb-formal/actions/runs/45581247435) and [push](https://github.com/dmbs335/rewb-formal/actions/runs/45581232898). The actual-matcher continuation adds 65 modules and 431 principal reports, including whole-plan correctness/cost, unconditional row producers, cached residual execution, all-six-form source correctness, the returned-ledger target, finite construction refinements and the public generated-code fix. Its complete local gate passed 694 targets and all 2,343 principal dependency reports: 2,295 use only the permitted standard axioms and 48 use none. The generated-code route regression also passed; the exact publication tree is recorded in the PR. Five new compiled probes completed with zero mismatches, giving 83 when combined with the unchanged successful prefix. The masked all-start probe was rerun after the compiler fix, preserving both answers and the four tested cost bounds. Broader timed-out diagnostics are excluded.

The previous run-coverage work in PR #13 passed remote CI and was merged. The original three-commit continuation was published in [PR #14](https://github.com/dmbs335/rewb-formal/pull/14) through the connected GitHub API. Its three file trees exactly match the original local commits; the publication metadata changed their commit IDs to `59c6403`, `971c238`, and `d3ef34a`. The last passed both remote jobs in [run 45531815252](https://github.com/dmbs335/rewb-formal/actions/runs/45531815252). Later additions require their own checks; the evidence logs and Git history identify the current local checkpoint.

Interpreted execution probes, repaired stack/candidate-growth defects, and practical limits are recorded separately in [RUNTIME_LIMITS.md](RUNTIME_LIMITS.md). In particular, the kernel-verified isolated-source regression must not be mistaken for a completed run of the full large P1 formula.
