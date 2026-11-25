# Masked-index continuation: verified machinery and proposed construction

Updated 2026-11-25. This note preserves the next algorithmic direction. The full masked all-start index and the headline matcher running-time theorem are **not proved**. The actual complete geometric suffix-trie traversal is implemented; its changing-partition bank repair, aggregate query and reporting integration remains open.

Continuation update: descriptor-only compressed trie construction and complete first-threshold loci are now implemented in `BoundaryTrie*`; `MaskedRunDiscovery*` connects actual suffix loci, surviving dense pairs, indexed extension and true minimum-period cubic runs. `MaskedProgression*` implements the arbitrary-mask AP array, and `MaskedCut*` implements shared-cut transformation tuples and one doubled-period index for all rotations. `MaskedFiniteActionRange` adds general ordered interval products. The remaining cluster geometry, update policy and complete event execution below are still proposals unless a specific checked theorem is named.

Current execution update: `MaskedCluster` now compiles source-filtered normal/overshoot cursor blocks and complete replay banks, and `MaskedCluster.Cut` enforces a single shared B/C/E length. `MaskedMutableProgression.Batch` implements actual arbitrary source deletions through one-shot reverse run addresses; `MaskedCluster.Mutable.Batch` compiles banks directly from those current run/global snapshots. `MaskedClusterLeaders.execute` maintains exact dense-component starts with a verified live-event coverage invariant. `MaskedEmpty.SourceBatch.start` reports all zero-length witnesses and removes exactly those sources before positive-length processing. These additions close local operations and initialization; the actual suffix-class traversal, local bank ownership/repair and aggregate event-query execution still require integration.

Latest integration: `MaskedSuffixClass.query_complete` now supplies complete occurrence classes from the actual first-threshold lookup. `MaskedCluster.Mutable.Store` owns fixed-partition banks and repairs precisely one affected slot after source deletion, preserving every other slot and all targets. `MaskedTraversalEdge` executes the real descending queue and emits uniquely covering stable length bands, including parent-depth ordering and zero-length refinement gates. `MaskedTraversalDriver` now executes the global small-to-large schedule, proves child-before-parent threshold ordering, and gives complete, unique positive start/length coverage. Its cost includes actual imports, pops and discarded queues. The changing-partition anchor policy, finite-action aggregate and actual charged repair records still need connection. These completed components remove the corresponding input oracles; they do not turn the proposal below into a finished all-start index.

Current bank and charging update: `MaskedRunCatalog` reuses the actual batch run array, builds exact direct IDs and immutable target counts once, and proves complete descriptor-to-ID discovery. `MaskedTraversalBankReady` now creates real dense/singleton banks with actual predecessor-derived incoming cursors and current source histories; its semantic theorem uses `H=L` and explicit retained-neighbor anchor bounds. `MaskedTraversalBandUnique` proves actual band disjointness and the global primitive-square budget from local one-shot emission plus `DensityAt` attribution. Neither result supplies the missing dirty-set completeness or global repair invariant. Successor incoming-context refresh must retain its existing anchor and run metadata instead of starting an uncharged reset cascade.

Actual repair and query update: `MaskedTraversalDirty` derives requests from real import patches and live records; `MaskedTraversalRepair` resets selected anchors first and then rebuilds actual banks. `MaskedTraversalContext.incoming_unchanged` proves only reset successors need incoming-context refresh, with no anchor-reset cascade. `store_current` handles retained anchors and original source-mask-minus-history semantics. `MaskedTraversalAggregate` now supplies the actual persistent product, common-length band query and two-boundary source-window clipping, with exact matrix-chain semantics and physical soundness under explicit local invariants. Its runtime audit includes windows cutting within dense clusters. `MaskedTraversalNeighbor` now proves descriptor locality and pending anchor-bound preservation for actual insertion, live-threshold and import/merge operations. Whole-traversal retained H-word/overlap certificates, bank coherence, cross-cluster completeness and reporter execution remain to be derived.

The residual side now has an exact actual schedule dispatcher, an assembled one-use cache conditional only on its finite all-start rows, and a concrete short-outer table with exact equality/G/H semantics and an `O_P(nL²+nL log n+n log n)` bound. Those finite inputs and the nested joins still require actual production constructors; the following proposed global index is not yet replaced by a complete matcher time theorem.

## 1. What is now verified

`MaskedReporting` implements balanced output extraction from a measured interval-existence query. For height `h` and `k` outputs, it makes at most `1+2*h*k` queries, counting negative queries too. Output concatenation copies at most `h*k` cells. Query work remains a separate counter; with an independently verified per-query cost `A`, the combined bound is `(A+1)+(2*A+3)*h*k`. A cached output count avoids repeated length traversals merely to compute that counter.

The adapter to `Spec.maskedStart` includes the terminal boundary. Only the unresolved source mask is cleared. The target mask remains immutable. The checked `aaaa` regression has target `{3}` and source outputs `{0,1,2}`: deleting the target after reporting one source would lose the other outputs. `MeasuredMaskQuery` supplies an actual, deliberately slow array-scan instance of the query interface.

`MaskedEventBudget` implements a destructive bottom-up merge-tree schedule using ordered-list insertion as a reference. The smaller child's entries are inserted into the larger child's set. It proves:

- At most `N*log2 N` transferred entries.
- At most two new adjacency generations per insertion, using an exact local edge-replacement certificate.
- Explicit retirement of both broken destination adjacencies and the absorbed light child's live adjacencies.
- Conservation: fresh generations equal final live edges plus retired generations.
- At most `2*N*log2 N` fresh adjacency generations and `4*N*log2 N` density/overlap threshold records.
- A one-shot processing bound when processed and pending entries are a permutation of the original records. This includes stale entries, but excludes implementations that recreate old records.

These are event counts, not the runtime of the ordered-list reference. The newer sparse `MaskedOrdered` implementation, threshold queue and current-adjacency validation now account for their corresponding operations without list insertion scans or old-log copying. Their complete traversal integration is still necessary. A unary-chain regression proves that rebuilding all current adjacencies at every level creates exactly `N*(N-1)/2` records: 4,950 rebuild records versus 99 persistent adjacencies for `N=100`.

`MaskedFiniteAction`, `MaskedFiniteActionTree` and `MaskedFiniteActionMaps` add a different verified component:

- Materialized finite vectors of Boolean transition matrices.
- Pointwise matrix multiplication and noninjective vector reindexing.
- A balanced position tree with cached products, materialized lazy maps, global root reindexing, prefix products and point replacement.
- Exact semantics and explicit modeled work bounds for these operations.
- Correct composition order for precomposition, and preservation of a newly replaced cell from older lazy actions.
- An explicit enumeration of all materialized maps on `m` states, with exactly `m^m` entries and a proved encode/decode round trip.
- Algebraic composition of the transformations induced by word slices under shortening.

The map universe depends only on fixed automata. It does not enumerate text positions, periods or phases. Its preprocessing and the text range queries that select shortening maps are not yet included in the action-tree counters. The regression uses a noninjective map and a noncommuting second map, then replaces one leaf; it checks both tag order and the treatment of fresh cells.

## 2. Why a single global anchor is insufficiently justified

The existing Python cross-cluster audit uses a common anchor length `H`. The current selected copy has length `L<=H`; skipping its anchored length and reading the tail `X[L:H]` simulates skipping only the actual copy. The audit checks only families where occurrence sets, dense clusters and overlap modes stay unchanged.

Within such a family, dependence on `L` enters through finitely many DFA transformations of that tail. Tabulating a matrix for every transformation therefore handles shortening without inspecting every occurrence.

At a geometry change, resetting a **global** `H` would move every anchored endpoint. A proof that only the locally changed adjacency requires repair does not follow. Noninvertible DFA transformations also prevent recovering all shorter tail maps by cancelling a common suffix. This motivates local anchors.

## 3. Proposed local-anchor invariant

Maintain the full occurrence set of the current pattern, independently of both masks. A source reported earlier remains an occurrence and can still be a target. Partition occurrences into maximal dense clusters, where neighboring starts at distance `g` are dense when `2*g<=L`.

For cluster `i`, let its first and last starts be `s_i,t_i`. A nonsingleton cluster is an arithmetic progression of minimum-period step `q_i`. Give the cluster an anchor length `H_i` with the following proposed certificates:

1. `L<=H_i`, and every occurrence in this cluster has the same length-`H_i` anchored word. All anchored copies are in bounds. Different clusters may have different extensions beyond the current common prefix.
2. At a boundary to the next cluster, `t_i+H_i` overlaps the next first start exactly when `t_i+L` does.
3. If the predecessor cluster has a penultimate occurrence, that occurrence's anchored endpoint is at or before the next first start. Only the last occurrence can overshoot that boundary.
4. The last anchored endpoint reaches no farther than the next cluster's second occurrence, when that cluster has one. If the next cluster is a singleton, it reaches no farther than the following cluster boundary, or the end of text.

Conditions 3 and 4 justify the audit's two cursor modes: either the cursor is at the next first occurrence, or it lies just after a preceding anchored jump and skips at most that first occurrence. In particular, the no-jump transition must never attempt to read a reversed interval.

At creation or a reset, choose `H_i=L`. `MaskedLocalAnchor.reset` and `reset_terminal` now derive the word/bounds, overlap and both cursor certificates from complete unmasked occurrence classes. The following-position proof handles either a dense next cluster or a singleton followed by another sparse boundary. `shorten` retains the certificate for fixed neighbors and unchanged overlap mode. The following update policy is a **candidate**, not yet a checked algorithm:

- When a current overlap mode changes during shortening, reset its predecessor anchor and rebuild the affected incoming/outgoing matrix summaries.
- When an occurrence is inserted, or clusters merge or split, reset edited clusters and a constant-radius neighborhood.
- Radius two is necessary in the proposed layout: inserting a boundary after a singleton can invalidate that singleton's predecessor cursor, even if the predecessor/singleton adjacency itself did not move.
- Density splits can affect an entire progression; charge their occurrence-level rebuilding separately as described below.

Unchanged boundary endpoints preserve their old certificates. An anchor reset changes the tail map and local matrices, but does not itself change occurrence positions. A proof that this update policy always suffices, including simultaneous events and all singleton/end-of-text cases, remains open. The Lean files now prove the certificates at reset and their unchanged-mode preservation; they do not yet implement the full repair policy.

## 4. Finite-vector shortening with different local tails

For a cluster with current tail `Y_i`, shortening from `L` to `L'<L` prepends the same word `Z` to every local tail:

```
Y_i' = Z ++ Y_i.
```

The old tails can differ between clusters. Only the newly exposed part of the common current pattern must agree.

Use the word-map convention

```
mul a b = b composed with a
tau(u ++ v) = mul (tau u) (tau v).
```

Let a leaf vector `F_i(T)` describe its matrix after an additional prefix having map `T`. After prepending `Z`, its new vector is

```
F_i'(T) = F_i(mul T (tau Z)).
```

This is precomposition on a fixed finite vector. Applying reindex map `f` and then `g` yields `old(f(g(index)))`. It is **not** existential-image color merging. Noninjective maps are allowed because no inverse is used.

Pointwise matrix multiplication commutes with reindexing. A cached aggregate vector can therefore receive a global shortening action at its root. On a local reset, push older tags to old children, replace the leaf with a freshly tabulated vector at the current length, and rebuild the path. This mechanism is implemented and proved in `MaskedFiniteActionTree`.

A static position tree can place each cluster's matrix at its first text position and use identity vectors at nonleaders. This would avoid needing a separately balanced dynamic sequence of clusters. Connecting actual cluster edits to those point updates is still an obligation.

For interval reporting, the implemented bank now records whether the source jump is enabled. Whole clusters outside a requested source interval can use the disabled component; whole clusters inside can use the enabled component. At most two boundary clusters need partial source-mask queries. The actual local compilers and chronological block products are verified, including nonperiodic singletons and target uses outside the source window. General interval products are implemented by `MaskedFiniteActionRange`, with at most two boundary paths and exact lazy-map semantics. Selecting the correct complete cluster sequence and maintaining its stored banks remain application work.

## 5. Charging density resets by primitive-square occurrences

When a dense progression of gap `q` ceases to be dense as length falls below `2*q`, its current length-`2*q` prefix is the relevant square. The intended argument is that this square has least period `q`: a smaller period of that prefix would extend through the anchored `q`-periodic word and contradict minimality.

Charge rebuilding an occurrence to `(start,q)`, a primitive-square occurrence. If each occurrence's represented length decreases along its suffix-tree ancestry and already-crossed thresholds are never rescheduled, a given `(start,q)` should be charged only once. `RunBudget.primitive_budget` already bounds duplicate-free lists of such occurrences by `2*n*(log2 n+1)`.

`MaskedLocalAnchor.reset_square` now proves the square/minimum-period certificate at every occurrence of the complete class. Injectivity of these reset charges in the actual suffix-tree/event execution remains to be proved. The existing primitive-square theorem supplies a budget only after these bridges; it does not justify arbitrary resets or repeated reconstruction.

## 6. Proposed within-run arbitrary-mask queries without q-squared preprocessing

The same-cluster periodic branch in the audit considers source lengths `a*q+rho`, with `a>=2`, and targets at `s+k*q`. For fixed source phase, `rho` influences the acceptance conditions through a finite tuple of DFA maps, together with the cases `rho=0`, `rho>0`, and `rho<=eta`, where

```
N = floor((R-s)/q),  eta = (R-s) mod q.
```

The numerical bounds on `a,k` then use these flags, rather than the exact positive value of `rho`. The tuples must remain joint tuples arising from **one** cut; independently combining their components would be unsound.

### One-cut map tuples

The implemented preprocessing uses `MaskedCut`'s finite-monoid cut summary. Its associative product retains prefix and suffix transformations from one common cut and materializes the finite relation after every multiplication. Each of the `q` rotations is one length-`q` interval in a shared doubled-period index, so its attainable tuple set is obtained with pattern-constant table work and logarithmic hierarchy visits, without scanning all `q` cuts separately for every rotation.

For the `rho<=eta` cases, allow the cut only before the `eta` boundary, stop the appropriate E transformation at that boundary, and continue the C transformation to the period end. This can use a constant number of finite relation products for the before/after portions. Since `eta` is determined by source phase, there are only `q` such constrained windows per run, rather than `q^2` independent phase/cut pairs.

`MaskedCutRotations.batch` now constructs that shared index and all q outputs. It counts `(log2(2q)+1)*2q` preparation products, at most `3q` query products and `3q*(log2(2q)+2)` visits. `MaskedCutTuples.queryConstrained_correct` proves exact B-prefix/C-full-suffix/E-short-suffix coverage with a common cut; the common C tail is read from a fourth range query. A lower cut bound of one excludes rho=0, even when a positive cut produces identity transformations. Empty positive windows return no tuples. Connecting these outputs to every periodic acceptance formula and its complete cost ledger is the remaining application step.

### Masked target progression queries

After selecting a realizable tuple, finite-orbit conditions and integer projection should leave a pattern-constant union of interval/residue constraints on `k`. Let `K` be a pattern-only common modulus. A target constraint

```
j = s+k*q,  lo<=k<=hi,  k mod K = r
```

is an interval query in one physical residue class modulo `K*q`. The arbitrary target mask need not be periodic.

For one run, scan its positions once and build stepped prefix counts

```
count[j] = mask[j] + count[j-K*q],
```

using zero before the run's beginning. `MaskedProgression*` implements this finite array and proves exact clipped AP/residue existence, including empty intervals and inclusive upper bounds. Construction costs at most `13*len` tracked operations, with no residue loop; each query uses at most two array reads and 37 scalar operations. Counts are at most len. The projected formula and integration of per-run preparation into the full index still need their application ledger.

### Safe total-span budget and the discovery obligation

For this branch, both disjoint equal copies have length at least `2*q`, so their containing run has length at least `4*q`. Such runs are cubic. For a cubic run, its length is at most three times the verified primitive-square mass. Consequently, summing their spans can use the existing `O(n log n)` mass budget. The sum of lengths of arbitrary low-exponent runs cannot be used this way and can be quadratic.

This budget is valid **once the relevant runs have been found**. It does not construct a fast enumeration. The current `RankIndexSchedule` sampled all-period generator costs `O(n^2/s polylog n)`; at `s=1` it is quadratic. It therefore does not by itself supply near-linear full-run discovery for an index rebuilt per grid boundary. Discovery must instead be charged to the cluster/event traversal or supplied by a separately verified fast all-run construction.

One possible charged discovery route is to extend surviving fresh dense adjacencies. For a relevant neighboring pair at starts `p,p+q`, the current pattern length is at least `2*q`. Their suffix-tree LCA has depth at least that length. At the first completed merge where both leaves coexist, its occurrence set is a subset of the later complete set, so no occurrence lies between this pair there either. The pair is newly adjacent and dense. Dense-consecutive geometry would identify `q` as the least period, and LCE/LCS extension would find its maximal run. The existing adjacency-generation bound could then pay for extension queries and exact `(lo,hi,q)` deduplication before applying the cubic-span budget.

There is a necessary restriction: **temporary adjacencies during a partial merge are not enough**. An omitted light-child occurrence may lie between a temporary pair, whose gap can be a multiple of the true minimum period. Finish the complete prefix-class merge, cancel obsolete generations and test only surviving adjacencies. Binary trie refinements at equal depth are not separate complete classes. `BoundaryTrieLocus` selects the first threshold ancestor; `MaskedRunDiscoveryLocus` derives exact occurrence completeness from the actual n+1-suffix trie. `MaskedRunDiscoveryEvents` proves first-coexistence and actual fresh-generation provenance, and `MaskedRunDiscovery` performs/proves the two-query minimum-period cubic extension. Equal-depth gates and temporary nonminimal gaps have explicit regressions.

These local construction/coverage bridges are now checked. The full traversal that chooses all required loci, cancels records, invokes discovery once per surviving generation, deduplicates runs and repairs dirty cluster summaries is still needed. In particular, no matrix query is justified while a batch insertion leaves the local anchor certificates dirty.

## 7. Required next proof interfaces

1. Exact variable-anchor cluster transfer matrices, including terminal marks, singleton clusters, chronological ordering and both cursor modes.
2. A concrete suffix-tree/occurrence-set traversal maintaining the proposed local certificates, with no rescheduling of already-crossed thresholds.
3. The primitive-square injection for density-reset rebuilding and an efficient discovery route for relevant periodic runs.
4. Connect the verified arbitrary-mask AP arrays to progression clusters and their split/merge origin changes.
5. Connect the verified shared-cut tuple index to complete projected target-index formulas and their aggregate ledger.
6. A costed connection from actual local edits, range queries and matrix construction to the verified finite-action tree operations.
7. Complete all-start output/query correctness and the total operation ledger.

The finite-action machinery removes one concrete obstruction—global shortening no longer needs to update every matrix individually. It leaves the geometry, leaf/query compiler and complete data-structure execution to be proved.

## 8. Newly connected execution layers

`BoundaryApplication` builds real fixed-end source/target descriptors, range maps, mixed programs and all persistent node snapshots. Its local right-boundary query is exact; raw-path lookup is charged explicitly. Heavy-path subset versions, cached source addresses and exact source-route jumps are now implemented in Heavy/Address/Jump/Locate; Coverage.query_iff_cuts closes full fixed-end source/target semantics with only endpoint assumptions. Fixed-start and boundaryRange assembly remain separate.

`MaskedPeriodic.phaseQuery_correct` uses the actual shared cut/range index, cached LCM modulus and immutable-mask AP array for its three word-family cases. `MaskedPeriodic.Text.query_full_run_correct` now supplies the real periodic-text and full-input suffix transport, including equal copies and arbitrary source phases. Complete compiler-construction accounting remains open.

`MaskedOrdered` replaces list scans with sparse persistent position trees and cached-count light imports. Fresh and retired records are emitted and counted by the executable schedule, with exact edge balance and O(N log N * h) tracked work. Owner.enumerateAuto now performs complete-owner validation, actual indexed extension and exact deduplication, and returns exactly all cubic runs within a closed O_sigma(n log^2 n) tracked bound. `MaskedRunCoverage.actual_suffix_coverage` provides the corresponding global cubic-run coverage certificate at actual LCA depths, and `MaskedRunTrieBridge` constructs the exact distinct-position merge schedule from the real suffix trie.

`MaskedClusterStage` now constructs the finite waiting/C/E DFA and marked jump vectors. Local representative-tail replay is proved equal to the real current-copy skip, and two jumps mean exactly a marked source, accepting C gap, marked target and accepting E suffix. MaskedCluster now compiles real dense/singleton one-jump cells and materialized matrices, deriving dense periodicity from the local-anchor certificate. Source-only clipping, zero-jump/two-cursor block assembly and dynamic event repair are the next connections.

`MaskedPeriodic.Batch.solve` now supplies the whole within-run all-start branch: real run enumeration, shared cut index, per-run immutable target-mask arrays, eligible source scans and exact output union. The total scanned span is at most 6*n*(log2 n+1); its work theorem preserves the existing finite-compiler exclusions. This covers the long-capture within-run witness class, not every masked match.

## 9. Current source and event invariants

The source eligibility index is now physically mutable through persistent sparse erasure. Its original input mask is arbitrary. `MaskedMutableProgression.Batch.Current source history p` means the original bit is true and p does not occur in the actual deletion history. Every run row and the global singleton row satisfy this same predicate. The complete occurrence set is not filtered, and the immutable target counts continue to admit reported sources as targets.

Reverse run addresses are built once by `MaskedSourceFanout.prepare` from the actual enumerated cubic runs. Taking a row clears it, so each source/run membership is delivered once. The total delivery budget is `6*n*(log2 n+1)`, even with repeated requests. Actual per-row sparse updates and one global membership update are counted by the Batch loop. This proves source-index maintenance, not automatic repair of already-cached finite banks.

The mutable bank compiler reads the current persistent source index directly. Its theorem-only snapshot mask is not materialized in the executable path. The run adapter retrieves the actual run's q and index by ID and checks the fixed pattern modulus. Targets stay immutable. Every explicit rebuilt bank has exact physical cursor semantics and the proved common-prefix reindexing law. An old persistent bank still represents its old source snapshot; its own regression makes this distinction observable.

The leader state now retains actual occurrence and leader trees plus the threshold queue. `Invariant L state` gives exact full-set component starts. `Future L state` ensures that every adjacency record still needed below L is in the actual queue. One inserted occurrence affects only its own leader status and its strict successor. Every new leader caused by lowering L has a live density record returned by the real drain. The guarded operation stream preserves these invariants with a linear bound in the number of operations times tree height.

This local stream does not authorize moving queries across a merge. Queries and threshold events on a compressed suffix edge must be processed before merging the lower endpoint's extra occurrences. A pair that becomes stale after that merge may have been needed for an intervening query. Equal-depth refinement nodes also remain partial classes for periodic geometry, even though their leader sets are well-defined.

Length zero is now separate. The actual backwards empty-capture scan reports every accepted boundary, including n, and `SourceBatch.start` applies those exact deletions. `start_partition` leaves only live positive-capture witnesses. Positive cluster code can therefore require L>0 and derive a real last-start-before-n bound; inventing a terminal position n+1 is unnecessary.

`MaskedClusterDescriptor.describe` now supplies the actual local descriptor by membership and a constant number of cached neighbor queries. `describe_geometry` derives the AP extent and `H=L` reset certificate from an entire unmasked class. The locator is defined exactly on real occurrences, so a deleted source that lies geometrically inside a dense AP hull but is not an occurrence cannot be treated as a cluster member. Such positions also must not spuriously invalidate a stored bank. Attaching the complete class to an actual compressed suffix-trie locus remains the next input-side connection.
