# Masked-index continuation: verified machinery and proposed construction

Updated 2026-11-25. This note preserves the next algorithmic direction. The full masked all-start index and the headline matcher running-time theorem are **not proved**. The proposed cluster implementation below has not yet been connected to an executable suffix-tree traversal.

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

These are event counts, not the runtime of the ordered-list reference. List-length reads, insertion scans, log copying, a fast queue and cancellation machinery still need accounting. A unary-chain regression proves that rebuilding all current adjacencies at every level creates exactly `N*(N-1)/2` records: 4,950 rebuild records versus 99 persistent adjacencies for `N=100`.

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

At creation or a reset, choose `H_i=L`. The existing dense-gap and separated-cluster geometry is relevant to proving the certificates at such a reset. The following update policy is a **candidate**, not yet a checked algorithm:

- When a current overlap mode changes during shortening, reset its predecessor anchor and rebuild the affected incoming/outgoing matrix summaries.
- When an occurrence is inserted, or clusters merge or split, reset edited clusters and a constant-radius neighborhood.
- Radius two is necessary in the proposed layout: inserting a boundary after a singleton can invalidate that singleton's predecessor cursor, even if the predecessor/singleton adjacency itself did not move.
- Density splits can affect an entire progression; charge their occurrence-level rebuilding separately as described below.

Unchanged boundary endpoints preserve their old certificates. An anchor reset changes the tail map and local matrices, but does not itself change occurrence positions. A proof that this update policy always suffices, including simultaneous events and all singleton/end-of-text cases, remains open. The current Lean files prove the algebra used after such certificates are available, not these certificates themselves.

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

For interval reporting, a further proposed finite component records whether the source jump is enabled. Whole clusters outside a requested source interval use the disabled component; whole clusters inside use the enabled component. At most two boundary clusters need partial source-mask queries. Their matrices and the prefix/interior/suffix products must then be composed in chronological order. General interval products and this query compiler are not yet implemented by the new prefix-query tree alone.

## 5. Charging density resets by primitive-square occurrences

When a dense progression of gap `q` ceases to be dense as length falls below `2*q`, its current length-`2*q` prefix is the relevant square. The intended argument is that this square has least period `q`: a smaller period of that prefix would extend through the anchored `q`-periodic word and contradict minimality.

Charge rebuilding an occurrence to `(start,q)`, a primitive-square occurrence. If each occurrence's represented length decreases along its suffix-tree ancestry and already-crossed thresholds are never rescheduled, a given `(start,q)` should be charged only once. `RunBudget.primitive_budget` already bounds duplicate-free lists of such occurrences by `2*n*(log2 n+1)`.

Two bridges remain to be proved: the square/minimum-period certificate for every reset, and injectivity of these reset charges in the actual suffix-tree/event execution. The existing primitive-square theorem supplies a budget only after these bridges; it does not justify arbitrary resets or repeated reconstruction.

## 6. Proposed within-run arbitrary-mask queries without q-squared preprocessing

The same-cluster periodic branch in the audit considers source lengths `a*q+rho`, with `a>=2`, and targets at `s+k*q`. For fixed source phase, `rho` influences the acceptance conditions through a finite tuple of DFA maps, together with the cases `rho=0`, `rho>0`, and `rho<=eta`, where

```
N = floor((R-s)/q),  eta = (R-s) mod q.
```

The numerical bounds on `a,k` then use these flags, rather than the exact positive value of `rho`. The tuples must remain joint tuples arising from **one** cut; independently combining their components would be unsound.

### One-cut map tuples

The proposed preprocessing uses a fixed-state automaton that nondeterministically chooses one cut in a period word and records the required prefix and suffix transformations. Build finite relation range products over a doubled period word. Each of the `q` rotations is one length-`q` interval, so its attainable tuple set can be obtained in pattern-constant times logarithmic query work, without scanning all `q` cuts separately for every rotation.

For the `rho<=eta` cases, allow the cut only before the `eta` boundary, stop the appropriate E transformation at that boundary, and continue the C transformation to the period end. This can use a constant number of finite relation products for the before/after portions. Since `eta` is determined by source phase, there are only `q` such constrained windows per run, rather than `q^2` independent phase/cut pairs.

The intended preprocessing is `O_P(q polylog n)`. The automaton, tuple coverage and the exact relation to every audited periodic case are not yet formalized.

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

using zero before the run's beginning. Aligned endpoint counts answer existence in the required progression by subtraction. The source phase and residue choose the physical class; the data structure does not enumerate all phase pairs. Exact rounding, boundary conventions, empty intervals, the projected formula and the finite-array implementation remain to be checked.

### Safe total-span budget and the discovery obligation

For this branch, both disjoint equal copies have length at least `2*q`, so their containing run has length at least `4*q`. Such runs are cubic. For a cubic run, its length is at most three times the verified primitive-square mass. Consequently, summing their spans can use the existing `O(n log n)` mass budget. The sum of lengths of arbitrary low-exponent runs cannot be used this way and can be quadratic.

This budget is valid **once the relevant runs have been found**. It does not construct a fast enumeration. The current `RankIndexSchedule` sampled all-period generator costs `O(n^2/s polylog n)`; at `s=1` it is quadratic. It therefore does not by itself supply near-linear full-run discovery for an index rebuilt per grid boundary. Discovery must instead be charged to the cluster/event traversal or supplied by a separately verified fast all-run construction.

One possible charged discovery route is to extend surviving fresh dense adjacencies. For a relevant neighboring pair at starts `p,p+q`, the current pattern length is at least `2*q`. Their suffix-tree LCA has depth at least that length. At the first completed merge where both leaves coexist, its occurrence set is a subset of the later complete set, so no occurrence lies between this pair there either. The pair is newly adjacent and dense. Dense-consecutive geometry would identify `q` as the least period, and LCE/LCS extension would find its maximal run. The existing adjacency-generation bound could then pay for extension queries and exact `(lo,hi,q)` deduplication before applying the cubic-span budget.

There is a necessary restriction: **temporary adjacencies during a partial merge are not enough**. An omitted light-child occurrence may lie between a temporary pair, whose gap can be a multiple of the true minimum period. Finish the suffix-node merge, cancel obsolete generations and test only surviving adjacencies in the complete occurrence set. Similarly, matrix invariants can be temporarily dirty during a batch insertion; no query is justified until affected clusters have been repaired. The suffix-tree/LCA coverage theorem, surviving-generation bookkeeping, exact extension/deduplication and dirty-set repair bound are all still unproved. This route is a proposal for replacing a separate all-run construction, not an implemented discovery theorem.

## 7. Required next proof interfaces

1. Exact variable-anchor cluster transfer matrices, including terminal marks, singleton clusters, chronological ordering and both cursor modes.
2. A concrete suffix-tree/occurrence-set traversal maintaining the proposed local certificates, with no rescheduling of already-crossed thresholds.
3. The primitive-square injection for density-reset rebuilding and an efficient discovery route for relevant periodic runs.
4. Rank/residue queries for arbitrary source and target masks inside progression clusters, including split/merge origin changes.
5. The one-cut finite automaton compiler and complete projected target-index formulas.
6. A costed connection from actual local edits, range queries and matrix construction to the verified finite-action tree operations.
7. Complete all-start output/query correctness and the total operation ledger.

The finite-action machinery removes one concrete obstruction—global shortening no longer needs to update every matrix individually. It leaves the geometry, leaf/query compiler and complete data-structure execution to be proved.
