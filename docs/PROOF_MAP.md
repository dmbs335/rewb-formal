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

## 7. Remaining obligations for the headline exponent

1. **Masked all-start index.** Construct the actual arbitrary-mask algorithm, including dense-cluster maintenance, shortening, relabeling, threshold updates and reporting every output start. The audit enumerates lengths and occurrences; it does not implement the claimed amortized data structure.
2. **Boundary-aware range index.** Construct and verify the claimed soft-O(n^2/s) preprocessing and soft-O(s^2) queries, including persistent colored-position structures, path aggregation, depth cutoffs and all boundary cases.
3. **Global dispatch.** Cover short captures, separated equality regions, long gaps, low-exponent regions and large-period cubic runs. Combine their geometric coverage with actual generated queries and an efficient all-period equality/run index. The bounded-period enumerator above covers only one branch.
4. **Unified deterministic cost model.** Sum all preparation and execution work, account for omitted fixed-shape assembly operations, specify word width and memory operations, and connect the verified integer-rounded ledger to those actual costs. An unconstrained supplied cost function cannot witness this goal.

The remaining masked-index amortization needs more than a bound on successful outputs. The supplied target mask must remain immutable; reported source starts are removed from a separate unresolved-source set. In `aaaa` with a one-character capture, unrestricted gap/suffix languages and target mask `{3}`, the same target occurrence witnesses starts 0, 1 and 2. Removing that target after the first report would lose valid outputs. Removing only sources avoids this specific defect, but unsuccessful searches, structural repairs and recreated threshold events still need a charged bound.

The current audit tests shortening only when occurrence sets, clusters and overlap modes stay unchanged. A real data structure must schedule the changes. Similarly, boundary-index color maps need to support noninjective transitions, persistent coalesced color classes, newly admissible endpoints and partial heavy-path edges. DFA transitions cannot generally be inverted to recover an earlier version. These are missing algorithmic invariants and operation counts; no counterexample to the overall proposed exponent is asserted.

The conditional phase ledger is

```
n^2/s + n*L^2 + n^2*s^2/L + n^2*s^2/D0 + n^2*s^2/Q
  + n*D0*s^2 + n*s^2 + n*Q^k.
```

P1 uses k=3, s=n^(1/10), Q=n^(3/10); P2 uses k=4, s=n^(1/13), Q=n^(3/13); both use L=D0=n^(1/3). `Cost.lean` checks the scaled exponents. `ThresholdBudget` now handles integer rounding for every n: let k=floor(log2(n+2)/39)+1 and t=2^k; choose s=t³, Q=t⁹ and L=D0=t¹³. The explicit ledger, with each quotient rounded upward, is at most 12*t^75. Its thirteenth power is at most `12^13*(2^39)^25*(n+2)^25`.

Accordingly, `ThresholdBudget.ledger_target` proves `Spec.Target25Over13` for that **explicit numeric ledger**. It does not prove that any complete REWB matcher incurs the ledger. The matcher-cost instance of the target remains open until the missing index/dispatch bounds and machine accounting are supplied.

## 8. Verification and publication

Use `bash scripts/check.sh` and `bash scripts/audit.sh`. The former checks the complete import closure and principal axiom reports; the latter runs nine independent finite Python audits. No proof placeholders, custom assumptions or native-evaluation proof shortcuts are permitted.

The previous run-coverage work in PR #13 passed remote CI and was merged. New continuation work is being verified locally; successful older CI is not evidence of remote validation of these new files. See the current build/audit logs and Git history for the exact local checkpoint.

Interpreted execution probes, repaired stack/candidate-growth defects, and practical limits are recorded separately in [RUNTIME_LIMITS.md](RUNTIME_LIMITS.md). In particular, the kernel-verified isolated-source regression must not be mistaken for a completed run of the full large P1 formula.
