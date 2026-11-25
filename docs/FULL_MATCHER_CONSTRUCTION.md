# Full matcher construction and accounting

## Verified scope

This note describes the concrete construction path in `REWB.ResidualActual.FullCost`, verified at commit [`8614bf808df5bbb5f73bd629951f01617923fa6c`](https://github.com/dmbs335/rewb-formal/commit/8614bf808df5bbb5f73bd629951f01617923fa6c). The eight refined periodic modules and eight final dispatcher/matcher modules build in Lean 4.19. Their 56 and 70 principal dependency reports, respectively, contain only `propext`, `Classical.choice`, and `Quot.sound`.

Semantic correctness is unconditional for the public matcher. The complexity result concerns its documented, concrete returned operation ledger. It is not an identification of that ledger with Lean VM time, machine-integer bit cost, reference counting, allocation, or garbage collection.

**Composition runtime status:** the original attempt and its identical retry both ended on runner shutdown before their 120-second limits and before fixture output. This does not identify the shutdown cause. The source build and all 70 dependency checks passed. A split, resource-limited audit now separates direct compiled-form dispatch, normalization and independent execution; only completed modes are recorded as successful below.

## Actual execution path

[`ResidualActualFullCostMatcher.lean`](../REWB/ResidualActualFullCostMatcher.lean) normalizes an input expression with `compile`, then `run` executes the resulting finite list of forms. `form` handles all six constructors:

| Form | Actual computation |
| --- | --- |
| `regular` | DFA execution on the text |
| `once` | Full-cost P2 on the proved `oncePattern` reduction |
| `sameValue` | Full-cost P1 on the proved `samePattern` reduction |
| `independent` | Two measured all-start rows, one regular-gap suffix aggregate, and an endpoint scan |
| `nested1` | Full-cost P1 |
| `nested2` | Full-cost P2 |

[`ResidualActualFullCostDispatch.lean`](../REWB/ResidualActualFullCostDispatch.lean) constructs the required finite row bank through `FullCost.P1.inputs` or `FullCost.P2.inputs`. It passes the stored row bits to [`ResidualActualFullCostCached.lean`](../REWB/ResidualActualFullCostCached.lean), which executes the refined periodic branch, short-outer branch, residual schedule, residual cache, and its queries. Row factories and the periodic solver are each called once at their respective call sites. The public path receives no externally supplied row, witness, split, answer, or cost oracle.

The independent branch uses a row for reversed `(B,C,A)` to identify first-copy-pair ends, a forward `(F,G,H)` row to identify second-copy-pair starts, and `D` to join these endpoints. The two captured words remain independent; empty words and empty intervening gaps are included. See [`ResidualActualFullCostIndependent.lean`](../REWB/ResidualActualFullCostIndependent.lean).

The refined periodic path installs actual measured run enumeration, cache/context construction, rotation/short-key construction, formula projection and event preparation, followed by the chronological join. Long and short P1 call `Join.run` once after preparation; the short branch uses its required `N = 0`. Cubic P1 executes both branches. P2 executes the actual phase solver. Old implementations occur as equality targets in proofs, rather than additional runtime executions to recover a comparison answer.

## Exported semantic contracts

The final namespace is `REWB.ResidualActual.FullCost.Matcher`. Principal entry points and theorems are:

- `compile`, `run`, `solve`, and `matchWord`.
- `form_correct`, `run_correct`, `solve_correct`, and `matchWord_correct`.
- `correctMatcher`: `Spec.CorrectMatcher p (matchWord p fallback)`.
- `Cost.solve_charged_bound`, `Cost.solve_target`, `Cost.word_target`, and `Cost.correctMatcher_with_accounting`.

In particular, for every word `w`, the actual result satisfies

```lean
matchWord p fallback w = true ↔ MatchesWithin p w 2
```

The finite alphabet and fallback letter are ordinary executable inputs. The public `fallback : Fin σ` requires a nonempty alphabet; empty input words are included. There is no additional `Ready`, row-generation, all-start-answer, or periodic-answer premise on this public theorem.

Lower wrappers preserve the entire old payload where promised, including the old counters. Their extra component records newly measured construction work. At the final cached dispatcher the periodic work field is replaced by that refined work, while answer equality and residual-counter preservation are proved separately. Some bounds deliberately add a full measured subroutine ledger to an inherited ledger that already counts some of its operations. This is safe overcounting, not a claim that every returned unit is a distinct machine instruction.

## Exact coefficient and charge scope

Put

```text
h(n) = Nat.log2 (n + 2) + 1
b(n) = 2 ^ (Nat.log2 (n + 2) / 39 + 1)
scale(n) = b(n)^75 * h(n)^3.
```

For each fixed source expression `p` and each fixed natural `charge`, `Cost.solve_charged_bound` proves the existence of a coefficient independent of the text and its length such that

```text
solve.accountedWork + charge * solve.fixedPatternBuilds
  ≤ coefficient * scale(n).
```

`charge` accounts for an arbitrary fixed-pattern cost per counted action build. Its value may depend on the fixed pattern, and the resulting coefficient may depend on both the pattern and `charge`. Neither is a text-size-dependent parameter hidden in the theorem. The coefficient is a proof envelope and is not enumerated by the runtime matcher. Finite automaton, map, formula, and normalized-form universes may have very large fixed-pattern constants.

The combined P1/P2 proof in [`ResidualActualFullCostDispatchCost.lean`](../REWB/ResidualActualFullCostDispatchCost.lean) uses the explicit coefficient sum

```text
old periodic-dispatch coefficient(P, charge)
  + 3 * p1Coefficient(P, 0)
  + 3 * p2Coefficient(P, 0)
  + PeriodicActual.FullCost.roundedCoefficient(P).
```

The two zero-charge row coefficients pay for the added actual input construction. The arbitrary action-build charge is retained through equality of the existing build counters. The independent-case coefficient similarly adds the two measured row coefficients to its old charged endpoint/aggregate bound. Finite-form composition adds the actual per-form and per-cons overhead, using a coefficient fixed by the compiled list.

`Cost.wordWork` additionally charges `w.length + 2` for materializing the word array. Pattern normalization is fixed-pattern preparation exposed separately through `compile` and reusable `run`. The convenience `solve` calls `compile`; its returned text ledger does not separately meter the normalizer. The theorem is therefore stated for that ledger, with reusable fixed-pattern compilation distinguished from text processing.

The conversion to `Spec.Target25Over13` is explicit. If the preceding bound uses `coefficient`, the proof may choose

```text
C = (coefficient + 1)^13 * (2^39)^25,   d = 39
```

and proves `work(n)^13 ≤ C * (n+2)^25 * h(n)^d`. This uses `b(n)^39 ≤ 2^39 * (n+2)`. The refined external periodic branches alone have the stronger `rounded_bound` with `h(n)` instead of `h(n)^3`, and `rounded_target` uses logarithmic exponent 13 after taking the thirteenth power.

The ledger retains the stated unit costs for primitive natural-number arithmetic, indexing, DFA transitions and comparisons. In particular, the inherited `Nat.lcm` calls in `ActualModulus` and `CountedProjection` remain primitive arithmetic operations; this layer does not derive their GCD or bit-operation cost. No reference-count, copy-on-write, allocator or garbage-collector complexity is asserted by these target theorems.

## Source and principal-check manifest

| Family | Production files under `REWB/` | Principal checks |
| --- | --- | ---: |
| Refined P2 | `PeriodicActualFullCostP2.lean`, `PeriodicActualFullCostP2Cost.lean` | 14 |
| Refined event/short folds | `PeriodicActualFullCostEvents.lean`, `PeriodicActualFullCostShort.lean` | 8 |
| Refined preparation | `PeriodicActualFullCostPrepare.lean`, `PeriodicActualFullCostPrepareCost.lean` | 14 |
| Refined P1/Cubic and target | `PeriodicActualFullCostBranch.lean`, `PeriodicActualFullCostBranchCost.lean` | 20 |
| Final cached dispatcher | `ResidualActualFullCostCached.lean`, `ResidualActualFullCostDispatch.lean`, `ResidualActualFullCostDispatchCost.lean` | 39 |
| Independent captures | `ResidualActualFullCostIndependent.lean`, `ResidualActualFullCostIndependentCost.lean` | 11 |
| Six-form/source matcher | `ResidualActualFullCostMatcher.lean`, `ResidualActualFullCostMatcherCostBase.lean`, `ResidualActualFullCostMatcherCost.lean` | 20 |

The exact names are listed by the four `audits/periodic_actual_full_cost_*_axioms.lean` files and the three `audits/residual_actual_full_cost_*_axioms.lean` files. The 56 periodic checks passed in jobs [139161245173](https://github.com/dmbs335/rewb-formal/actions/runs/45601488591/job/139161245173), [139161245260](https://github.com/dmbs335/rewb-formal/actions/runs/45601488591/job/139161245260), and [139161245183](https://github.com/dmbs335/rewb-formal/actions/runs/45601488591/job/139161245183). The final 70 checks and 687-target build passed before the runner shutdown in [job 139161245357](https://github.com/dmbs335/rewb-formal/actions/runs/45601488591/job/139161245357).

## Completed runtime checks and observed limits

[`audits/periodic_actual_full_cost_smoke.lean`](../audits/periodic_actual_full_cost_smoke.lean) passed at the verified commit in 50 ms: three non-cubic P1 fixtures, one actual positive period-one P2 fixture, and one empty Cubic fixture, with zero mismatches. It compares complete retained old payloads/counters, checks the positive P2 against literal/reference matching, and reads the actual new counters. The positive P2 fixture returned old work 67,990 and refined work 136,722. It does not evaluate proof-only coefficient families.

The broad positive P1 probe has **not** passed. The observed diagnostics are preserved, rather than counted as regression successes:

| Probe | Observed result |
| --- | --- |
| Original positive P1 pipeline, unary length 3 / period 1 | 300-second timeout |
| Isolated actual positive P2, same size/period | Passed, approximately 30 ms |
| Isolated five-step P1 target projection | Passed, 3,249 ms; clause counts 5, 26, 182, 1,560, 20,176 |
| Long P1 preparation | Completed in about 16 s, four source and four target events, returned preparation work 70,423,799 |
| Long P1 join after that preparation | Did not complete before the 120-second total diagnostic limit |
| Short P1 preparation | Did not complete before its separate 120-second limit |

The isolated long/short evidence comes from [job 139157729908 at commit 917c2d5](https://github.com/dmbs335/rewb-formal/actions/runs/45600471549/job/139157729908). Thus projection alone is not the observed long-branch bottleneck. These timings expose large fixed-pattern constants; they do not substitute for, or invalidate, the separately checked semantic and operation-ledger theorems. The unchanged expensive probes remain available through [`audits/periodic_actual_diagnostic.lean`](../audits/periodic_actual_diagnostic.lean) and the optional workflow path.

[`audits/residual_actual_full_cost_matcher_smoke.lean`](../audits/residual_actual_full_cost_matcher_smoke.lean) is intended to cover regular normalization/list composition on 32 words and one empty independent case using actual reversed/forward full-cost rows. Its initial attempt and identical retry were interrupted by runner shutdown, so those unsplit attempts provide no completed composition fixtures. The split audit retains the original `full` fixture scope, corrects the invalid assumption that normalization has zero action builds, and reports each selected mode separately. The resource wrapper's default `regular` mode checks direct already-constructed form lists; it does not claim normalization or independent execution. The source-level universal six-form theorem, the actual row-factory component tests, and the bounded periodic tests remain distinct pieces of evidence; they are not described as an exhaustive runtime test of every normalized branch.
