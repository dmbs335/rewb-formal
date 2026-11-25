# One-use range cache execution audit

The nine `OneUseRangeReverse`, `FarSelection`, `FarSemantics`, `FarBank`,
`Grid`, `Cache`, `CacheCorrect`, `CacheCost`, and `CacheRegression` modules
construct an eager finite cache and query its two far branches and the
actual midpoint near index. The cache takes two finite vectors of bit
arrays. `Cache.Ready` states that those arrays are the appropriate
all-start answers on actual text prefixes. Producing them by the proposed
fast all-start algorithm remains a separate construction obligation.

`Cache.query_correct` proves the exact original `Spec.oneUseRange`
predicate under that explicit input provenance. `Cache.build_work` and
`Cache.query_work` bound the actual cache counters without requiring
`Ready`. The build bound excludes the input rows' construction; fixed
reverse-DFA compilation is pattern preprocessing. The bound on the
remaining cache construction has an `O_P(n² / width + n log² n)` form,
and the query bound is `O_P(width² log² n)`. These are the existing
fixed-pattern primitive counters, not a bit-complexity or allocator
theorem.

## Confirmed generated-code issue and correction

Before the local refactor, `Cache.Backward.query` passed `w.reverse`
through the phantom word parameter of `FarBank.query`. The generated
`l_REWB_OneUseRange_Cache_Backward_query___rarg` body contained the actual
call `x_8 = l_List_reverse___rarg(x_1);`. Although the eventual selector
ignored the word, evaluating the argument performed an uncharged
linear text traversal on each backward query.

The active implementation introduces word-free `FarSelection.keyCore`
and `FarBank.queryCore`. The public wrappers are definitionally equal to
those cores. `Backward.query` directly passes its cached DFA, bank,
range tree, materialized color table and length to `queryCore`; it has
no word argument. No frozen dependency was changed. This is an
observed call-path correction; no claim about an upstream compiler bug
is made.

After rebuilding with Lean 4.19.0, the generated backward query has four
runtime arguments and ends in:

```c
x_12 = l_REWB_OneUseRange_FarBank_queryCore___rarg(
  x_5, x_7, x_9, x_10, x_11, x_3, x_4);
lean_dec(x_11);
return x_12;
```

The arguments come from cached record fields and one `Table.get`. The
full generated bodies of the following seven functions contain no
reverse-DFA construction, list reverse/length/take/conversion, array
materialization, logarithm/power computation, range-index build, or
color-table build:

| Module | Function | Generated body lines |
| --- | --- | ---: |
| `OneUseRangeFarSelection` | `keyCore` | 59 |
| `OneUseRangeFarSelection` | `key` | 13 |
| `OneUseRangeFarBank` | `queryCore` | 90 |
| `OneUseRangeFarBank` | `query` | 16 |
| `OneUseRangeCache` | `Backward.query` | 25 |
| `OneUseRangeCache` | `queryValid` | 167 |
| `OneUseRangeCache` | `query` | 49 |

The near index's own scan is restricted to the two clipped blocks,
whose widths are each strictly less than the stored positive width.
The imported near-index audit checks its range sharing and hot paths.

## Runtime and kernel checks

Reproduce the build and executable audit from the repository root:

```sh
lake build REWB.OneUseRangeCacheRegression
lake env lean --run audits/one_use_range_cache_smoke.lean
```

The audit constructs small input rows independently by enumerating the
original all-start cuts. This deliberately slow test fixture is not
counted as production preprocessing. Four asymmetric DFA patterns,
all binary texts of length zero through three, widths 1, 2 and 5, and
one targeted positive-length copy exercise 181 eager cache builds and
3,457 queries. It includes invalid ranges, terminal empty captures,
widths larger than the text and a noninjective transition pattern.

The observed totals were 346 positive answers, 253 positive forward
far answers, 306 positive backward far answers, and 68 positive near
answers, including 40 where both far answers were false. Every full
answer agreed with independent original-cut enumeration. The maximum
small query counter was 4,915.

The length-128, width-8 fixture has 18 actual grid slots. Its all-word
automata have stationary initial states, including the reverse machine;
the audit checks that finite transition premise before constructing
constant final-subset rows. All 780 queries agreed with original cuts.
The observed build counter was 505,406 and maximum query counter was
152,403. Total observed runtime was 45.223 seconds with exit code zero.

The kernel build completed 282 targets. An independent 46-principal
`#print axioms` manifest reported only `propext`, `Classical.choice`
and `Quot.sound`. The new Lean sources contain no admissions, custom
axioms or alternate executable implementations. Empty-input rows and
their `Ready` provenance are constructed and proved directly in
`CacheRegression`, without an all-start assumption.
