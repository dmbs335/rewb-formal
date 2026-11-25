# Periodic construction audit

This audit concerns the actual periodic P1/P2 preparation paths and their returned structural-operation ledgers. The inspected `PeriodicActualFullCostPrepare`, `PeriodicActualFullCostEvents` and `PeriodicActualFullCostShort` sources are byte-identical at commits `fac5d22ee08a872b77ed3b5ddae2791857abd0e3` and `917c2d54a8ba8ae995da0884334661fc0717348f`.

## Installed execution paths

Each branch preparation binds the following results once and consumes those results. Separate P1/P2 branches may each perform their own preparation; this is not a claim that all branches share one global enumeration.

| Work | Actual path | Accounting |
|---|---|---|
| Text materialization | `PeriodicActual.P2.segment` | Source reads, list construction and scalar updates; `3*n+1`. |
| Exterior DFA contexts | `Cache.contexts` | Prefix states, every suffix state row and both arrays; at most 64 times the legacy boundary-entry counter. |
| Run discovery | `Runs.enumerate`, followed by `Orbit.filter` | Actual enumeration/extension bookkeeping and cubic filtering; the old run list and comparison count are retained. |
| Periodic transition/equality tables | `Cache.prepareAt` once per retained run | Actual segment, state-domain, prefix-table, equality-table, row and array construction. Source and target event generation reuse the resulting shared cache. |
| Rotation and short target keys | `Keys.Rotation.tables` / `Keys.Short.tables` | Actual word creation, repeated/taken pieces, exact interning and rank-array materialization. |
| Ordinary short source keys | `PeriodicActual.Short.sourceKeys` | Each token calls measured `P2.segment` once. Its extra work is exactly `3*cells + 7*tokenCount + 1`; trie-assignment work is retained separately. |
| Event construction | `Events.source`, `Events.target`, `Short.choice` | Measured formula construction/projection, schedule traversal and list assembly. A short target projects once per phase and performs exactly three measured exponent checks. |

In particular, `FullCost.Short.prepare` includes both `sk.1.work` and `sk.2`. The first is the actual source-key trie ledger; the second charges source-word/list construction. The uninstrumented `P1ShortSources.buildKeys` appears in value-preservation proofs, not as a second executed source generator.

The wrappers preserve the entire old result, including old counters. Their added work is obtained from the executed replacement constructors. Some charges overlap deliberately; the resulting budgets are conservative upper bounds. Old generators are not rerun to recover their statistics.

## Fixed-pattern coefficients

The cache bounds are concrete:

- Transition tables: `64*(states+1)*(q+1)^2`.
- Equality tables: `64*(q+1)^3`.
- Shared run preparation: `128*(stateSum P+1)*(q+1)^3`.
- `prepareCoefficient P = 1024*(stateSum P+1)`.
- New preparation work is at most that coefficient times `oldPreparationWork+1`; for positive period, twice that coefficient times the old counter suffices.

The zero-period case is explicit: each empty table costs 6, and seven-DFA preparation costs 72 even though the legacy transition/comparison counter is zero.

The actual cache builders do not call these bound functions or finite template-enumeration factories. Array materialization obtains its size from the produced array, without an additional list-length scan. Formula-family budgets elsewhere remain proof bounds; their numerical evaluation is not inserted into these constructors.

## Primitive model and its boundary

The selected model counts scalar arithmetic/comparisons, direct symbol access, DFA operations, documented trie operations, list/array structural work, and **primitive LCM calls**. It excludes elementary bit-operation costs, internal Euclidean/GCD-loop costs of those primitive LCM calls, runtime allocation/GC and reference-counting semantics.

The explicit retained LCM sites are:

- [`ActualModulus.row`, `formula`, `entries`, and `build`](../REWB/ActualModulus.lean); compiled fold replacements use `ActualModulus.combine` / `buildFast`.
- [`CountedProjection.multiplier` and `commonPeriod`](../REWB/CountedProjection.lean). The runtime projection path is `project → eliminateFormula → eliminateConj`; normalization calls `multiplier`, and `eliminateConj` calls `commonPeriod` on the normalized guards.

`LiteralShape.multiplier_conj` and `commonPeriod_map` show that numeric RHS literals do not change these LCM values. Generic formulas can supply arbitrary coefficients or moduli. For the actual periodic formulas, `UniformPhaseBounds` supplies finite fixed-pattern families; the emitted-event modulus is bounded by the compatible fixed-pattern modulus through `ActualModulus.build_le`. Values may vary with emitted formulas, but these bounds do not grow with text literals.

Those sites count each LCM as a primitive step; they do not use the separate Euclidean-loop ledger in `PeriodicConstruction.Pattern.lcm`. This is an explicit model choice, not a claim about native instruction counts. Production text readers are shifted `ArrayText.read` closures, so source access does not hide list indexing or a fresh text scan.

No additional text-length-dependent constructor outside the documented Cache/Runs/Keys replacements was found in the inspected P1 preparation paths.

## Confirmed validation

- Cut construction/query family: commit `cfead9ae7031656d8ec5e89b9872f6a4ba020f1f`, [job 139136754568](https://github.com/dmbs335/rewb-formal/actions/runs/45594456698/job/139136754568). Kernel build, 112 principal axiom reports, and actual runtime audit passed. Runtime checked 60 builds, 564 ranges, 1,404 closed windows, 17,199 literal matrix cells, 1,280 tuple queries, 241 guarded queries, 24 full phases, and a length-257 profile.
- Run construction: commit `fac5d22ee08a872b77ed3b5ddae2791857abd0e3`, [job 139155880205](https://github.com/dmbs335/rewb-formal/actions/runs/45599938988/job/139155880205). Build and 35 principal reports passed; runtime checked 252 cases, 208 runs, zero mismatches, and two length-1024 profiles.
- Key construction: the same commit, [job 139155880058](https://github.com/dmbs335/rewb-formal/actions/runs/45599938988/job/139155880058). Build and 25 principal reports passed; runtime checked 24 intern fixtures, 64 run-table fixtures, 720 keys and 37 runs, with zero mismatches.
- Cache construction: commit `8614bf808df5bbb5f73bd629951f01617923fa6c`, [job 139161245512](https://github.com/dmbs335/rewb-formal/actions/runs/45601488591/job/139161245512). Five-module build, all 49 principal reports and runtime audit passed in 1,601 ms. Runtime checked 1,200 transition tables/16,800 literal cells, 300 equality tables/7,800 literal cells, 60 exterior contexts, and 1,500 shared preparations. The length-1024/period-17 profile retained old work 8,670 and measured new work 114,567; the 64-state zero-period case retained preparation work 72.

- Installed periodic P1/P2 wrappers: the same `8614bf8` commit, [P2 job 139161245173](https://github.com/dmbs335/rewb-formal/actions/runs/45601488591/job/139161245173), [preparation job 139161245260](https://github.com/dmbs335/rewb-formal/actions/runs/45601488591/job/139161245260), and [branch job 139161245183](https://github.com/dmbs335/rewb-formal/actions/runs/45601488591/job/139161245183). All three jobs passed with 56 principal reports in total. The installed-path runtime checked three non-cubic P1 fixtures, one positive P2 case and one empty cubic case, with zero mismatches in 50 ms.

The axiom reports use only standard Lean axioms where required. This audit records local construction and the inspected installation paths; the public combined matcher and final parameter optimization are certified by their separate integration theorems.
