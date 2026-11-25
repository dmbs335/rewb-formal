# Full construction execution: validated scope

This note records the construction-counted all-start solver, its materialized row producers, and the small-period run enumerator. It distinguishes Lean source theorems, executed regression probes, and targeted generated-C inspection. The pinned toolchain is Lean 4.19.0.

## Actual solver and execution

`REWB.MaskedAllStart.FullCost.solve` accepts only the three automata, the materialized text, a fallback symbol, and source/target Boolean arrays. Its implementation calls the measured preparation and measured execution plan, then includes the actual source-update counter difference. It does not accept an answer, budget, bank correctness certificate, or row factory from the caller.

The returned first projection is the complete previous `MaskedAllStart.Result`, including its bitmap, execution state, source history, and previous counters. `solve_value` proves this equality. `solve_correct` consequently gives the original `Spec.maskedStart` predicate for every position and arbitrary input masks. The second projection is the construction-counted work of the executed replacement path.

The new Bank, Updates, Repair, Clip, Erase, Report, Query, Window, Collect, ExecuteBand, and Execute modules substitute measured constructions and prove value preservation through the actual traversal. A band retains its single repair and collection result. Collection retains its single reporting and erase result. The construction bound is proved for this execution, rather than obtained by defining an inflated counter around a call to the old solver.

Writing `H(n) = REWB.ResidualCached.Growth.height n`, the public theorems `solve_work_closed` and `solve_charged_work_closed` prove, for fixed automata and any fixed construction charge `c`,

```text
actualWork + c * fixedPatternBuilds <= C * (n + 2) * H(n)^3.
```

The coefficient depends on the fixed automata and charge. It is used in proofs, not evaluated by a query.

## Materialized rows and cached inputs

The six files `MaskedAllStartFullCostTable`, `MaskedAllStartFullCostRows`, `MaskedAllStartFullCostRowsCost`, `ResidualActualFullCostInputs`, `ResidualActualFullCostInputsCost`, and `MaskedAllStartFullCostRowsRegression` provide 58 audited principal declarations.

The measured table invokes each factory once, stores both its original payload/counter and new work, and reconstructs the previous dependent table from those stored cells. Restoration and projection do not invoke a solver again. Row, prefix, far-right, forward, backward, and boundary constructors preserve their complete previous values. Their Ready contracts therefore transfer to the actual existing boundary and one-use cache consumers.

Far-right construction includes the real `FarRight.prepare` masks. The P1/P2 input constructors build the actual nested finite-variant tables and project their cached payloads. `p1_inputs_profile` and `p2_inputs_profile` bound their new work plus an arbitrary fixed charge for their retained construction count by

```text
C_P * (n + 2) * (n / width + 2) * H(n)^3.
```

Forward grid bounds refer to the original text; backward bounds refer to the reversed text with equal length. The proofs include the actual table restoration and finite projection costs. No query builds the row bank again.

The row/input kernel and all 58 dependency reports passed at commit `917c2d5` ([job 139157729385](https://github.com/dmbs335/rewb-formal/actions/runs/45600471549/job/139157729385)). The final runtime and generated-code checks passed at `8614bf8` ([job 139161245369](https://github.com/dmbs335/rewb-formal/actions/runs/45601488591/job/139161245369)): 288 stored-table checks, four actual rows and one prefix bank, 297 total checks, zero mismatches. The prefix fixture returned full work 2,020,377 while retaining old work 23,194. The two counters are deliberately different.

## Small-period run construction

`PeriodicConstructionRuns.lean` and `PeriodicConstructionRunsCost.lean` provide an actual measured endpoint-list construction, array materialization, counted tests, candidate collection, per-period enumeration, append, and cubic filter. There are 35 audited principal declarations.

`enumerate_value` preserves the complete original pair: both the ordered run list and the previous comparison count. `cubic_value` preserves the original cubic run list together with that comparison count. The cubic implementation enumerates once and filters the retained result. For both measured operations, `enumerate_work_closed` and `cubic_work` prove

```text
actualWork <=
  160 * (Q * (n + (n + 1) * (2 * Q * (Q + 1) + 1)) + n + Q + 1).
```

Their underlying symbol access/equality uses the repository's primitive-operation model; the materialized finite-alphabet text is the intended application.

## Executed checks and generated code

| Scope | Confirmed evidence |
| --- | --- |
| Public full-cost solver | [00528, job 139150686141](https://github.com/dmbs335/rewb-formal/actions/runs/45598459926/job/139150686141): 10 fixtures, 55 position comparisons, 17 positives, 42 bands, 16 reports, zero mismatches; 34,385 ms reported by the probe. It compares actual old/new results and a literal semantic reference. |
| Execution code generation | [8260, job 139143101075](https://github.com/dmbs335/rewb-formal/actions/runs/45596285828/job/139143101075): execution kernel/90 dependency reports and six per-return call checks passed. |
| Materialized rows | [8614bf8, job 139161245369](https://github.com/dmbs335/rewb-formal/actions/runs/45601488591/job/139161245369): 58 exact dependency reports, runtime and generated-code checks passed. |
| Run constructors | [fac5d22, job 139155880205](https://github.com/dmbs335/rewb-formal/actions/runs/45599938988/job/139155880205): 71 build targets, 35 dependency reports, 252 bounded cases and two length-1,024 cases passed. Bounded totals: 208 runs, 7,666 old comparisons, 177,266 full work, zero mismatches. Deep full work was 127,827 and 412,886; complete probe elapsed 257 ms. |

The run probe includes empty input, a zero period threshold, and thresholds larger than the text. It compares ordered output triples and old comparison counts, and checks the explicit polynomial work bound.

The execution C inspection verifies one repair, collection, and finite action call on each of five band return paths; one transaction call on each of three collection return paths; and one report and erase call on each of three transaction return paths. It rejects loop/jump/switch shapes before applying this lexical return-path check, and rejects direct calls to the original report/collect/erase implementations.

The inspected repair/update/plan bodies release intermediate state records before passing owned arrays onward. In those bodies, no retained old array alias forcing a repeated whole-array copy was found. This is a scoped generated-code observation, not a general ownership, allocator, or compiler theorem. The row inspection separately checks the generated factories for direct old solver/row/input calls. Reading its captured bodies also confirms one `FullCost.solve` in the row wrapper and one materializing table build plus one restore. P2 input construction calls forward and backward once on each return path; its two textual backward calls occupy mutually exclusive ownership branches.

Runtime probes use `lake env lean --run`. Generated C is inspected separately. These checks are not described as execution of an independently linked native-C test binary.

## Reproduction and cost boundary

Run from the repository root:

```sh
lake build REWB.MaskedAllStartFullCost REWB.MaskedAllStartFullCostRowsRegression REWB.PeriodicConstructionRunsCost
lake env lean --run audits/masked_full_cost_solve_smoke.lean
lake env lean --run audits/masked_full_cost_rows_smoke.lean
lake env lean --run audits/periodic_runs_construction_smoke.lean
lake env lean audits/periodic_runs_construction_axioms.lean
python3 audits/masked_full_cost_execution_codegen.py
python3 audits/masked_full_cost_rows_codegen.py
```

The audited theorems use only Lean's standard `propext`, `Classical.choice`, and `Quot.sound` where reported; the run family uses only the first and third. The recovery gate rejects incomplete/custom proof constructs.

The mathematical cost statements bound returned ledgers for the stated transition, comparison, list/array construction, finite-state construction, and traversal operations. They do not count arbitrary-precision bit arithmetic, every generated C instruction, reference-count operations, allocator behavior, garbage collection, or elapsed time. No compiler-cost preservation theorem is asserted. This note covers the solver, rows, execution, and run primitive; it does not by itself certify every outer periodic construction or the final expression-level asymptotic assembly.
