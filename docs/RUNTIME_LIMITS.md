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

## Remaining limits

P1 must produce unary formulas for the offline join, so its current generic projection still materializes a large DNF. Formal fixed-pattern constants can be very large, and negative P2 cases can also be expensive. Successful kernel checks should not be described as a practical speedup on ordinary inputs.

The counters distinguish preparation, symbol comparisons, equality-array reads, formula operations, modulus traversal, sorting, interval tests and event/text visits. Allocation, runtime stack representation, garbage collection, bit-level arithmetic and a single complete word-RAM cost semantics are not verified by these probes. Large-input runtime readiness is not asserted.
