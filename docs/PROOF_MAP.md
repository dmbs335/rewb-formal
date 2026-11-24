# Proof map and verification ledger

**Research draft.** The proposed soft-O(n^(25/13)) algorithm is not a verified result. The initial Lean source covers exact fixed-form witnesses, finite-state algebra and exponent arithmetic. No claimed speedup has been established by the kernel. Passing a finite audit is not a proof of asymptotic complexity.

## Model and dependencies

The register stores the last closed capture, including captured recalled text. The initial register is empty. Each successful trace uses the register at most twice. Prove full normalization from arbitrary expressions to a finite union of the four forms, with explicit handling of zero and one use and unused capture events. The interval classification in NormalForms is only conditional on the supplier intervals being laminar and on the selected endpoints.

## Independent quadratic baseline

For outer capture O(p,e), fix the two outer copy ends e,f. Let d=min(LCS(e,f), f-e). Possible first starts p are e-d through e; the gap is w[e:f-d] ++ w[e-d:p]. Inject G states at e-d with H acceptance at f and scan forward to compute each O column. Propagate through F backwards to construct R(p,t)=∃e≥t, O(p,e) and F(w[t:e]). For P2 absorb the initial B segment into a mask of eligible first inner starts; for P1 transport the varying A prefix across the inner-copy equality and use marked C-to-D and A/D-to-B transitions. Need a verified slice algebra, executable specification, and constant-time finite-monoid and LCS operations with a real cost model. See audits/rewb_nested_quadratic.py.

## Critical obligations

1. Masked all-start one-use: dense occurrence clusters are arithmetic progressions. Separate same-run selections and distinct-cluster selections. Verify finite boundary modes, arbitrary masks, shortening, lazy relabeling, threshold events and all output extraction. Do not assume the claimed amortization from small-input tests.
2. Ordinary range and boundary-aware indexes: prove separated matching state propagation, persistent colored position trees, heavy-path aggregation, fixed endpoint queries, depth cutoffs, all four boundary-block cases and border/prefix-suffix AP queries. Show actual preprocessing soft-O(n²/s) and query soft-O(s²). The Python audits implement logical reference variants, not the claimed fast persistent index.
3. Outer equality-region coverage: expand equal copies; prove disjoint-region reductions and grid hitting for long captures; overlapping maximal regions correspond to runs and a multiple of their minimum period. Long gaps admit a grid cut. Low exponent runs give O(N-2q+1+D0) starts; high-period cubic runs admit O(N²/q) pairs.
4. Small-period branch: fix residues, project the resulting fixed-coefficient Presburger formula; for P1 join external source length records with target intervals and residues via the C automaton. Verify both directions, all endpoint bounds, finite-state phase summaries, and the aggregate costs.
5. Literature: formalize or explicitly isolate Fine–Wilf, the runs theorem, primitive-square occurrence bound, IPM/prefix-suffix range families and fixed-dimensional integer feasibility/projection. Check precise hypotheses before using them.
6. Word-RAM: define a deterministic machine, word width Θ(log(n+2)), uniform finite description for each fixed pattern, actual worst-case step count and correct acceptance. An arbitrary supplied cost function is not a complexity proof.

## Conditional cost ledger

Suppressing polylogs, the draft phase budget is

    n²/s + n L² + n² s²/L + n² s²/D0 + n² s²/Q
      + n D0 s² + n s² + n Q^k.

For P1 k=3, s=n^(1/10), Q=n^(3/10), L=D0=n^(1/3).
For P2 k=4, s=n^(1/13), Q=n^(3/13), L=D0=n^(1/3).
Cost.lean checks scaled integer exponents (57/30 and 75/39). Establish actual algorithm costs and integer rounding separately.

## Literature

- Kumabe–Uezato, ICALP 2026, DOI 10.4230/LIPIcs.ICALP.2026.135.
- Internal pattern matching, SIAM J. Comput. 2024, DOI 10.1137/23M1567618.
- Bannai et al., The “Runs” Theorem; Fine–Wilf periodicity.
- Primitive-square occurrence bounds; fixed-dimensional integer feasibility and fixed-coefficient Presburger elimination.

No claim of novelty, priority, or optimality is made. Revisit the original natural-language proof and resolve each obligation independently.
