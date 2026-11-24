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


## Baseline formalization branch

The new Reference module implements exhaustive finite split enumeration and four exact Boolean matchers. Their correctness statements refer to the operational MatchesWithin relation through the concrete normal-form witness theorems. They deliberately make no quadratic or subquadratic time claim.

MarkedDP isolates two central finite-state invariants: accepting a prefix ending at an arbitrary eligible mark (the backwards F absorption), and choosing exactly one marked switch from D into B, preserving the same split for both conditions. Marks are allowed at the terminal position. The shortening lemma transports the removed common prefix into the gap between equal copies.

TraceFacts proves that generated traces restore stack depth, characterizes the dynamic-use promise via the syntactic trace count, and proves the emitted-text erasure property for traces without recalls. General supplier selection and compilation of regular inter-event regions remain open.

Remaining for the independent quadratic baseline: derive the outer-column injection relation from verified substring boundaries and a certified common-suffix limit, connect the F and D/B recurrences to P1/P2, materialize finite-state tables in an explicit cost model, and verify the two endpoint loops. The new reference matchers can be used as test oracles for this work. Kernel status remains to be checked by CI; proof scripts are not asserted to have compiled merely because they were written.

OuterColumn now contains the endpoint-indexed slice calculus, a certified reference maximum for min(LCS(e,f), f-e), the shortening/gap transport identity, a pointwise equivalence for fixed outer-copy ends, and the forward seeded-scan invariant and column correctness statement. The reference maximum scans lengths, so this module alone does not establish the fast LCS computation or a quadratic time bound.


## Indexed nested endpoint decisions and materialized masks (PR #5)

The following implementation modules passed the Lean 4.19 kernel and reference-audit jobs on commit 71694ff62dedd057e40b203e7d374661662964e6 (Actions run 45389536414):

- OrderedExit.Machine.run_left: ordered transition from a nondeterministic phase to a deterministic final phase, including an exit at the terminal boundary.
- TensorRelation.tensor_comp: correctness of synchronizing a relation with a deterministic state transformer.
- P1Index.p1_query: exact P1 anchored predicate using two indexed range products and a finite-state join at z=t-d, **given the correct Ready mask**. The A state is inserted at z, not at the first marked switch. Both switches may occur at the same boundary.
- MaskScan.readyRow_correct: a backward scan computes all ReadyState values for fixed p, **given the correct Outer(p,e) bits**.
- MaskScan.forward_correct and first2Row_correct: seeded forward DFA scans and P2's First2 marks, **given the correct seeds or Ready bits**.

The next executable integration must construct the outer seeds from the LCS table, G transition queries and H suffix acceptance; generate all outer columns and Ready bits; then build the indexed query masks for each t and enumerate (a,t). The P1 and P2 endpoint reductions are unconditional, but the indexed implementations still have these explicit input-mask hypotheses. The current dyadic query routing is logarithmic, and the LCS table uses quadratic storage. No complete time/space bound or final strongly subquadratic theorem is asserted.
