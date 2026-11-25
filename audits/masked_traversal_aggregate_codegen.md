# Aggregate query generated-code inspection

Checked with the pinned Lean 4.19.0 compiler after building
`REWB.MaskedTraversalAggregateReplay`.

The generated `MaskedTraversalAggregateWindow.c` query body calls
`Clip_window` once. Its success branch calls `queryBand` once; the failure
branch returns a false answer and zero cut queries. There is no word,
occurrence, deletion-history or length-band traversal in this wrapper.

`MaskedTraversalAggregateBand.c` calls `region`, `close` and the actual
`MaskedCluster_Cut_query` once each. The whole product is closed before
selecting the common replay tuple. It does not choose a separate copy
length for each bank.

`MaskedTraversalAggregateClip.c` reads one actual indexed slot per selected
leader, retains its configuration fields through `Clip_config`, calls the
mutable bank compiler and performs one `MaskedFiniteAction_Tree_replace`
on success. A missing entry or a rejected compilation marks the query
unready. `Clip_window` calls the actual predecessor plan and the bounded
key fold; the checked `plan_length` theorem limits this list to two.

The permanent aggregate and source store are passed immutably. Temporary
boundary replacements share the persistent tree. The shared identity
template is constructed once; `fresh` returns that existing value with
one tracked operation.

This inspection checks the stated compiled call structure. Pattern-size
table/DFA expressions are still visible in generated wrappers. Allocation,
reference counting, reclamation and bit-level arithmetic are not covered
by this inspection or by the abstract query counters. The complete
changing-partition aggregate invariant and all-start reporting execution
remain separate proof obligations.
