# Concrete word-RAM refinement

Updated 2026-11-27. This continuation starts from the construction-ledger
checkpoint `b1a082820f590ce01dae4dfa22f4eafb2bdaa6e0`. It adds 24 Lean modules
and 293 theorem reports to the public import/dependency gates.

**Current result:** concrete arithmetic and list programs have independently
counted, kernel-verified instruction executions, with checked finite-word
variants and scoped connections to the installed matcher's counters.
The complete six-form matcher does not yet have a word-RAM execution
refinement. Its existing correctness and returned-ledger target remain
the end-to-end results.

## Instruction model

`REWB.WordRAM` defines a finite array of instructions, a program counter,
registers, random-access memory and a halt flag. Successful `step` transitions
execute exactly one instruction. `Exec program steps input output` counts
those transitions independently of any source algorithm's returned ledger.
The language has constants, moves, arithmetic, loads/stores, conditional
and unconditional jumps, and halt. It has no host callback, supplied answer,
supplied cost or high-level matcher instruction.

This is the unit-cost word-RAM variant with multiplication, division and
remainder instructions. Natural subtraction saturates at zero. Division
and remainder use Lean's total natural-number semantics; in particular,
division by zero returns zero. The LCM implementation therefore also covers
the `(0,0)` case. These are explicit machine choices, not a theorem about
the wall-clock cost of Lean's arbitrary-precision arithmetic.

`wordStep capacity` checks touched operands, addresses, results and program
counters, trapping if a value does not fit. At capacity `2^w`, it provides
the finite-word execution relation `WordExec`. `WordExec.toExec` proves
agreement with the natural-valued instruction semantics. Given initial
`Fits`, `WordExec.prefixFits` proves that every natural execution prefix up
to the certified count also has representable registers, heap values and PC.
The initial whole-state invariant is a real hypothesis: a trace that checks
only touched words does not constrain arbitrary untouched memory by itself.

## Complete local instruction programs

| Program | Certified execution | Capacity and representation |
| --- | --- | --- |
| Euclidean GCD | Exact `gcdLoopSteps m n + 1`; at most `5*m+2` instructions | Both inputs fit and capacity is at least 6. |
| LCM | Exact `gcdLoopSteps m n + 5`; at most `5*m+6` instructions | Both inputs, their product and PCs fit; inputs at most `M` are supported at capacity `M*M+M+10`. |
| Copying reverse | Exactly `11*length+4` instructions | Null-terminated two-cell source list, initial `Fits`, capacity above PC 13 and final frontier. Allocates exactly `2*length` fresh words. |
| Two-pass copy/append | Exactly `22*length+9` instructions | Source and accumulator representations, initial `Fits`, capacity above PC 28 and final frontier. Allocates exactly `4*length` fresh words. |
| Connected LCM fold | Exact recursive `LCMFold.steps`; at most `4+(5*M+11)*length` when every item divides positive `M` | One 18-instruction program includes both list control flow and Euclid's loop. Capacity `limit+M*M+M+18` suffices for all touched words and addresses. |

The lists are stored as a value at address `p` and successor at `p+1`, with
zero reserved for null. The reverse and append programs read these links
and terminate at null. Their runtime inputs contain no list length or
precomputed result. The logical lists in their theorem statements describe
the represented heap and support induction. Original cells below the fresh
frontier are preserved. Append intentionally retains its intermediate
reversed copy and charges that allocation.

`WordRAMInputLists` gives an explicit finite-alphabet input encoding with
frontier `1+2*n`. It proves initial whole-state `Fits` and the actual reverse
execution at power-of-two capacity with width

```text
width = log2(σ+20)+1 + (log2(n+2)+1).
width <= (log2(σ+20)+2) * (log2(n+2)+1).
```

This encoding stores only input letter values and successor links. Its
result representation is the reversed input and its step count is
`11*n+4`, for every input, including the empty word.

## Connection to installed arithmetic and traversal

`ActualModulusCalls` observes the precise left-fold LCM operand order used
by the installed `ActualModulus.fastFold` substitutions. It proves the
result value, call count and divisibility invariant for rows, formulas,
entry lists and the final build. Their original counters equal
`2*callCount+1`. Every intermediate operand divides the same positive
compatible modulus, and consequently is bounded by it.

`ActualModulusRAM` replaces the unit LCM price in that observation by the
exact instruction length of the verified LCM program. `PeriodicModulusRAM`
discharges compatibility for the actual `FullCost.Long.prepare` source and
target events. Its arithmetic contribution is at most

```text
(5*p1Modulus(P)+6) * actualLongPrepareWork.
```

The coefficient and arithmetic word width depend only on the fixed pattern.
This sum certifies actual primitive calls; it does not by itself execute
their surrounding event/formula traversal.

`ActualModulusFoldRAM.row_word_refines` goes further for a single
conjunction: given a heap list representing its atom modulus fields, one
connected checked RAM program computes the actual `ActualModulus.row`
result, halts, leaves the heap unchanged and uses at most

```text
(5*M+11) * (ActualModulus.row C).2
```

instructions. The input representation supplies the atom fields, not their
aggregate LCM or a cost. Constructing the enclosing formula/event heap and
composing nested traversals are still separate obligations. Its theorem
checks every touched word; it does not infer a bound on untouched heap
values without an initial `Fits` invariant.

`ProjectionModulusCalls` independently observes the right-recursive
multiplier/common-period calls in `CountedProjection`. It covers eager
projection and the actual short-circuit search. The eager and unpruned
traces are invariant under literal erasure. Actual search can prune based
on literals, so its calls are proved contained in the corresponding
unpruned trace and their count is bounded by the actual search counter.
`ActualProjectionModulusRAM` instantiates the finite shape families for the
installed cached P2 search and P1 target projection, including prepared
boundary contexts. Each observed call has a checked instruction trace;
their total lengths are bounded by a fixed-pattern multiple of the actual
projection ledger. The left-fold program's exact operand sequence is not
identified with these right-recursive calls.

`ProjectionTraversalRAM.appendTR_refines` certifies an entire append
primitive with at most 22 times its actual counter in instructions and
4 times that counter in allocated words. `mapTR_final_reverse` and
`flatMapTR_final_reverse` certify the final reversal of an already completed,
encoded accumulator, using at most 11 times the corresponding actual
counter in instructions. The completed accumulator is an explicit
precondition. Arbitrary callbacks have not been replaced by unit-time
instructions. Identity mapping is one fully discharged concrete case.

## Word magnitudes and final numerical transfer

`MachineWordBounds` constructs an explicit width for any proved polynomial
cap `C*(n+2)^d`, including addresses and signed magnitude representations.
`PeriodicMachineWordBounds` instantiates existing bounds on P1/P2 formula
constant terms. `AffineWordBounds` strengthens this to every affine
subexpression in all P2 stages through 8 and P1 target stages through 5,
including intermediate values that later cancel. Those stage corollaries
evaluate at the empty environment, and signed representation requires a
sign bit. These are actual data bounds, but they are not a lowered signed
affine evaluator or a global heap invariant.

`MatcherMachineCostTransfer` proves that if an independently verified
implementation has answer refinement and the uniform simulation bound

```text
steps(w) <= preprocessing
  + factor * (wordWork(w)+length(w)+1) * H(length(w))^overhead,
```

then its execution cost satisfies the target, with logarithm exponent
`39+13*overhead` in the thirteenth-power inequality. The constant is selected
before all input words. The displayed simulation inequality and answer
refinement remain explicit premises. There is no theorem here discharging
them for a complete matcher machine.

## Remaining proof work

The remaining end-to-end obligation is to construct and compose concrete
RAM implementations of the other matcher routines: text/index access,
array and tree operations, sorting/joins, finite-state tables and formula
evaluation, then the row producers and six-form dispatch. Their heap
representations and callback/control-flow boundaries must agree. The
combined execution must establish a global value/address/allocation
invariant and the simulation inequality above. Fixed-pattern preprocessing
may be charged as a pattern-dependent constant or performed before text
execution, with its concrete result represented in memory.

This independent RAM route does not require verifying Lean's compiler,
reference counts, allocator or garbage collector. Conversely, the present
local programs do not establish any cost theorem about those Lean runtime
components. The existing unsuccessful positive-P1 and full-normalization
runtime diagnostics remain documented in `RUNTIME_LIMITS.md`.

## Reproduction

```sh
bash scripts/check.sh
bash scripts/ram-audit.sh
```

The full gate includes all 293 new theorem reports. The focused RAM audit
checks the same new declarations and runs the actual instruction
interpreter. Its bounded execution suite covers 441 GCD/LCM input pairs,
39 reverse fixtures, 39 append fixtures, 7 connected LCM folds and 4
overflow traps. It checks values, exact halting times, allocation counts
and preservation of original memory. The reverse/frontier overflow case
has capacity above every instruction address, so it isolates the intended
allocation failure. Finite probes supplement the universal Lean proofs;
they do not replace an end-to-end matcher simulation.
