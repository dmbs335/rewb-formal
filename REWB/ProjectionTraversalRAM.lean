import REWB.WordRAMAppend
import REWB.CountedProjection

/-! Concrete list instructions are dominated by the existing projection
counters. `appendTR_refines` certifies an entire copy/append primitive.
The map/flatMap theorems certify their final reversal after the callback
results have been represented in the accumulator. They deliberately make
that representation a precondition: no callback is treated as one RAM
instruction and no whole projection/matcher compilation is asserted.
Payload encodings are copied as words; constructing the encoded objects
and simulating arbitrary callbacks remain separate obligations. -/
namespace REWB.ProjectionTraversalRAM
open WordRAM WordRAM.Lists WordRAM.ListHeap

theorem appendTR_instruction_bound (xs ys : List Nat) :
    22*xs.length+9 ≤ 22*(CountedProjection.appendTR xs ys).2 := by
  simp only [CountedProjection.appendTR]
  omega

theorem appendTR_allocation_bound (xs ys : List Nat) :
    4*xs.length ≤ 4*(CountedProjection.appendTR xs ys).2 := by
  simp only [CountedProjection.appendTR]
  omega

/-- A complete primitive refinement: output, instruction count, allocation,
and checked finite-word execution of a fixed program. -/
theorem appendTR_refines (capacity : Nat) (s : WordRAM.State) (xs ys : List Nat)
    (hp : s.pc = 0) (hh : s.halted = false) (hf : 0 < s.regs 2)
    (hx : ListAt s.heap (s.regs 2) (s.regs 0) xs)
    (hy : ListAt s.heap (s.regs 2) (s.regs 1) ys)
    (hs : Fits capacity s) (hc : 28 < capacity)
    (hspace : s.regs 2+4*xs.length < capacity) :
    ∃ t, WordExec capacity appendProgram (22*xs.length+9) s t ∧
      ListAt t.heap (t.regs 2) (t.regs 1) (CountedProjection.appendTR xs ys).1 ∧
      t.regs 2 = s.regs 2+4*xs.length ∧
      22*xs.length+9 ≤ 22*(CountedProjection.appendTR xs ys).2 ∧
      4*xs.length ≤ 4*(CountedProjection.appendTR xs ys).2 ∧ Fits capacity t := by
  have hrun := append_word_exec capacity s xs hp hh hf hx hs hc hspace
  refine ⟨appendResult s xs,hrun,?_,append_result_frontier s xs hf hx,
    appendTR_instruction_bound xs ys,appendTR_allocation_bound xs ys,hrun.preservesFits hs⟩
  exact append_result_rep s xs ys hf hx hy

theorem mapTR_output_length (f : X → CountedProjection.Result Y) (xs : List X) :
    (CountedProjection.mapTR f xs).1.length = xs.length := by
  rw [← CountedProjection.map_eq_mapTR,CountedProjection.map_value]
  exact List.length_map _

theorem mapTR_reverse_instruction_bound (f : X → CountedProjection.Result Y) (xs : List X) :
    11*(CountedProjection.mapTR f xs).1.length+4 ≤ 11*(CountedProjection.mapTR f xs).2 := by
  rw [← CountedProjection.map_eq_mapTR]
  have h := CountedProjection.map_length_le_steps f xs
  rw [CountedProjection.map_value]
  simp only [List.length_map]
  omega

theorem mapTR_reverse_allocation_bound (f : X → CountedProjection.Result Y) (xs : List X) :
    2*(CountedProjection.mapTR f xs).1.length ≤ 2*(CountedProjection.mapTR f xs).2 := by
  rw [← CountedProjection.map_eq_mapTR]
  have h := CountedProjection.map_length_le_steps f xs
  rw [CountedProjection.map_value]
  simp only [List.length_map]
  omega

theorem flatMapTR_reverse_instruction_bound (f : X → CountedProjection.Result (List Y)) (xs : List X) :
    11*(CountedProjection.flatMapTR f xs).1.length+4 ≤ 11*(CountedProjection.flatMapTR f xs).2 := by
  rw [← CountedProjection.flatMap_eq_flatMapTR]
  have h := CountedProjection.flatMap_length_le_steps f xs
  omega

theorem flatMapTR_reverse_allocation_bound (f : X → CountedProjection.Result (List Y)) (xs : List X) :
    2*(CountedProjection.flatMapTR f xs).1.length ≤ 2*(CountedProjection.flatMapTR f xs).2 := by
  rw [← CountedProjection.flatMap_eq_flatMapTR]
  have h := CountedProjection.flatMap_length_le_steps f xs
  omega

/-- The precise final pass, assuming the completed accumulator already
contains the reversed encoded callback results. -/
theorem mapTR_final_reverse (f : X → CountedProjection.Result Y) (encode : Y → Nat) (xs : List X)
    (capacity : Nat) (s : WordRAM.State)
    (hp : s.pc = 0) (hh : s.halted = false) (hf : 0 < s.regs 2) (hn : s.regs 1 = 0)
    (hx : ListAt s.heap (s.regs 2) (s.regs 0) ((CountedProjection.mapTR f xs).1.map encode).reverse)
    (hs : Fits capacity s) (hc : 13 < capacity)
    (hspace : s.regs 2+2*(CountedProjection.mapTR f xs).1.length < capacity) :
    ∃ t, WordExec capacity reverseProgram (11*(CountedProjection.mapTR f xs).1.length+4) s t ∧
      ListAt t.heap (t.regs 2) (t.regs 1) ((CountedProjection.mapTR f xs).1.map encode) ∧
      t.regs 2 = s.regs 2+2*(CountedProjection.mapTR f xs).1.length ∧
      11*(CountedProjection.mapTR f xs).1.length+4 ≤ 11*(CountedProjection.mapTR f xs).2 ∧
      2*(CountedProjection.mapTR f xs).1.length ≤ 2*(CountedProjection.mapTR f xs).2 ∧ Fits capacity t := by
  let words := ((CountedProjection.mapTR f xs).1.map encode).reverse
  have hrun := reverse_word_exec capacity s words hp hh hx hs hc (by simpa [words] using hspace)
  have hrep := reverse_result_rep s words [] hf hx (hn ▸ ListAt.nil)
  have halloc := reverse_result_frontier s words hx
  refine ⟨reverseResult s words,?_,?_,?_,mapTR_reverse_instruction_bound f xs,
    mapTR_reverse_allocation_bound f xs,hrun.preservesFits hs⟩
  · simpa [words] using hrun
  · simpa [words] using hrep
  · simpa [words] using halloc

/-- Variable-length callback outputs have the same concrete final-pass
guarantee. Their total output length is bounded by the existing flatMap
ledger, so its accumulator reversal does not invalidate the cost bound. -/
theorem flatMapTR_final_reverse (f : X → CountedProjection.Result (List Y)) (encode : Y → Nat) (xs : List X)
    (capacity : Nat) (s : WordRAM.State)
    (hp : s.pc = 0) (hh : s.halted = false) (hf : 0 < s.regs 2) (hn : s.regs 1 = 0)
    (hx : ListAt s.heap (s.regs 2) (s.regs 0) ((CountedProjection.flatMapTR f xs).1.map encode).reverse)
    (hs : Fits capacity s) (hc : 13 < capacity)
    (hspace : s.regs 2+2*(CountedProjection.flatMapTR f xs).1.length < capacity) :
    ∃ t, WordExec capacity reverseProgram (11*(CountedProjection.flatMapTR f xs).1.length+4) s t ∧
      ListAt t.heap (t.regs 2) (t.regs 1) ((CountedProjection.flatMapTR f xs).1.map encode) ∧
      t.regs 2 = s.regs 2+2*(CountedProjection.flatMapTR f xs).1.length ∧
      11*(CountedProjection.flatMapTR f xs).1.length+4 ≤ 11*(CountedProjection.flatMapTR f xs).2 ∧
      2*(CountedProjection.flatMapTR f xs).1.length ≤ 2*(CountedProjection.flatMapTR f xs).2 ∧ Fits capacity t := by
  let words := ((CountedProjection.flatMapTR f xs).1.map encode).reverse
  have hrun := reverse_word_exec capacity s words hp hh hx hs hc (by simpa [words] using hspace)
  have hrep := reverse_result_rep s words [] hf hx (hn ▸ ListAt.nil)
  have halloc := reverse_result_frontier s words hx
  refine ⟨reverseResult s words,?_,?_,?_,flatMapTR_reverse_instruction_bound f xs,
    flatMapTR_reverse_allocation_bound f xs,hrun.preservesFits hs⟩
  · simpa [words] using hrun
  · simpa [words] using hrep
  · simpa [words] using halloc

/-- Identity mapping is one concrete callback instance discharged in full:
the fixed append program copies the list onto null. No abstract callback
instruction or callback simulation hypothesis occurs. -/
theorem mapTR_identity_refines (capacity : Nat) (s : WordRAM.State) (xs : List Nat)
    (hp : s.pc = 0) (hh : s.halted = false) (hf : 0 < s.regs 2) (hn : s.regs 1 = 0)
    (hx : ListAt s.heap (s.regs 2) (s.regs 0) xs)
    (hs : Fits capacity s) (hc : 28 < capacity)
    (hspace : s.regs 2+4*xs.length < capacity) :
    ∃ t, WordExec capacity appendProgram (22*xs.length+9) s t ∧
      ListAt t.heap (t.regs 2) (t.regs 1) (CountedProjection.mapTR (fun x : Nat => (x,0)) xs).1 ∧
      22*xs.length+9 ≤ 22*(CountedProjection.mapTR (fun x : Nat => (x,0)) xs).2 ∧
      t.regs 2 = s.regs 2+4*xs.length ∧ Fits capacity t := by
  have hrun := append_word_exec capacity s xs hp hh hf hx hs hc hspace
  refine ⟨appendResult s xs,hrun,?_,?_,append_result_frontier s xs hf hx,hrun.preservesFits hs⟩
  · rw [← CountedProjection.map_eq_mapTR,CountedProjection.map_value]
    simpa using append_result_rep s xs [] hf hx (hn ▸ ListAt.nil)
  · rw [← CountedProjection.map_eq_mapTR,CountedProjection.map_plain_steps]
    simp only [Nat.zero_add,Nat.mul_one]
    omega

end REWB.ProjectionTraversalRAM
