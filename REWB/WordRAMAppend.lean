import REWB.WordRAMListBounds

/-! A fixed, two-pass linked-list copy/append program. The first pass copies
the source in reverse into fresh memory; the second copies it back onto
the original accumulator. Both passes follow links and stop at null.
The intermediate list remains allocated, so this implementation uses four
fresh words per source item. No callback is present in this program. -/
namespace REWB.WordRAM.Lists
open ListHeap

def appendProgram : Program := #[
  .const 6 1,.const 7 2,.mov 8 1,.const 1 0,
  .jz 0 15,.load 3 0,.add 5 0 6,.load 4 5,
  .store 2 3,.add 5 2 6,.store 5 1,.mov 1 2,
  .add 2 2 7,.mov 0 4,.jump 4,
  .mov 0 1,.mov 1 8,
  .jz 0 28,.load 3 0,.add 5 0 6,.load 4 5,
  .store 2 3,.add 5 2 6,.store 5 1,.mov 1 2,
  .add 2 2 7,.mov 0 4,.jump 17,.halt]

theorem appendProgram_firstLoop : HasLoop appendProgram 4 15 := by
  unfold HasLoop
  decide

theorem appendProgram_secondLoop : HasLoop appendProgram 17 28 := by
  unfold HasLoop
  decide

def appendSetup (s : State) : State :=
  { (((s.writeReg 6 1).writeReg 7 2).writeReg 8 (s.regs 1)).writeReg 1 0
    with pc := 4 }

def appendFirst (s : State) (xs : List Nat) : State :=
  leave 15 (iterate 4 (appendSetup s) xs)

def appendTurn (s : State) : State :=
  { (s.writeReg 0 (s.regs 1)).writeReg 1 (s.regs 8) with pc := 17 }

def appendResult (s : State) (xs : List Nat) : State :=
  { iterate 17 (appendTurn (appendFirst s xs)) xs.reverse with pc := 28,halted := true }

theorem appendSetup_exec (s : State) (hp : s.pc = 0) (hh : s.halted = false) :
    Exec appendProgram 4 s (appendSetup s) := by
  apply (exec_iff_runSteps _ _ _ _).mpr
  simp [runSteps,step,appendProgram,execInstr,State.writeReg,State.next,hp,hh,appendSetup]

theorem appendTurn_exec (s : State) (hp : s.pc = 15) (hh : s.halted = false) :
    Exec appendProgram 2 s (appendTurn s) := by
  apply (exec_iff_runSteps _ _ _ _).mpr
  simp [runSteps,step,appendProgram,execInstr,State.writeReg,State.next,hp,hh,appendTurn]

theorem appendFirst_source (s : State) (xs : List Nat)
    (hf : 0 < s.regs 2) (hx : ListAt s.heap (s.regs 2) (s.regs 0) xs) :
    ListAt (appendFirst s xs).heap ((appendFirst s xs).regs 2)
      ((appendFirst s xs).regs 1) xs.reverse := by
  have h := iterate_rep 4 (appendSetup s) xs []
    (by simpa [appendSetup,State.writeReg] using hf)
    (by simpa [appendSetup,State.writeReg] using hx)
    (by simpa [appendSetup,State.writeReg] using ListAt.nil (heap := s.heap) (limit := s.regs 2))
  simpa [appendFirst,leave] using h

theorem appendFirst_frontier (s : State) (xs : List Nat)
    (hx : ListAt s.heap (s.regs 2) (s.regs 0) xs) :
    (appendFirst s xs).regs 2 = s.regs 2+2*xs.length := by
  simpa [appendFirst,leave,appendSetup,State.writeReg] using
    iterate_frontier 4 (appendSetup s) xs (by simpa [appendSetup,State.writeReg] using hx)

theorem appendFirst_aux (s : State) (xs : List Nat) (r : Nat) (hr : 6 ≤ r) :
    (appendFirst s xs).regs r = (appendSetup s).regs r := by
  exact iterate_aux_reg 4 (appendSetup s) xs r hr

theorem appendFirst_acc (s : State) (xs ys : List Nat)
    (hx : ListAt s.heap (s.regs 2) (s.regs 0) xs)
    (hy : ListAt s.heap (s.regs 2) (s.regs 1) ys) :
    ListAt (appendFirst s xs).heap ((appendFirst s xs).regs 2)
      ((appendFirst s xs).regs 8) ys := by
  rw [appendFirst_aux s xs 8 (by decide)]
  simp only [appendSetup,State.writeReg,show (8:Nat) ≠ 1 by decide,if_false,ite_true]
  apply ListAt.mono (b := s.regs 2) _ (by rw [appendFirst_frontier s xs hx]; omega)
  apply hy.frame
  intro i hi
  exact iterate_frame 4 (appendSetup s) xs
    (by simpa [appendSetup,State.writeReg] using hx) i (by simpa [appendSetup,State.writeReg] using hi)

theorem append_result_rep (s : State) (xs ys : List Nat)
    (hf : 0 < s.regs 2) (hx : ListAt s.heap (s.regs 2) (s.regs 0) xs)
    (hy : ListAt s.heap (s.regs 2) (s.regs 1) ys) :
    ListAt (appendResult s xs).heap ((appendResult s xs).regs 2)
      ((appendResult s xs).regs 1) (xs++ys) := by
  have h := iterate_rep 17 (appendTurn (appendFirst s xs)) xs.reverse ys
    (by simp [appendTurn,State.writeReg,appendFirst_frontier s xs hx]; omega)
    (by simpa [appendTurn,State.writeReg] using appendFirst_source s xs hf hx)
    (by simpa [appendTurn,State.writeReg] using appendFirst_acc s xs ys hx hy)
  simpa [appendResult] using h

theorem append_result_frontier (s : State) (xs : List Nat)
    (hf : 0 < s.regs 2) (hx : ListAt s.heap (s.regs 2) (s.regs 0) xs) :
    (appendResult s xs).regs 2 = s.regs 2+4*xs.length := by
  have h := iterate_frontier 17 (appendTurn (appendFirst s xs)) xs.reverse
    (by simpa [appendTurn,State.writeReg] using appendFirst_source s xs hf hx)
  simp only [appendResult]
  rw [h]
  simp [appendTurn,State.writeReg,appendFirst_frontier s xs hx]
  omega

theorem append_result_frame (s : State) (xs : List Nat)
    (hf : 0 < s.regs 2) (hx : ListAt s.heap (s.regs 2) (s.regs 0) xs)
    (i : Nat) (hi : i < s.regs 2) : (appendResult s xs).heap i = s.heap i := by
  have hfirst : (appendFirst s xs).heap i = s.heap i :=
    iterate_frame 4 (appendSetup s) xs
      (by simpa [appendSetup,State.writeReg] using hx) i (by simpa [appendSetup,State.writeReg] using hi)
  have hsecond := iterate_frame 17 (appendTurn (appendFirst s xs)) xs.reverse
    (by simpa [appendTurn,State.writeReg] using appendFirst_source s xs hf hx) i
    (by simp [appendTurn,State.writeReg,appendFirst_frontier s xs hx]; omega)
  exact hsecond.trans hfirst

theorem append_exec (s : State) (xs : List Nat) (hp : s.pc = 0)
    (hh : s.halted = false) (hf : 0 < s.regs 2)
    (hx : ListAt s.heap (s.regs 2) (s.regs 0) xs) :
    Exec appendProgram (22*xs.length+9) s (appendResult s xs) := by
  have hstart := appendSetup_exec s hp hh
  have hfirst := loop_exec appendProgram 4 15 (appendSetup s) xs appendProgram_firstLoop rfl
    (by simpa [appendSetup,State.writeReg] using hh)
    (by simp [appendSetup,State.writeReg]) (by simp [appendSetup,State.writeReg])
    (by simpa [appendSetup,State.writeReg] using hx)
  have hturn := appendTurn_exec (appendFirst s xs) rfl
    (by simpa [appendFirst,leave,iterate_halted,appendSetup,State.writeReg] using hh)
  have hsecond := loop_exec appendProgram 17 28 (appendTurn (appendFirst s xs)) xs.reverse
    appendProgram_secondLoop rfl
    (by simpa [appendTurn,State.writeReg,appendFirst,leave,iterate_halted,appendSetup] using hh)
    (by simp [appendTurn,State.writeReg,appendFirst_aux,appendSetup])
    (by simp [appendTurn,State.writeReg,appendFirst_aux,appendSetup])
    (by simpa [appendTurn,State.writeReg] using appendFirst_source s xs hf hx)
  have hend : Exec appendProgram 1
      (leave 28 (iterate 17 (appendTurn (appendFirst s xs)) xs.reverse)) (appendResult s xs) := by
    apply Exec.one
    simp [step,appendProgram,leave,iterate_halted,appendTurn,appendFirst,appendSetup,
      State.writeReg,hh,execInstr,appendResult]
  have h := hstart.trans (hfirst.trans (hturn.trans (hsecond.trans hend)))
  simpa only [List.length_reverse,
    show 4+(11*xs.length+1+(2+(11*xs.length+1+1))) = 22*xs.length+9 by omega] using h

theorem appendSetup_fits {capacity : Nat} {s : State}
    (hs : Fits capacity s) (hc : 4 < capacity) : Fits capacity (appendSetup s) := by
  refine ⟨hc,?_,hs.2.2⟩
  intro r
  simp only [appendSetup,State.writeReg]
  split
  · omega
  · split
    · exact hs.2.1 1
    · split
      · omega
      · split
        · omega
        · exact hs.2.1 r

theorem appendTurn_fits {capacity : Nat} {s : State}
    (hs : Fits capacity s) (hc : 17 < capacity) : Fits capacity (appendTurn s) := by
  refine ⟨hc,?_,hs.2.2⟩
  intro r
  simp only [appendTurn,State.writeReg]
  split
  · exact hs.2.1 8
  · split
    · exact hs.2.1 1
    · exact hs.2.1 r

theorem appendSetup_word_exec (capacity : Nat) (s : State) (hp : s.pc = 0)
    (hh : s.halted = false) (hs : Fits capacity s) (hc : 4 < capacity) :
    WordExec capacity appendProgram 4 s (appendSetup s) := by
  apply (wordExec_iff_runWordSteps _ _ _ _ _).mpr
  have h0 : 0 < capacity := by omega
  have h1 : 1 < capacity := by omega
  have h2 : 2 < capacity := by omega
  have h3 : 3 < capacity := by omega
  simp [runWordSteps,wordStep,touched,appendProgram,execInstr,State.writeReg,
    State.next,hp,hh,appendSetup,h0,h1,h2,h3,hc,hs.2.1]

theorem appendTurn_word_exec (capacity : Nat) (s : State) (hp : s.pc = 15)
    (hh : s.halted = false) (hs : Fits capacity s) (hc : 17 < capacity) :
    WordExec capacity appendProgram 2 s (appendTurn s) := by
  apply (wordExec_iff_runWordSteps _ _ _ _ _).mpr
  have h15 : 15 < capacity := by omega
  have h16 : 16 < capacity := by omega
  simp [runWordSteps,wordStep,touched,appendProgram,execInstr,State.writeReg,
    State.next,hp,hh,appendTurn,h15,h16,hc,hs.2.1]

theorem append_word_exec (capacity : Nat) (s : State) (xs : List Nat)
    (hp : s.pc = 0) (hh : s.halted = false) (hf : 0 < s.regs 2)
    (hx : ListAt s.heap (s.regs 2) (s.regs 0) xs)
    (hs : Fits capacity s) (hc : 28 < capacity)
    (hspace : s.regs 2+4*xs.length < capacity) :
    WordExec capacity appendProgram (22*xs.length+9) s (appendResult s xs) := by
  have hshort : s.regs 2+2*xs.length < capacity := by omega
  have hsf := appendSetup_fits hs (by omega : 4 < capacity)
  have hstart := appendSetup_word_exec capacity s hp hh hs (by omega)
  have hfirst := loop_word_exec appendProgram 4 15 capacity (appendSetup s) xs
    appendProgram_firstLoop rfl (by simpa [appendSetup,State.writeReg] using hh)
    (by simp [appendSetup,State.writeReg]) (by simp [appendSetup,State.writeReg])
    (by simpa [appendSetup,State.writeReg] using hx) hsf (by omega) (by omega)
    (by simpa [appendSetup,State.writeReg] using hshort)
  have hff : Fits capacity (appendFirst s xs) := by
    have h := iterate_fits xs hsf (by omega : 4 < capacity)
      (by simpa [appendSetup,State.writeReg] using hshort)
    exact ⟨by change 15 < capacity; omega,h.2⟩
  have hturn := appendTurn_word_exec capacity (appendFirst s xs) rfl
    (by simpa [appendFirst,leave,iterate_halted,appendSetup,State.writeReg] using hh) hff (by omega)
  have hsecond := loop_word_exec appendProgram 17 28 capacity (appendTurn (appendFirst s xs)) xs.reverse
    appendProgram_secondLoop rfl
    (by simpa [appendTurn,State.writeReg,appendFirst,leave,iterate_halted,appendSetup] using hh)
    (by simp [appendTurn,State.writeReg,appendFirst_aux,appendSetup])
    (by simp [appendTurn,State.writeReg,appendFirst_aux,appendSetup])
    (by simpa [appendTurn,State.writeReg] using appendFirst_source s xs hf hx)
    (appendTurn_fits hff (by omega)) (by omega) hc
    (by simp [appendTurn,State.writeReg,appendFirst_frontier s xs hx]; omega)
  have hend : WordExec capacity appendProgram 1
      (leave 28 (iterate 17 (appendTurn (appendFirst s xs)) xs.reverse)) (appendResult s xs) := by
    apply WordExec.one
    simp [wordStep,touched,appendProgram,leave,iterate_halted,appendTurn,appendFirst,appendSetup,
      State.writeReg,hh,execInstr,appendResult,hc]
  have h := hstart.trans (hfirst.trans (hturn.trans (hsecond.trans hend)))
  simpa only [List.length_reverse,
    show 4+(11*xs.length+1+(2+(11*xs.length+1+1))) = 22*xs.length+9 by omega] using h

end REWB.WordRAM.Lists
