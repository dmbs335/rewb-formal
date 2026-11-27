import REWB.WordRAMLists

/-! Finite-word execution of the concrete copying reverse program.
Every accessed address and produced value is checked by `wordStep`.
The arena capacity is an explicit input-representation condition; the
program still discovers its input length by following stored links. -/
namespace REWB.WordRAM.Lists
open ListHeap

theorem round_fits {capacity entry : Nat} {s : State}
    (hs : Fits capacity s) (he : entry < capacity)
    (hf : s.regs 2+2 < capacity) : Fits capacity (round entry s) := by
  refine ⟨he,?_,?_⟩
  · intro r
    simp only [round]
    split
    · exact hs.2.2 _
    · split
      · exact hf
      · split
        · exact hs.2.1 _
        · split
          · omega
          · split
            · exact hs.2.2 _
            · split
              · exact hs.2.2 _
              · exact hs.2.1 _
  · exact push_values_bounded hs.2.2 (hs.2.2 _) (hs.2.1 _)

theorem iterate_fits {capacity entry : Nat} {s : State} (xs : List Nat)
    (hs : Fits capacity s) (he : entry < capacity)
    (hf : s.regs 2+2*xs.length < capacity) :
    Fits capacity (iterate entry s xs) := by
  induction xs generalizing s with
  | nil => exact hs
  | cons x xs ih =>
    simp only [List.length_cons] at hf
    exact ih (round_fits hs he (by omega)) (by simp [round]; omega)

theorem round_word_exec (p : Program) (entry exit capacity : Nat) (s : State)
    (hc : HasLoop p entry exit) (hp : s.pc = entry) (hh : s.halted = false)
    (hz : s.regs 0 ≠ 0) (h₁ : s.regs 6 = 1) (h₂ : s.regs 7 = 2)
    (hs : Fits capacity s) (he : entry+11 < capacity)
    (ha : s.regs 0+1 < capacity) (hf : s.regs 2+2 < capacity) :
    WordExec capacity p 11 s (round entry s) := by
  have c0 := hc ⟨0,by decide⟩
  have c1 := hc ⟨1,by decide⟩
  have c2 := hc ⟨2,by decide⟩
  have c3 := hc ⟨3,by decide⟩
  have c4 := hc ⟨4,by decide⟩
  have c5 := hc ⟨5,by decide⟩
  have c6 := hc ⟨6,by decide⟩
  have c7 := hc ⟨7,by decide⟩
  have c8 := hc ⟨8,by decide⟩
  have c9 := hc ⟨9,by decide⟩
  have c10 := hc ⟨10,by decide⟩
  simp [loopCode] at c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10
  have pcBound : ∀ k, k ≤ 11 → entry+k < capacity := by intro k hk; omega
  have hp0 : entry < capacity := by omega
  have h1c : 1 < capacity := by omega
  have h2c : 2 < capacity := by omega
  have hf1 : s.regs 2+1 < capacity := by omega
  apply (wordExec_iff_runWordSteps capacity p 11 s (round entry s)).mpr
  simp [runWordSteps,wordStep,touched,execInstr,State.writeReg,State.writeMem,State.next,
    hp,hh,hz,h₁,h₂,c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,Nat.add_assoc,
    pcBound,hp0,h1c,h2c,ha,hf,hf1,hs.2.1,hs.2.2,round]
  constructor
  · funext r
    by_cases h5 : r = 5 <;> simp [h5]
  · rfl

theorem leave_word_exec (p : Program) (entry exit capacity : Nat) (s : State)
    (hc : HasLoop p entry exit) (hp : s.pc = entry) (hh : s.halted = false)
    (hz : s.regs 0 = 0) (hs : Fits capacity s) (he : exit < capacity) :
    WordExec capacity p 1 s (leave exit s) := by
  apply WordExec.one
  apply wordStep_of_fits (t := leave exit s) ?_ hs ⟨he,hs.2⟩
  · have h := hc ⟨0,by decide⟩
    simp [loopCode] at h
    simp [step,hp,hh,h,execInstr,hz,leave]

theorem loop_word_exec (p : Program) (entry exit capacity : Nat) (s : State) (xs : List Nat)
    (hc : HasLoop p entry exit) (hp : s.pc = entry) (hh : s.halted = false)
    (h₁ : s.regs 6 = 1) (h₂ : s.regs 7 = 2)
    (hx : ListAt s.heap (s.regs 2) (s.regs 0) xs)
    (hs : Fits capacity s) (he : entry+11 < capacity) (hxpc : exit < capacity)
    (hf : s.regs 2+2*xs.length < capacity) :
    WordExec capacity p (11*xs.length+1) s (leave exit (iterate entry s xs)) := by
  induction xs generalizing s with
  | nil =>
    simpa [iterate] using leave_word_exec p entry exit capacity s hc hp hh hx.nil_pointer hs hxpc
  | cons x xs ih =>
    obtain ⟨q,hpos,haddr,hval,hnext,htail⟩ := hx.cons_fields
    have hfront : s.regs 2+2 < capacity := by simp only [List.length_cons] at hf; omega
    have hr := round_word_exec p entry exit capacity s hc hp hh (by omega) h₁ h₂ hs he
      (by omega) hfront
    have ht := ih (round entry s) rfl (by simpa [round] using hh)
      (by simpa [round] using h₁) (by simpa [round] using h₂) (round_source hx)
      (round_fits hs (by omega) hfront)
      (by simp [round]; simp only [List.length_cons] at hf; omega)
    have h := hr.trans ht
    simpa only [iterate,show 11+(11*xs.length+1) = 11*(x::xs).length+1 by
      simp only [List.length_cons]; omega] using h

theorem setup_fits {capacity : Nat} {s : State}
    (hs : Fits capacity s) (hc : 2 < capacity) : Fits capacity (setup s) := by
  refine ⟨hc,?_,hs.2.2⟩
  intro r
  simp only [setup,State.writeReg]
  split
  · exact hc
  · split
    · omega
    · exact hs.2.1 r

theorem setup_word_exec (capacity : Nat) (s : State) (hp : s.pc = 0)
    (hh : s.halted = false) (hs : Fits capacity s) (hc : 2 < capacity) :
    WordExec capacity reverseProgram 2 s (setup s) := by
  apply (wordExec_iff_runWordSteps _ _ _ _ _).mpr
  have h0 : 0 < capacity := by omega
  have h1 : 1 < capacity := by omega
  simp [runWordSteps,wordStep,touched,reverseProgram,execInstr,State.writeReg,
    State.next,hp,hh,setup,h0,h1,hc]

theorem reverse_word_exec (capacity : Nat) (s : State) (xs : List Nat)
    (hp : s.pc = 0) (hh : s.halted = false)
    (hx : ListAt s.heap (s.regs 2) (s.regs 0) xs)
    (hs : Fits capacity s) (hc : 13 < capacity)
    (hf : s.regs 2+2*xs.length < capacity) :
    WordExec capacity reverseProgram (11*xs.length+4) s (reverseResult s xs) := by
  have hstart := setup_word_exec capacity s hp hh hs (by omega)
  have hlo := loop_word_exec reverseProgram 2 13 capacity (setup s) xs
    reverseProgram_hasLoop rfl (by simpa [setup,State.writeReg] using hh)
    (by simp [setup,State.writeReg]) (by simp [setup,State.writeReg])
    (by simpa [setup,State.writeReg] using hx) (setup_fits hs (by omega))
    (by omega) hc (by simpa [setup,State.writeReg] using hf)
  have hend : WordExec capacity reverseProgram 1
      (leave 13 (iterate 2 (setup s) xs)) (reverseResult s xs) := by
    apply WordExec.one
    simp [wordStep,touched,reverseProgram,leave,iterate_halted,setup,State.writeReg,
      hh,execInstr,reverseResult,finish,hc]
  have h := hstart.trans (hlo.trans hend)
  simpa only [show 2+(11*xs.length+1+1) = 11*xs.length+4 by omega] using h

end REWB.WordRAM.Lists
