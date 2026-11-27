import REWB.WordRAMArithmetic

/-! The concrete arithmetic programs execute without overflow in the
checked word machine. Capacity bounds include program counters, operands,
GCD remainders, and the intermediate LCM product. -/
namespace REWB.WordRAM.Arithmetic

theorem loop_zero_word (capacity : Nat) (p : Program) (pc n tmp : Nat)
    (heap rest : Nat → Nat) (h : LoopAt p pc) (hpc : pc+5 < capacity) :
    WordExec capacity p 1 (frame pc 0 n tmp heap rest)
      (frame (pc+5) 0 n tmp heap rest) := by
  apply WordExec.one
  have hp : pc < capacity := by omega
  have hz : 0 < capacity := by omega
  simp [wordStep,touched,frame,registers,execInstr,h.1,hp,hpc,hz]

theorem loop_five_word (capacity : Nat) (p : Program) (pc m n tmp : Nat)
    (heap rest : Nat → Nat) (h : LoopAt p pc) (hpc : pc+5 < capacity)
    (hm : m < capacity) (hn : n < capacity) (hm0 : m ≠ 0) :
    WordExec capacity p 5 (frame pc m n tmp heap rest)
      (frame pc (n%m) m (n%m) heap rest) := by
  apply (wordExec_iff_runWordSteps _ _ _ _ _).mpr
  rcases h with ⟨h0,h1,h2,h3,h4⟩
  have hp0 : pc < capacity := by omega
  have hp1 : pc+1 < capacity := by omega
  have hp2 : pc+2 < capacity := by omega
  have hp3 : pc+3 < capacity := by omega
  have hp4 : pc+4 < capacity := by omega
  have hr : n%m < capacity := Nat.lt_trans (Nat.mod_lt _ (Nat.pos_of_ne_zero hm0)) hm
  simp [runWordSteps,wordStep,touched,frame,registers,execInstr,State.writeReg,State.next,
    h0,h1,h2,h3,h4,hm0,Nat.add_assoc,hp0,hp1,hp2,hp3,hp4,hpc,hm,hn,hr]
  funext r
  by_cases h0 : r=0 <;> by_cases h1 : r=1 <;> by_cases h2 : r=2 <;>
    simp_all [registers]

theorem gcd_loop_word (capacity : Nat) (p : Program) (pc m n tmp : Nat)
    (heap rest : Nat → Nat) (h : LoopAt p pc) (hpc : pc+5 < capacity)
    (hm : m < capacity) (hn : n < capacity) :
    WordExec capacity p (gcdLoopSteps m n) (frame pc m n tmp heap rest)
      (frame (pc+5) 0 (Nat.gcd m n) (if m=0 then tmp else 0) heap rest) := by
  induction m using Nat.strongRecOn generalizing n tmp with
  | ind m ih =>
    by_cases hm0 : m=0
    · subst m
      simpa [gcdLoopSteps] using loop_zero_word capacity p pc n tmp heap rest h hpc
    · have hr := Nat.mod_lt n (Nat.pos_of_ne_zero hm0)
      have ht := (loop_five_word capacity p pc m n tmp heap rest h hpc hm hn hm0).trans
        (ih (n%m) hr m (n%m) (Nat.lt_trans hr hm) hm)
      have hz : (if n%m=0 then n%m else 0)=0 := by split <;> simp_all
      have hg : Nat.gcd m n = Nat.gcd (n%m) m := by rw [Nat.gcd_def]; simp [hm0]
      rw [gcdLoopSteps]
      simp only [dif_neg hm0,if_neg hm0,hg]
      simpa only [hz,Nat.add_comm] using ht

theorem gcd_lt_capacity (capacity m n : Nat) (hm : m < capacity) (hn : n < capacity) :
    Nat.gcd m n < capacity := by
  by_cases hm0 : m=0
  · simpa [hm0] using hn
  · exact Nat.lt_of_le_of_lt (Nat.gcd_le_left n (Nat.pos_of_ne_zero hm0)) hm

theorem gcd_word_exec (capacity m n : Nat) (hc : 6 ≤ capacity)
    (hm : m < capacity) (hn : n < capacity) :
    WordExec capacity gcdProgram (gcdSteps m n) (gcdInput m n) (gcdOutput m n) := by
  have h := gcd_loop_word capacity gcdProgram 0 m n 0 (fun _=>0) (fun _=>0)
    gcd_loop_at (by omega) hm hn
  have e : WordExec capacity gcdProgram 1
      (frame 5 0 (Nat.gcd m n) 0 (fun _=>0) (fun _=>0)) (gcdOutput m n) := by
    apply WordExec.one
    have h5 : 5 < capacity := by omega
    simp [wordStep,touched,gcdProgram,frame,gcdOutput,execInstr,h5]
  simp only [ite_self,Nat.zero_add] at h
  exact h.trans e

theorem lcm_prefix_word (capacity m n : Nat) (hc : 10 ≤ capacity)
    (hm : m < capacity) (hn : n < capacity) :
    WordExec capacity lcmProgram 2 (lcmInput m n)
      (frame 2 m n 0 (fun _=>0) (saved m n)) := by
  apply (wordExec_iff_runWordSteps _ _ _ _ _).mpr
  have h0 : 0 < capacity := by omega
  have h1 : 1 < capacity := by omega
  have h2 : 2 < capacity := by omega
  simp [runWordSteps,wordStep,touched,lcmProgram,lcmInput,frame,registers,execInstr,
    State.writeReg,State.next,saved,h0,h1,h2,hm,hn]
  funext r
  by_cases h0 : r=0 <;> by_cases h1 : r=1 <;> by_cases h2 : r=2 <;>
    by_cases h3 : r=3 <;> by_cases h4 : r=4 <;> simp_all [registers,saved]

theorem lcm_suffix_word (capacity m n : Nat) (hc : 10 ≤ capacity)
    (hm : m < capacity) (hn : n < capacity) (hprod : m*n < capacity) :
    WordExec capacity lcmProgram 3
      (frame 7 0 (Nat.gcd m n) 0 (fun _=>0) (saved m n)) (lcmOutput m n) := by
  apply (wordExec_iff_runWordSteps _ _ _ _ _).mpr
  have h7 : 7 < capacity := by omega
  have h8 : 8 < capacity := by omega
  have h9 : 9 < capacity := by omega
  have hg := gcd_lt_capacity capacity m n hm hn
  have hd : m*n/Nat.gcd m n < capacity :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hprod
  simp [runWordSteps,wordStep,touched,lcmProgram,frame,registers,execInstr,
    State.writeReg,State.next,saved,lcmOutput,Nat.lcm,h7,h8,h9,hm,hn,hprod,hg,hd]
  funext r
  by_cases h0 : r=0 <;> by_cases h1 : r=1 <;> by_cases h2 : r=2 <;>
    by_cases h3 : r=3 <;> by_cases h4 : r=4 <;> simp_all [registers,saved]

theorem lcm_word_exec (capacity m n : Nat) (hc : 10 ≤ capacity)
    (hm : m < capacity) (hn : n < capacity) (hprod : m*n < capacity) :
    WordExec capacity lcmProgram (lcmSteps m n) (lcmInput m n) (lcmOutput m n) := by
  have h := gcd_loop_word capacity lcmProgram 2 m n 0 (fun _=>0) (saved m n)
    lcm_loop_at (by omega) hm hn
  simp only [ite_self] at h
  have out := ((lcm_prefix_word capacity m n hc hm hn).trans h).trans
    (lcm_suffix_word capacity m n hc hm hn hprod)
  have he : (2+gcdLoopSteps m n)+3=lcmSteps m n := by unfold lcmSteps; omega
  rw [he] at out
  exact out

theorem lcm_word_exec_cap (cap m n : Nat) (hm : m ≤ cap) (hn : n ≤ cap) :
    WordExec (cap*cap+cap+10) lcmProgram (lcmSteps m n) (lcmInput m n) (lcmOutput m n) := by
  have hprod : m*n ≤ cap*cap := Nat.mul_le_mul hm hn
  exact lcm_word_exec _ m n (by omega) (by omega) (by omega) (by omega)

theorem lcmInput_fits (capacity m n : Nat) (hc : 0 < capacity)
    (hm : m < capacity) (hn : n < capacity) : Fits capacity (lcmInput m n) := by
  refine ⟨hc,?_,fun _=>hc⟩
  intro r
  simp only [lcmInput,frame,registers]
  split <;> first | assumption | skip
  split <;> first | assumption | skip
  simp [hc]

theorem lcmOutput_fits (capacity m n : Nat) (hc : 10 ≤ capacity)
    (hm : m < capacity) (hn : n < capacity) (hprod : m*n < capacity) :
    Fits capacity (lcmOutput m n) := by
  have hz : 0 < capacity := by omega
  have hg := gcd_lt_capacity capacity m n hm hn
  have hl : Nat.lcm m n < capacity :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hprod
  refine ⟨by simpa [lcmOutput,frame] using (show 9<capacity by omega),?_,fun _=>hz⟩
  intro r
  simp only [lcmOutput,frame,registers,saved]
  split <;> first | assumption | skip
  split <;> first | assumption | skip
  split <;> first | assumption | skip
  split <;> first | assumption | skip
  split <;> assumption

end REWB.WordRAM.Arithmetic
