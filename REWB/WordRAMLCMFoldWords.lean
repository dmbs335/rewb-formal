import REWB.WordRAMLCMFold
import REWB.WordRAMArithmeticWords

/-! Checked finite-word execution of the complete linked-list LCM fold.
The bounds cover every read payload, successor address, Euclidean operand,
intermediate product, and program counter in the connected execution. -/
namespace REWB.WordRAM.LCMFold

open Arithmetic ListHeap

theorem nodePrefix_word (capacity m n tmp a b ptr addr acc x : Nat)
    (heap rest : Nat → Nat) (hc : 18 ≤ capacity) (hp : ptr ≠ 0)
    (hptr : ptr < capacity) (hacc : acc < capacity) (hval : x < capacity)
    (hx : heap ptr = x) :
    WordExec capacity program 5 (state 2 m n tmp a b ptr addr acc heap rest)
      (state 7 acc x tmp acc x ptr addr acc heap rest) := by
  apply (wordExec_iff_runWordSteps _ _ _ _ _).mpr
  have hpc (n : Nat) (hn : n < 18) : n < capacity := Nat.lt_of_lt_of_le hn hc
  simp [runWordSteps,wordStep,touched,program,state,frame,registers,extras,execInstr,
    State.writeReg,State.next,hp,hx,hpc,hptr,hacc,hval]
  funext r
  by_cases h0 : r=0 <;> simp_all [registers,extras]
  by_cases h1 : r=1 <;> simp_all [registers,extras]
  by_cases h2 : r=2 <;> simp_all [registers,extras]
  by_cases h3 : r=3 <;> simp_all [registers,extras]

theorem suffix_word (capacity acc x tmp ptr addr q : Nat) (heap rest : Nat → Nat)
    (hc : 18 ≤ capacity) (ha : acc < capacity) (hx : x < capacity)
    (hprod : acc*x < capacity) (hptr : ptr+1 < capacity) (hnext : q < capacity)
    (hq : heap (ptr+1) = q) :
    WordExec capacity program 5 (state 12 0 (Nat.gcd acc x) tmp acc x ptr addr acc heap rest)
      (state 2 (acc*x) (Nat.gcd acc x) tmp acc x q (ptr+1)
        (Nat.lcm acc x) heap rest) := by
  apply (wordExec_iff_runWordSteps _ _ _ _ _).mpr
  have hpc (n : Nat) (hn : n < 18) : n < capacity := Nat.lt_of_lt_of_le hn hc
  have hp : ptr < capacity := by omega
  have hg := gcd_lt_capacity capacity acc x ha hx
  have hd : acc*x/Nat.gcd acc x < capacity :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hprod
  simp [runWordSteps,wordStep,touched,program,state,frame,registers,extras,execInstr,
    State.writeReg,State.next,hq,Nat.lcm,hpc,ha,hx,hprod,hptr,hnext,hp,hg,hd]
  funext r
  by_cases h0 : r=0 <;> simp_all [registers,extras]
  by_cases h1 : r=1 <;> simp_all [registers,extras]
  by_cases h2 : r=2 <;> simp_all [registers,extras]
  by_cases h3 : r=3 <;> simp_all [registers,extras]
  by_cases h4 : r=4 <;> simp_all [registers,extras]
  by_cases h5 : r=5 <;> simp_all [registers,extras]
  by_cases h6 : r=6 <;> simp_all [registers,extras]
  by_cases h7 : r=7 <;> simp_all [registers,extras]

theorem exit_word (capacity m n tmp a b addr acc : Nat) (heap rest : Nat → Nat)
    (hc : 18 ≤ capacity) :
    WordExec capacity program 2 (state 2 m n tmp a b 0 addr acc heap rest)
      {state 17 m n tmp a b 0 addr acc heap rest with halted := true} := by
  apply (wordExec_iff_runWordSteps _ _ _ _ _).mpr
  have hpc (n : Nat) (hn : n < 18) : n < capacity := Nat.lt_of_lt_of_le hn hc
  simp [runWordSteps,wordStep,touched,program,state,frame,registers,extras,execInstr,hpc]

theorem startup_word (capacity ptr : Nat) (heap : Heap) (hc : 18 ≤ capacity) :
    WordExec capacity program 2 (input ptr heap)
      (state 2 0 0 0 0 0 ptr 0 1 heap (fun _=>0)) := by
  apply (wordExec_iff_runWordSteps _ _ _ _ _).mpr
  have hpc (n : Nat) (hn : n < 18) : n < capacity := Nat.lt_of_lt_of_le hn hc
  simp [runWordSteps,wordStep,touched,program,input,state,frame,registers,extras,execInstr,
    State.writeReg,State.next,hpc]
  funext r
  by_cases h0 : r=0 <;> simp_all [registers,extras]
  by_cases h1 : r=1 <;> simp_all [registers,extras]
  by_cases h2 : r=2 <;> simp_all [registers,extras]
  by_cases h3 : r=3 <;> simp_all [registers,extras]
  by_cases h4 : r=4 <;> simp_all [registers,extras]
  by_cases h5 : r=5 <;> simp_all [registers,extras]
  by_cases h6 : r=6 <;> simp_all [registers,extras]
  by_cases h7 : r=7 <;> simp_all [registers,extras]

theorem loop_word_exec (capacity M : Nat) (heap rest : Nat → Nat) (limit ptr : Nat)
    (xs : List Nat) (hx : ListAt heap limit ptr xs) (m n tmp a b addr acc : Nat)
    (hc : 18 ≤ capacity) (hlim : limit ≤ capacity) (hM : 0 < M)
    (hword : M < capacity) (hproduct : M*M < capacity)
    (hacc : acc ∣ M) (hvals : ∀ x ∈ xs, x ∣ M) :
    ∃ out, WordExec capacity program (loopSteps acc xs)
      (state 2 m n tmp a b ptr addr acc heap rest) out ∧
      Result heap (xs.foldl Nat.lcm acc) out := by
  induction xs generalizing ptr m n tmp a b addr acc with
  | nil =>
    have hp := hx.nil_pointer
    subst ptr
    refine ⟨{state 17 m n tmp a b 0 addr acc heap rest with halted:=true},
      exit_word capacity m n tmp a b addr acc heap rest hc, ?_⟩
    simp [Result,state,frame,registers,extras]
  | cons x xs ih =>
    obtain ⟨q,hp,ha,hv,hn,ht⟩ := hx.cons_fields
    have hacc_le : acc ≤ M := Nat.le_of_dvd hM hacc
    have hx_dvd : x ∣ M := hvals x (by simp)
    have hx_le : x ≤ M := Nat.le_of_dvd hM hx_dvd
    have ha_word : acc < capacity := Nat.lt_of_le_of_lt hacc_le hword
    have hx_word : x < capacity := Nat.lt_of_le_of_lt hx_le hword
    have hprod : acc*x < capacity :=
      Nat.lt_of_le_of_lt (Nat.mul_le_mul hacc_le hx_le) hproduct
    have hq : q < capacity := Nat.lt_of_lt_of_le (ht.pointer_lt (by omega)) hlim
    obtain ⟨out,he,hr⟩ := ih q ht (acc*x) (Nat.gcd acc x)
      (if acc=0 then tmp else 0) acc x (ptr+1) (Nat.lcm acc x)
      (Nat.lcm_dvd hacc hx_dvd) (fun y hy => hvals y (by simp [hy]))
    have hpre := nodePrefix_word capacity m n tmp a b ptr addr acc x heap rest hc
      (by omega) (by omega) ha_word hx_word hv
    have hg := gcd_loop_word capacity program 7 acc x tmp heap
      (extras acc x ptr addr acc rest) loop_at (by omega) ha_word hx_word
    have hs := suffix_word capacity acc x (if acc=0 then tmp else 0) ptr addr q heap rest
      hc ha_word hx_word hprod (by omega) hq hn
    have hall := ((hpre.trans hg).trans hs).trans he
    refine ⟨out, ?_, ?_⟩
    · have hcount : (5+gcdLoopSteps acc x)+5+loopSteps (Nat.lcm acc x) xs =
          loopSteps acc (x::xs) := by simp only [loopSteps]; omega
      rw [hcount] at hall
      exact hall
    · simpa using hr

theorem word_exec (capacity M : Nat) (heap : Heap) (limit ptr : Nat) (xs : List Nat)
    (hx : ListAt heap limit ptr xs) (hc : 18 ≤ capacity) (hlim : limit ≤ capacity)
    (hM : 0 < M) (hword : M < capacity) (hproduct : M*M < capacity)
    (hvals : ∀ x ∈ xs, x ∣ M) :
    ∃ out, WordExec capacity program (steps xs) (input ptr heap) out ∧
      Result heap (xs.foldl Nat.lcm 1) out := by
  obtain ⟨out,he,hr⟩ := loop_word_exec capacity M heap (fun _=>0) limit ptr xs hx
    0 0 0 0 0 0 1 hc hlim hM hword hproduct (Nat.one_dvd M) hvals
  exact ⟨out,(startup_word capacity ptr heap hc).trans he,hr⟩

theorem word_exec_cap (M : Nat) (heap : Heap) (limit ptr : Nat) (xs : List Nat)
    (hx : ListAt heap limit ptr xs) (hM : 0 < M) (hvals : ∀ x ∈ xs, x ∣ M) :
    ∃ out, WordExec (limit+M*M+M+18) program (steps xs) (input ptr heap) out ∧
      Result heap (xs.foldl Nat.lcm 1) out := by
  exact word_exec _ M heap limit ptr xs hx (by omega) (by omega) hM
    (by omega) (by omega) hvals

theorem input_fits (capacity ptr : Nat) (heap : Heap) (hc : 0 < capacity)
    (hp : ptr < capacity) (hh : ∀ a, heap a < capacity) :
    Fits capacity (input ptr heap) := by
  refine ⟨hc,?_,hh⟩
  intro r
  simp only [input]
  split <;> assumption

end REWB.WordRAM.LCMFold
