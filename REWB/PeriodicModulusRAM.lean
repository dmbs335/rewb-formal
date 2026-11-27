import REWB.ActualModulusRAM
import REWB.PeriodicModulusCalls

/-! The exact verified LCM subroutine lengths, summed over the actual
long-periodic constructor's calls, are bounded by its concrete ledger.
The multiplier depends on the fixed pattern only. This is the arithmetic
component of a simulation proof, not a whole-matcher execution theorem. -/
namespace REWB.PeriodicActual.FullCost.ModulusRAM
open REWB.ActualModulus
variable {σ : Nat}

theorem long_lcm_instructions (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n Q : Nat) :
    RAM.instructions (Calls.build (Long.prepare P f n Q).1.sources
      (Long.prepare P f n Q).1.targets).calls ≤
        (5*UniformPhaseBounds.p1Modulus P+6)*(Long.prepare P f n Q).2 := by
  have hb := RAM.observation_le _ _ (UniformPhaseBounds.p1Modulus_pos P)
    (ModulusCalls.long_divides P f n Q)
  exact Nat.le_trans hb (Nat.mul_le_mul_left _ (ModulusCalls.long_calls_le_work P f n Q))

/-- No modulus-compatibility premise is supplied by the caller: the bound
comes from the actual generated source and target entries. -/
theorem long_call_certificate (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n Q : Nat)
    (pair : Calls.Call)
    (hp : pair ∈ (Calls.build (Long.prepare P f n Q).1.sources
      (Long.prepare P f n Q).1.targets).calls) :
    WordRAM.Exec WordRAM.Arithmetic.lcmProgram
      (WordRAM.Arithmetic.lcmSteps pair.1 pair.2)
      (WordRAM.Arithmetic.lcmInput pair.1 pair.2)
      (WordRAM.Arithmetic.lcmOutput pair.1 pair.2) ∧
    WordRAM.Arithmetic.lcmSteps pair.1 pair.2 ≤ 5*UniformPhaseBounds.p1Modulus P+6 ∧
    (WordRAM.Arithmetic.lcmOutput pair.1 pair.2).regs 0 = Nat.lcm pair.1 pair.2 ∧
    (WordRAM.Arithmetic.lcmOutput pair.1 pair.2).halted = true :=
  ⟨WordRAM.Arithmetic.lcm_exec _ _,
    WordRAM.Arithmetic.lcmSteps_cap _ _ _ (ModulusCalls.long_operands P f n Q pair hp).1,
    WordRAM.Arithmetic.lcm_result _ _, WordRAM.Arithmetic.lcm_halts _ _⟩

/-- A finite power-of-two capacity is fixed by the pattern, before the
text and the call are selected. Every intermediate arithmetic operation
of the concrete LCM program is checked by `WordExec`. -/
theorem long_call_word_exec (P : SevenDFA (Fin σ)) (f : Nat → Fin σ) (n Q : Nat)
    (pair : Calls.Call)
    (hp : pair ∈ (Calls.build (Long.prepare P f n Q).1.sources
      (Long.prepare P f n Q).1.targets).calls) :
    WordRAM.WordExec (2^RAM.wordBits (UniformPhaseBounds.p1Modulus P))
      WordRAM.Arithmetic.lcmProgram (WordRAM.Arithmetic.lcmSteps pair.1 pair.2)
      (WordRAM.Arithmetic.lcmInput pair.1 pair.2)
      (WordRAM.Arithmetic.lcmOutput pair.1 pair.2) :=
  RAM.observation_word_exec _ _ (UniformPhaseBounds.p1Modulus_pos P)
    (ModulusCalls.long_divides P f n Q) pair hp

theorem long_word_bits (P : SevenDFA (Fin σ)) (n : Nat) :
    RAM.wordBits (UniformPhaseBounds.p1Modulus P) ≤
      RAM.wordBits (UniformPhaseBounds.p1Modulus P)*((n+2).log2+1) :=
  RAM.wordBits_le_log _ _

end REWB.PeriodicActual.FullCost.ModulusRAM
