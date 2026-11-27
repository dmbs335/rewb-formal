import REWB.ProjectionModulusCalls
import REWB.ActualModulusRAM

/-! Concrete arithmetic costs for the LCM calls in Cooper projection.
Every summand is the exact length of the verified Euclidean LCM program.
The operand cap is computed from a finite family of literal-erased
formulas. No machine-time bound is supplied by the caller.

This discharges the arithmetic primitive component only. Traversal,
formula representation, and whole-program control-flow simulation remain
separate obligations. -/
namespace REWB.ProjectionModulus.RAM
open REWB.AffineProjection REWB.UniformProjection

abbrev instructions := ActualModulus.RAM.instructions

theorem multiplier_instructions_erase (C : Conj) :
    instructions (Calls.multiplier C).calls=
      instructions (Calls.multiplier (LiteralShape.conj C)).calls := by
  rw [Calls.multiplier_erase]

theorem commonPeriod_instructions_erase (gs : List Guard) :
    instructions (Calls.commonPeriod gs).calls=
      instructions (Calls.commonPeriod (gs.map LiteralShape.guard)).calls := by
  rw [Calls.commonPeriod_erase]

theorem project_instructions_shape (k : Nat) (F G : Formula)
    (h : LiteralShape.formula F=LiteralShape.formula G) :
    instructions (Calls.project k F)=instructions (Calls.project k G) := by
  rw [Calls.project_shape k F G h]

theorem searchAll_instructions_shape (k : Nat) (F G : Formula)
    (h : LiteralShape.formula F=LiteralShape.formula G) :
    instructions (Calls.searchAll k F)=instructions (Calls.searchAll k G) := by
  rw [Calls.searchAll_shape k F G h]

theorem project_instructions (k : Nat) (F : Formula) (fs : Family) (h : Covered F fs) :
    instructions (Calls.project k F)≤
      (5*Calls.familyCap k fs+6)*(CountedProjection.project k F).2 := by
  have hb := ActualModulus.RAM.instructions_le (Calls.project k F) (Calls.familyCap k fs)
    (fun pair hp => (Calls.project_operands k F fs h pair hp).1)
  exact Nat.le_trans hb (Nat.mul_le_mul_left _ (Calls.project_length_le k F))

/-- The actual short-circuit call count is charged to its actual counter,
while only operand sizes use the unpruned shape-family bound. -/
theorem search_instructions (env : List Int) (k : Nat) (F : Formula) (fs : Family)
    (h : Covered F fs) : instructions (Calls.search env k F)≤
      (5*Calls.familyCap k fs+6)*(CountedProjection.search env k F).2 := by
  have hb := ActualModulus.RAM.instructions_le (Calls.search env k F) (Calls.familyCap k fs)
    (fun pair hp => (Calls.search_operands env k F fs h pair hp).1)
  exact Nat.le_trans hb (Nat.mul_le_mul_left _ (Calls.search_length_le env k F))

def wordBits (k : Nat) (fs : Family) : Nat := ActualModulus.RAM.wordBits (Calls.familyCap k fs)

theorem wordBits_le_log (k : Nat) (fs : Family) (n : Nat) :
    wordBits k fs≤wordBits k fs*((n+2).log2+1) :=
  ActualModulus.RAM.wordBits_le_log _ _

theorem project_call_word_exec (k : Nat) (F : Formula) (fs : Family) (h : Covered F fs)
    (pair : Calls.Call) (hp : pair∈Calls.project k F) :
    WordRAM.WordExec (2^wordBits k fs) WordRAM.Arithmetic.lcmProgram
      (WordRAM.Arithmetic.lcmSteps pair.1 pair.2)
      (WordRAM.Arithmetic.lcmInput pair.1 pair.2) (WordRAM.Arithmetic.lcmOutput pair.1 pair.2) := by
  have hb := Calls.project_operands k F fs h pair hp
  exact ActualModulus.RAM.call_word_exec pair (Calls.familyCap k fs) hb.1 hb.2

theorem search_call_word_exec (env : List Int) (k : Nat) (F : Formula) (fs : Family)
    (h : Covered F fs) (pair : Calls.Call) (hp : pair∈Calls.search env k F) :
    WordRAM.WordExec (2^wordBits k fs) WordRAM.Arithmetic.lcmProgram
      (WordRAM.Arithmetic.lcmSteps pair.1 pair.2)
      (WordRAM.Arithmetic.lcmInput pair.1 pair.2) (WordRAM.Arithmetic.lcmOutput pair.1 pair.2) := by
  have hb := Calls.search_operands env k F fs h pair hp
  exact ActualModulus.RAM.call_word_exec pair (Calls.familyCap k fs) hb.1 hb.2

theorem project_call_certificate (k : Nat) (F : Formula) (fs : Family) (h : Covered F fs)
    (pair : Calls.Call) (hp : pair∈Calls.project k F) :
    WordRAM.WordExec (2^wordBits k fs) WordRAM.Arithmetic.lcmProgram
      (WordRAM.Arithmetic.lcmSteps pair.1 pair.2)
      (WordRAM.Arithmetic.lcmInput pair.1 pair.2) (WordRAM.Arithmetic.lcmOutput pair.1 pair.2) ∧
    WordRAM.Arithmetic.lcmSteps pair.1 pair.2≤5*Calls.familyCap k fs+6 ∧
    (WordRAM.Arithmetic.lcmOutput pair.1 pair.2).regs 0=Nat.lcm pair.1 pair.2 ∧
    (WordRAM.Arithmetic.lcmOutput pair.1 pair.2).halted=true :=
  ⟨project_call_word_exec k F fs h pair hp,
    WordRAM.Arithmetic.lcmSteps_cap _ _ _ (Calls.project_operands k F fs h pair hp).1,
    WordRAM.Arithmetic.lcm_result _ _,WordRAM.Arithmetic.lcm_halts _ _⟩

theorem search_call_certificate (env : List Int) (k : Nat) (F : Formula) (fs : Family)
    (h : Covered F fs) (pair : Calls.Call) (hp : pair∈Calls.search env k F) :
    WordRAM.WordExec (2^wordBits k fs) WordRAM.Arithmetic.lcmProgram
      (WordRAM.Arithmetic.lcmSteps pair.1 pair.2)
      (WordRAM.Arithmetic.lcmInput pair.1 pair.2) (WordRAM.Arithmetic.lcmOutput pair.1 pair.2) ∧
    WordRAM.Arithmetic.lcmSteps pair.1 pair.2≤5*Calls.familyCap k fs+6 ∧
    (WordRAM.Arithmetic.lcmOutput pair.1 pair.2).regs 0=Nat.lcm pair.1 pair.2 ∧
    (WordRAM.Arithmetic.lcmOutput pair.1 pair.2).halted=true :=
  ⟨search_call_word_exec env k F fs h pair hp,
    WordRAM.Arithmetic.lcmSteps_cap _ _ _ (Calls.search_operands env k F fs h pair hp).1,
    WordRAM.Arithmetic.lcm_result _ _,WordRAM.Arithmetic.lcm_halts _ _⟩

end REWB.ProjectionModulus.RAM
