import REWB.ActualModulusCalls
import REWB.WordRAMArithmeticWords

/-! Instruction costs for the LCM subroutine calls made by the installed
left-fold modulus construction. Each summand is the exact length of an
independently verified instruction trace, rather than a caller-supplied
price for `Nat.lcm`. The enclosing traversal is not claimed to have been
compiled by this module. -/
namespace REWB.ActualModulus.RAM
open WordRAM AffineProjection

def instructions (calls : List Calls.Call) : Nat :=
  (calls.map (fun pair => Arithmetic.lcmSteps pair.1 pair.2)).sum

theorem instructions_le (calls : List Calls.Call) (cap : Nat) :
    (∀ pair, pair ∈ calls → pair.1 ≤ cap) →
    instructions calls ≤ (5*cap+6)*calls.length := by
  induction calls with
  | nil => simp [instructions]
  | cons pair rest ih =>
    intro h
    have hpair := Arithmetic.lcmSteps_cap pair.1 pair.2 cap
      (h pair (List.mem_cons_self))
    have hrest := ih (fun item hi => h item (List.mem_cons_of_mem _ hi))
    change Arithmetic.lcmSteps pair.1 pair.2 + instructions rest ≤
      (5*cap+6)*(rest.length+1)
    rw [Nat.mul_add, Nat.mul_one]
    omega

/-- All observed primitive calls have concrete, exact-length, halting
machine runs computing their mathematical LCM. -/
theorem call_correct (pair : Calls.Call) :
    Exec Arithmetic.lcmProgram (Arithmetic.lcmSteps pair.1 pair.2)
      (Arithmetic.lcmInput pair.1 pair.2) (Arithmetic.lcmOutput pair.1 pair.2) ∧
    (Arithmetic.lcmOutput pair.1 pair.2).regs 0 = Nat.lcm pair.1 pair.2 ∧
    (Arithmetic.lcmOutput pair.1 pair.2).halted = true :=
  ⟨Arithmetic.lcm_exec _ _, Arithmetic.lcm_result _ _, Arithmetic.lcm_halts _ _⟩

/-- This fixed-cap width covers both operands, their product, the GCD,
the quotient, and all instruction addresses of the LCM program. -/
def wordBits (cap : Nat) : Nat := (cap*cap+cap+10).log2+1

theorem call_word_exec (pair : Calls.Call) (cap : Nat)
    (hm : pair.1 ≤ cap) (hn : pair.2 ≤ cap) :
    WordExec (2^wordBits cap) Arithmetic.lcmProgram
      (Arithmetic.lcmSteps pair.1 pair.2)
      (Arithmetic.lcmInput pair.1 pair.2) (Arithmetic.lcmOutput pair.1 pair.2) := by
  have hc : cap*cap+cap+10 < 2^wordBits cap := Nat.lt_log2_self
  have hprod : pair.1*pair.2 ≤ cap*cap := Nat.mul_le_mul hm hn
  exact Arithmetic.lcm_word_exec _ _ _ (by omega) (by omega) (by omega) (by omega)

theorem wordBits_le_log (cap n : Nat) :
    wordBits cap ≤ wordBits cap*((n+2).log2+1) := by
  simpa only [Nat.mul_one] using Nat.mul_le_mul_left (wordBits cap)
    (show 1 ≤ (n+2).log2+1 by omega)

theorem observation_word_exec (out : Calls.Observation) (M : Nat) (hM : 0 < M)
    (h : Calls.Divides M out) (pair : Calls.Call) (hp : pair ∈ out.calls) :
    WordExec (2^wordBits M) Arithmetic.lcmProgram
      (Arithmetic.lcmSteps pair.1 pair.2)
      (Arithmetic.lcmInput pair.1 pair.2) (Arithmetic.lcmOutput pair.1 pair.2) := by
  have hb := Calls.operands_le out M hM h pair hp
  exact call_word_exec pair M hb.1 hb.2

theorem observation_le (out : Calls.Observation) (M : Nat) (hM : 0 < M)
    (h : Calls.Divides M out) :
    instructions out.calls ≤ (5*M+6)*out.calls.length :=
  instructions_le out.calls M (fun pair hp => (Calls.operands_le out M hM h pair hp).1)

theorem row_le (C : Conj) (M : Nat) (hM : 0 < M)
    (h : ∀ a, a ∈ C → ActualModulus.AtomDivides M a) :
    instructions (Calls.row C).calls ≤ (5*M+6)*(ActualModulus.row C).2 := by
  have hb := observation_le _ M hM (Calls.row_divides C M hM h)
  rw [Calls.row_counter]
  exact Nat.le_trans hb (Nat.mul_le_mul_left _ (by omega))

theorem formula_le (F : Formula) (M : Nat) (hM : 0 < M)
    (h : ExponentIntervals.Compatible M F) :
    instructions (Calls.formula F).calls ≤ (5*M+6)*(ActualModulus.formula F).2 := by
  have hb := observation_le _ M hM (Calls.formula_divides F M hM h)
  rw [Calls.formula_counter]
  exact Nat.le_trans hb (Nat.mul_le_mul_left _ (by omega))

theorem entries_le (es : List TimedJoin.TimedEntry) (M : Nat) (hM : 0 < M)
    (h : TimedJoin.Good M es) :
    instructions (Calls.entries es).calls ≤ (5*M+6)*(ActualModulus.entries es).2 := by
  have hb := observation_le _ M hM (Calls.entries_divides es M hM h)
  rw [Calls.entries_counter]
  exact Nat.le_trans hb (Nat.mul_le_mul_left _ (by omega))

theorem build_le (es fs : List TimedJoin.TimedEntry) (M : Nat) (hM : 0 < M)
    (he : TimedJoin.Good M es) (hf : TimedJoin.Good M fs) :
    instructions (Calls.build es fs).calls ≤ (5*M+6)*(ActualModulus.build es fs).2 := by
  have hb := observation_le _ M hM (Calls.build_divides es fs M hM he hf)
  rw [Calls.build_counter]
  exact Nat.le_trans hb (Nat.mul_le_mul_left _ (by omega))

end REWB.ActualModulus.RAM
