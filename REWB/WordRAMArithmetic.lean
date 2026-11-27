import REWB.WordRAM

/-! Concrete Euclidean GCD/LCM instruction programs. The step functions
below count the independently defined machine trace, not a caller's cost
annotation. Fixed operand caps give fixed-pattern bounds. -/
namespace REWB.WordRAM.Arithmetic

def registers (m n tmp : Nat) (rest : Nat → Nat) : Nat → Nat :=
  fun r => if r = 0 then m else if r = 1 then n else if r = 2 then tmp else rest r

def frame (pc m n tmp : Nat) (heap rest : Nat → Nat) : State :=
  ⟨pc,registers m n tmp rest,heap,false⟩

def gcdProgram : Program :=
  #[.jz 0 5,.mod 2 1 0,.mov 1 0,.mov 0 2,.jump 0,.halt]

def lcmProgram : Program :=
  #[.mov 3 0,.mov 4 1,.jz 0 7,.mod 2 1 0,.mov 1 0,.mov 0 2,.jump 2,
    .mul 0 3 4,.div 0 0 1,.halt]

def LoopAt (p : Program) (pc : Nat) : Prop :=
  p[pc]? = some (.jz 0 (pc+5)) ∧
  p[pc+1]? = some (.mod 2 1 0) ∧
  p[pc+2]? = some (.mov 1 0) ∧
  p[pc+3]? = some (.mov 0 2) ∧
  p[pc+4]? = some (.jump pc)

def gcdLoopSteps (m n : Nat) : Nat :=
  if hm : m = 0 then 1 else gcdLoopSteps (n % m) m + 5
termination_by m
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero hm)

def gcdSteps (m n : Nat) : Nat := gcdLoopSteps m n + 1
def lcmSteps (m n : Nat) : Nat := gcdLoopSteps m n + 5

theorem loop_zero (p : Program) (pc n tmp : Nat) (heap rest : Nat → Nat)
    (h : LoopAt p pc) :
    Exec p 1 (frame pc 0 n tmp heap rest) (frame (pc+5) 0 n tmp heap rest) := by
  apply Exec.one
  simp [step,frame,registers,execInstr,h.1]

theorem loop_five (p : Program) (pc m n tmp : Nat) (heap rest : Nat → Nat)
    (h : LoopAt p pc) (hm : m ≠ 0) :
    Exec p 5 (frame pc m n tmp heap rest)
      (frame pc (n%m) m (n%m) heap rest) := by
  apply (exec_iff_runSteps _ _ _ _).mpr
  rcases h with ⟨h0,h1,h2,h3,h4⟩
  simp [runSteps,step,frame,registers,execInstr,State.writeReg,State.next,
    h0,h1,h2,h3,h4,hm,Nat.add_assoc]
  funext r
  by_cases h0 : r=0 <;> by_cases h1 : r=1 <;> by_cases h2 : r=2 <;>
    simp_all [registers]

theorem gcd_loop (p : Program) (pc m n tmp : Nat) (heap rest : Nat → Nat)
    (h : LoopAt p pc) :
    Exec p (gcdLoopSteps m n) (frame pc m n tmp heap rest)
      (frame (pc+5) 0 (Nat.gcd m n) (if m=0 then tmp else 0) heap rest) := by
  induction m using Nat.strongRecOn generalizing n tmp with
  | ind m ih =>
    by_cases hm : m=0
    · subst m
      simpa [gcdLoopSteps] using loop_zero p pc n tmp heap rest h
    · have hr := Nat.mod_lt n (Nat.pos_of_ne_zero hm)
      have ht := (loop_five p pc m n tmp heap rest h hm).trans
        (ih (n%m) hr m (n%m))
      have hz : (if n%m=0 then n%m else 0)=0 := by split <;> simp_all
      have hg : Nat.gcd m n = Nat.gcd (n%m) m := by rw [Nat.gcd_def]; simp [hm]
      rw [gcdLoopSteps]
      simp only [dif_neg hm,if_neg hm,hg]
      simpa only [hz,Nat.add_comm] using ht

theorem gcdLoopSteps_bound (m n : Nat) : gcdLoopSteps m n ≤ 5*m+1 := by
  induction m using Nat.strongRecOn generalizing n with
  | ind m ih =>
    rw [gcdLoopSteps]
    split
    · omega
    · rename_i hm
      have hr := Nat.mod_lt n (Nat.pos_of_ne_zero hm)
      have ht := ih (n%m) hr m
      omega

theorem gcdSteps_bound (m n : Nat) : gcdSteps m n ≤ 5*m+2 := by
  have h := gcdLoopSteps_bound m n
  unfold gcdSteps
  omega

theorem lcmSteps_bound (m n : Nat) : lcmSteps m n ≤ 5*m+6 := by
  have h := gcdLoopSteps_bound m n
  unfold lcmSteps
  omega

theorem lcmSteps_cap (m n cap : Nat) (hm : m ≤ cap) : lcmSteps m n ≤ 5*cap+6 := by
  have h := lcmSteps_bound m n
  omega

theorem gcd_loop_at : LoopAt gcdProgram 0 := by unfold LoopAt gcdProgram; decide
theorem lcm_loop_at : LoopAt lcmProgram 2 := by unfold LoopAt lcmProgram; decide

def gcdInput (m n : Nat) : State := frame 0 m n 0 (fun _=>0) (fun _=>0)
def gcdOutput (m n : Nat) : State :=
  { frame 5 0 (Nat.gcd m n) 0 (fun _=>0) (fun _=>0) with halted := true }

theorem gcd_exec (m n : Nat) : Exec gcdProgram (gcdSteps m n) (gcdInput m n) (gcdOutput m n) := by
  have h := gcd_loop gcdProgram 0 m n 0 (fun _=>0) (fun _=>0) gcd_loop_at
  have e : Exec gcdProgram 1 (frame 5 0 (Nat.gcd m n) 0 (fun _=>0) (fun _=>0))
      (gcdOutput m n) := by
    apply Exec.one
    simp [step,gcdProgram,frame,gcdOutput,execInstr]
  simp only [ite_self,Nat.zero_add] at h
  exact h.trans e

theorem gcd_result (m n : Nat) : (gcdOutput m n).regs 1 = Nat.gcd m n := by
  simp [gcdOutput,frame,registers]

theorem gcd_halts (m n : Nat) : (gcdOutput m n).halted = true := rfl

def saved (m n : Nat) : Nat → Nat :=
  fun r => if r=4 then n else if r=3 then m else 0

def lcmInput (m n : Nat) : State := frame 0 m n 0 (fun _=>0) (fun _=>0)
def lcmOutput (m n : Nat) : State :=
  { frame 9 (Nat.lcm m n) (Nat.gcd m n) 0 (fun _=>0) (saved m n) with halted := true }

theorem lcm_prefix (m n : Nat) :
    Exec lcmProgram 2 (lcmInput m n) (frame 2 m n 0 (fun _=>0) (saved m n)) := by
  apply (exec_iff_runSteps _ _ _ _).mpr
  simp [runSteps,step,lcmProgram,lcmInput,frame,registers,execInstr,State.writeReg,State.next,saved]
  funext r
  by_cases h0 : r=0 <;> by_cases h1 : r=1 <;> by_cases h2 : r=2 <;>
    by_cases h3 : r=3 <;> by_cases h4 : r=4 <;> simp_all [registers,saved]

theorem lcm_suffix (m n : Nat) :
    Exec lcmProgram 3 (frame 7 0 (Nat.gcd m n) 0 (fun _=>0) (saved m n)) (lcmOutput m n) := by
  apply (exec_iff_runSteps _ _ _ _).mpr
  simp [runSteps,step,lcmProgram,frame,registers,execInstr,State.writeReg,State.next,saved,
    lcmOutput,Nat.lcm]
  funext r
  by_cases h0 : r=0 <;> by_cases h1 : r=1 <;> by_cases h2 : r=2 <;>
    by_cases h3 : r=3 <;> by_cases h4 : r=4 <;> simp_all [registers,saved]

theorem lcm_exec (m n : Nat) : Exec lcmProgram (lcmSteps m n) (lcmInput m n) (lcmOutput m n) := by
  have h := gcd_loop lcmProgram 2 m n 0 (fun _=>0) (saved m n) lcm_loop_at
  simp only [ite_self] at h
  have out := ((lcm_prefix m n).trans h).trans (lcm_suffix m n)
  have he : (2+gcdLoopSteps m n)+3=lcmSteps m n := by unfold lcmSteps; omega
  rw [he] at out
  exact out

theorem lcm_result (m n : Nat) : (lcmOutput m n).regs 0 = Nat.lcm m n := by
  simp [lcmOutput,frame,registers]

theorem lcm_halts (m n : Nat) : (lcmOutput m n).halted = true := rfl

end REWB.WordRAM.Arithmetic
