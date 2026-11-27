import Std

/-! An explicit deterministic register machine. Each successful `step`
executes one instruction from a finite program. There are no host-function,
answer, or supplied-cost instructions. `Exec` counts those steps independently
of any algorithm ledger. `wordStep` is its checked finite-word version: a
transition traps if an accessed address or result does not fit the capacity.
The finite-word refinement lemmas require an actual state-size invariant;
they do not assert that every REWB execution already has that invariant. -/
namespace REWB.WordRAM

structure State where
  pc : Nat := 0
  regs : Nat → Nat
  heap : Nat → Nat
  halted : Bool := false

@[ext] theorem State.ext {s t : State} (hp : s.pc = t.pc)
    (hr : ∀ r, s.regs r = t.regs r) (hm : ∀ a, s.heap a = t.heap a)
    (hh : s.halted = t.halted) : s = t := by
  cases s
  cases t
  simp_all only
  congr
  · exact funext hr
  · exact funext hm

def State.writeReg (s : State) (dst value : Nat) : State :=
  { s with regs := fun r => if r = dst then value else s.regs r }

def State.writeMem (s : State) (addr value : Nat) : State :=
  { s with heap := fun a => if a = addr then value else s.heap a }

def State.next (s : State) : State := { s with pc := s.pc + 1 }

@[simp] theorem State.writeReg_same (s : State) (r v : Nat) :
    (s.writeReg r v).regs r = v := by simp [State.writeReg]

@[simp] theorem State.writeReg_other (s : State) (r q v : Nat) (h : q ≠ r) :
    (s.writeReg r v).regs q = s.regs q := by simp [State.writeReg,h]

@[simp] theorem State.writeMem_same (s : State) (a v : Nat) :
    (s.writeMem a v).heap a = v := by simp [State.writeMem]

@[simp] theorem State.writeMem_other (s : State) (a b v : Nat) (h : b ≠ a) :
    (s.writeMem a v).heap b = s.heap b := by simp [State.writeMem,h]

inductive Instr where
  | const (dst value : Nat)
  | mov (dst src : Nat)
  | add (dst lhs rhs : Nat)
  | sub (dst lhs rhs : Nat)
  | mul (dst lhs rhs : Nat)
  | div (dst lhs rhs : Nat)
  | mod (dst lhs rhs : Nat)
  | load (dst addr : Nat)
  | store (addr src : Nat)
  | jump (target : Nat)
  | jz (src target : Nat)
  | halt
  deriving Repr, DecidableEq

abbrev Program := Array Instr

def execInstr (i : Instr) (s : State) : State :=
  match i with
  | .const d v => (s.writeReg d v).next
  | .mov d a => (s.writeReg d (s.regs a)).next
  | .add d a b => (s.writeReg d (s.regs a + s.regs b)).next
  | .sub d a b => (s.writeReg d (s.regs a - s.regs b)).next
  | .mul d a b => (s.writeReg d (s.regs a * s.regs b)).next
  | .div d a b => (s.writeReg d (s.regs a / s.regs b)).next
  | .mod d a b => (s.writeReg d (s.regs a % s.regs b)).next
  | .load d a => (s.writeReg d (s.heap (s.regs a))).next
  | .store a b => (s.writeMem (s.regs a) (s.regs b)).next
  | .jump p => { s with pc := p }
  | .jz a p => if s.regs a = 0 then { s with pc := p } else s.next
  | .halt => { s with halted := true }

def step (p : Program) (s : State) : Option State :=
  if s.halted then none else
    match p[s.pc]? with
    | none => none
    | some i => some (execInstr i s)

inductive Exec (p : Program) : Nat → State → State → Prop where
  | refl (s : State) : Exec p 0 s s
  | step {n : Nat} {s t u : State} :
      WordRAM.step p s = some t → Exec p n t u → Exec p (n+1) s u

theorem Exec.one {p : Program} {s t : State} (h : WordRAM.step p s = some t) :
    Exec p 1 s t := Exec.step h (Exec.refl t)

theorem Exec.trans {p : Program} {m n : Nat} {s t u : State}
    (h₁ : Exec p m s t) (h₂ : Exec p n t u) : Exec p (m+n) s u := by
  induction h₁ with
  | refl => simpa using h₂
  | @step k a b c hab hbc ih =>
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Exec.step hab (ih h₂)

def runSteps (p : Program) : Nat → State → Option State
  | 0,s => some s
  | n+1,s => (step p s).bind (runSteps p n)

theorem exec_iff_runSteps (p : Program) (n : Nat) (s t : State) :
    Exec p n s t ↔ runSteps p n s = some t := by
  induction n generalizing s with
  | zero => constructor
            · intro h; cases h; rfl
            · intro h; simp only [runSteps,Option.some.injEq] at h; subst s; exact Exec.refl t
  | succ n ih =>
    constructor
    · intro h
      cases h with
      | step hst htu => simp only [runSteps,hst,Option.bind_some]; exact (ih _).mp htu
    · intro h
      cases hs : step p s with
      | none => simp [runSteps,hs] at h
      | some u =>
        simp only [runSteps,hs,Option.bind_some] at h
        exact Exec.step hs ((ih u).mpr h)

theorem Exec.deterministic {p : Program} {n : Nat} {s t u : State}
    (ht : Exec p n s t) (hu : Exec p n s u) : t = u := by
  have h := (exec_iff_runSteps p n s t).mp ht
  have g := (exec_iff_runSteps p n s u).mp hu
  exact Option.some.inj (h.symm.trans g)

theorem Exec.invariant {p : Program} {n : Nat} {s t : State}
    (h : Exec p n s t) (P : State → Prop) (hs : P s)
    (hstep : ∀ u v, P u → WordRAM.step p u = some v → P v) : P t := by
  induction h with
  | refl => exact hs
  | step huv _ ih => exact ih (hstep _ _ hs huv)

theorem halt_no_step (p : Program) (s : State) (h : s.halted = true) :
    step p s = none := by simp [step,h]

/-- Whole-state representability. Addresses generated by a load or store
are register values. The program's fixed register identifiers are code,
not data addresses. Capacity is normally `2^bits`. -/
def Fits (capacity : Nat) (s : State) : Prop :=
  s.pc < capacity ∧ (∀ r, s.regs r < capacity) ∧ ∀ a, s.heap a < capacity

/-- Finitely many words read or produced by this one instruction. -/
def touched (i : Instr) (s t : State) : List Nat :=
  [s.pc,t.pc] ++ match i with
  | .const d _ => [t.regs d]
  | .mov d a => [s.regs a,t.regs d]
  | .add d a b | .sub d a b | .mul d a b | .div d a b | .mod d a b =>
      [s.regs a,s.regs b,t.regs d]
  | .load d a => [s.regs a,s.heap (s.regs a),t.regs d]
  | .store a b => [s.regs a,s.regs b,t.heap (s.regs a)]
  | .jz a _ => [s.regs a]
  | .jump _ | .halt => []

def wordStep (capacity : Nat) (p : Program) (s : State) : Option State :=
  if s.halted then none else
    match p[s.pc]? with
    | none => none
    | some i =>
      let t := execInstr i s
      if (touched i s t).all (fun v => v < capacity) then some t else none

inductive WordExec (capacity : Nat) (p : Program) : Nat → State → State → Prop where
  | refl (s : State) : WordExec capacity p 0 s s
  | step {n : Nat} {s t u : State} :
      wordStep capacity p s = some t → WordExec capacity p n t u →
      WordExec capacity p (n+1) s u

theorem WordExec.one {capacity : Nat} {p : Program} {s t : State}
    (h : wordStep capacity p s = some t) : WordExec capacity p 1 s t :=
  WordExec.step h (WordExec.refl t)

theorem WordExec.trans {capacity : Nat} {p : Program} {m n : Nat} {s t u : State}
    (h₁ : WordExec capacity p m s t) (h₂ : WordExec capacity p n t u) :
    WordExec capacity p (m+n) s u := by
  induction h₁ with
  | refl => simpa using h₂
  | @step k a b c hab hbc ih =>
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using WordExec.step hab (ih h₂)

def runWordSteps (capacity : Nat) (p : Program) : Nat → State → Option State
  | 0,s => some s
  | n+1,s => (wordStep capacity p s).bind (runWordSteps capacity p n)

theorem wordExec_iff_runWordSteps (capacity : Nat) (p : Program) (n : Nat) (s t : State) :
    WordExec capacity p n s t ↔ runWordSteps capacity p n s = some t := by
  induction n generalizing s with
  | zero => constructor
            · intro h; cases h; rfl
            · intro h; simp only [runWordSteps,Option.some.injEq] at h
              subst s; exact WordExec.refl t
  | succ n ih =>
    constructor
    · intro h
      cases h with
      | step hst htu => simp only [runWordSteps,hst,Option.bind_some]; exact (ih _).mp htu
    · intro h
      cases hs : wordStep capacity p s with
      | none => simp [runWordSteps,hs] at h
      | some u =>
        simp only [runWordSteps,hs,Option.bind_some] at h
        exact WordExec.step hs ((ih u).mpr h)

theorem wordStep_refines {capacity : Nat} {p : Program} {s t : State}
    (h : wordStep capacity p s = some t) : step p s = some t := by
  unfold wordStep at h
  unfold step
  split at h
  · contradiction
  · rename_i hh
    rw [if_neg hh]
    split at h
    · contradiction
    · dsimp only at h
      split at h
      · exact h
      · contradiction

theorem execInstr_fits {capacity : Nat} (i : Instr) (s : State)
    (hs : Fits capacity s)
    (ht : ∀ v ∈ touched i s (execInstr i s), v < capacity) :
    Fits capacity (execInstr i s) := by
  rcases hs with ⟨hp,hr,hm⟩
  have hpc : (execInstr i s).pc < capacity := ht _ (by simp [touched])
  have hreg (d v : Nat) (hv : v < capacity) :
      ∀ r, (s.writeReg d v).regs r < capacity := by
    intro r
    by_cases h : r = d
    · simpa [State.writeReg,h] using hv
    · simpa [State.writeReg,h] using hr r
  have hmem (a v : Nat) (hv : v < capacity) :
      ∀ b, (s.writeMem a v).heap b < capacity := by
    intro b
    by_cases h : b = a
    · simpa [State.writeMem,h] using hv
    · simpa [State.writeMem,h] using hm b
  refine ⟨hpc, ?_⟩
  cases i with
  | const d v =>
    exact ⟨hreg d v (ht _ (by simp [touched,execInstr,State.next])),hm⟩
  | mov d a =>
    exact ⟨hreg d (s.regs a) (hr a),hm⟩
  | add d a b =>
    exact ⟨hreg d _ (ht _ (by simp [touched,execInstr,State.next])),hm⟩
  | sub d a b =>
    exact ⟨hreg d _ (ht _ (by simp [touched,execInstr,State.next])),hm⟩
  | mul d a b =>
    exact ⟨hreg d _ (ht _ (by simp [touched,execInstr,State.next])),hm⟩
  | div d a b =>
    exact ⟨hreg d _ (ht _ (by simp [touched,execInstr,State.next])),hm⟩
  | mod d a b =>
    exact ⟨hreg d _ (ht _ (by simp [touched,execInstr,State.next])),hm⟩
  | load d a =>
    exact ⟨hreg d _ (hm (s.regs a)),hm⟩
  | store a b => exact ⟨hr,hmem _ _ (hr b)⟩
  | jump target => exact ⟨hr,hm⟩
  | jz a target =>
    simp only [execInstr]
    split <;> exact ⟨hr,hm⟩
  | halt => exact ⟨hr,hm⟩

theorem wordStep_preservesFits {capacity : Nat} {p : Program} {s t : State}
    (h : wordStep capacity p s = some t) (hs : Fits capacity s) : Fits capacity t := by
  unfold wordStep at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · rename_i i hi
      dsimp only at h
      split at h
      · rename_i hall
        simp only [Option.some.injEq] at h
        subst t
        apply execInstr_fits i s hs
        intro v hv
        exact of_decide_eq_true (List.all_eq_true.mp hall v hv)
      · contradiction

theorem WordExec.toExec {capacity : Nat} {p : Program} {n : Nat} {s t : State}
    (h : WordExec capacity p n s t) : Exec p n s t := by
  induction h with
  | refl => exact Exec.refl _
  | step hst _ ih => exact Exec.step (wordStep_refines hst) ih

theorem WordExec.preservesFits {capacity : Nat} {p : Program} {n : Nat} {s t : State}
    (h : WordExec capacity p n s t) (hs : Fits capacity s) : Fits capacity t := by
  induction h with
  | refl => exact hs
  | step hst _ ih => exact ih (wordStep_preservesFits hst hs)

theorem WordExec.take {capacity : Nat} {p : Program} {n : Nat} {s t : State}
    (h : WordExec capacity p n s t) (k : Nat) (hk : k ≤ n) :
    ∃ u, WordExec capacity p k s u := by
  induction k generalizing n s with
  | zero => exact ⟨s,WordExec.refl s⟩
  | succ k ih =>
    cases h with
    | refl => omega
    | step hst htu =>
      obtain ⟨u,hu⟩ := ih htu (by omega)
      exact ⟨u,WordExec.step hst hu⟩

/-- Every natural-machine prefix of a successful checked run has a
representable whole state, provided the input state is representable. -/
theorem WordExec.prefixFits {capacity : Nat} {p : Program} {n k : Nat}
    {s t u : State} (h : WordExec capacity p n s t) (hs : Fits capacity s)
    (hk : k ≤ n) (hu : Exec p k s u) : Fits capacity u := by
  obtain ⟨v,hv⟩ := h.take k hk
  have he : v = u := hv.toExec.deterministic hu
  rw [← he]
  exact hv.preservesFits hs

theorem touched_lt (capacity : Nat) (i : Instr) (s t : State)
    (hs : Fits capacity s) (ht : Fits capacity t) :
    ∀ v ∈ touched i s t, v < capacity := by
  cases i <;> simp_all [touched,Fits]

theorem wordStep_of_fits {capacity : Nat} {p : Program} {s t : State}
    (h : step p s = some t) (hs : Fits capacity s) (ht : Fits capacity t) :
    wordStep capacity p s = some t := by
  unfold step at h
  unfold wordStep
  split at h
  · contradiction
  · rename_i hh
    rw [if_neg hh]
    split at h
    · contradiction
    · rename_i i hi
      simp only [Option.some.injEq] at h
      subst t
      have ha : (touched i s (execInstr i s)).all (fun v => decide (v < capacity)) = true :=
        List.all_eq_true.mpr (fun v hv => decide_eq_true (touched_lt capacity i s _ hs ht v hv))
      simp only [ha,if_true]

/-- A state-size invariant along every prefix transfers the actual
instruction trace to the checked finite-word semantics without changing
its length. The invariant must be proved for the concrete program. -/
theorem Exec.toWordExec {capacity : Nat} {p : Program} {n : Nat} {s t : State}
    (h : Exec p n s t)
    (hfit : ∀ k u, k ≤ n → Exec p k s u → Fits capacity u) :
    WordExec capacity p n s t := by
  induction h with
  | refl => exact WordExec.refl _
  | @step n s v t hsv hvt ih =>
    apply WordExec.step (wordStep_of_fits hsv
      (hfit 0 s (by omega) (Exec.refl s))
      (hfit 1 v (by omega) (Exec.one hsv)))
    apply ih
    intro k u hk hku
    apply hfit (k+1) u (by omega)
    exact Exec.step hsv hku

end REWB.WordRAM
