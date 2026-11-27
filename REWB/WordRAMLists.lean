import REWB.WordRAM
import REWB.WordRAMListHeap

/-! A fixed RAM program for a fresh, two-cell copying reverse traversal.
Its control flow reads the source links from memory and stops at null.
No list length, answer, or cost is a machine input. The list appearing in
the theorem describes the input heap and supplies the induction proof. -/
namespace REWB.WordRAM.Lists
open ListHeap

def loopCode (entry exit : Nat) : Array Instr := #[
  .jz 0 exit, .load 3 0, .add 5 0 6, .load 4 5,
  .store 2 3, .add 5 2 6, .store 5 1, .mov 1 2,
  .add 2 2 7, .mov 0 4, .jump entry]

def HasLoop (p : Program) (entry exit : Nat) : Prop :=
  ∀ i : Fin 11, p[entry+i.val]? = (loopCode entry exit)[i.val]?

def round (entry : Nat) (s : State) : State := {
  pc := entry
  regs := fun r =>
    if r = 0 then s.heap (s.regs 0+1)
    else if r = 2 then s.regs 2+2
    else if r = 1 then s.regs 2
    else if r = 5 then s.regs 2+1
    else if r = 4 then s.heap (s.regs 0+1)
    else if r = 3 then s.heap (s.regs 0)
    else s.regs r
  heap := push s.heap (s.regs 2) (s.heap (s.regs 0)) (s.regs 1)
  halted := s.halted }

def iterate (entry : Nat) (s : State) : List Nat → State
  | [] => s
  | _::xs => iterate entry (round entry s) xs

def leave (exit : Nat) (s : State) : State := {s with pc := exit}

theorem round_exec (p : Program) (entry exit : Nat) (s : State)
    (hc : HasLoop p entry exit) (hp : s.pc = entry) (hh : s.halted = false)
    (hz : s.regs 0 ≠ 0) (h₁ : s.regs 6 = 1) (h₂ : s.regs 7 = 2) :
    Exec p 11 s (round entry s) := by
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
  apply (exec_iff_runSteps p 11 s (round entry s)).mpr
  simp [runSteps,step,execInstr,State.writeReg,State.writeMem,State.next,
    hp,hh,hz,h₁,h₂,c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,Nat.add_assoc,round,push]
  constructor
  · funext r
    by_cases h5 : r = 5 <;> simp [h5]
  · rfl

theorem leave_exec (p : Program) (entry exit : Nat) (s : State)
    (hc : HasLoop p entry exit) (hp : s.pc = entry) (hh : s.halted = false)
    (hz : s.regs 0 = 0) : Exec p 1 s (leave exit s) := by
  apply Exec.one
  have h := hc ⟨0,by decide⟩
  simp [loopCode] at h
  simp [step,hp,hh,h,execInstr,hz,leave]

theorem round_source {entry : Nat} {s : State} {x : Nat} {xs : List Nat}
    (hx : ListAt s.heap (s.regs 2) (s.regs 0) (x::xs)) :
    ListAt (round entry s).heap ((round entry s).regs 2) ((round entry s).regs 0) xs := by
  obtain ⟨q,hp,ha,hv,hn,ht⟩ := hx.cons_fields
  simp only [round,ite_true,show (0:Nat) ≠ 2 by decide,if_false,show (2:Nat) ≠ 0 by decide]
  rw [hn]
  exact (ht.frame (fun i hi => push_below s.heap (s.regs 2)
    (s.heap (s.regs 0)) (s.regs 1) i hi)).mono (by omega)

theorem loop_exec (p : Program) (entry exit : Nat) (s : State) (xs : List Nat)
    (hc : HasLoop p entry exit) (hp : s.pc = entry) (hh : s.halted = false)
    (h₁ : s.regs 6 = 1) (h₂ : s.regs 7 = 2)
    (hx : ListAt s.heap (s.regs 2) (s.regs 0) xs) :
    Exec p (11*xs.length+1) s (leave exit (iterate entry s xs)) := by
  induction xs generalizing s with
  | nil =>
    simpa [iterate] using leave_exec p entry exit s hc hp hh hx.nil_pointer
  | cons x xs ih =>
    have hz : s.regs 0 ≠ 0 := by obtain ⟨q,h,_,_,_,_⟩ := hx.cons_fields; omega
    have hr := round_exec p entry exit s hc hp hh hz h₁ h₂
    have ht := ih (round entry s) rfl (by simpa [round] using hh)
      (by simpa [round] using h₁) (by simpa [round] using h₂) (round_source hx)
    have h := hr.trans ht
    simpa only [iterate,show 11+(11*xs.length+1) = 11*(x::xs).length+1 by
      simp only [List.length_cons]; omega] using h

theorem iterate_heap (entry : Nat) (s : State) (xs : List Nat)
    (hx : ListAt s.heap (s.regs 2) (s.regs 0) xs) :
    (iterate entry s xs).heap = (copyReverse s.heap (s.regs 2) (s.regs 1) xs).heap ∧
    (iterate entry s xs).regs 1 = (copyReverse s.heap (s.regs 2) (s.regs 1) xs).pointer ∧
    (iterate entry s xs).regs 2 = (copyReverse s.heap (s.regs 2) (s.regs 1) xs).frontier := by
  induction xs generalizing s with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons x xs ih =>
    have hv : s.heap (s.regs 0) = x := by
      obtain ⟨_,_,_,hv,_,_⟩ := hx.cons_fields
      exact hv
    have h := ih (round entry s) (round_source hx)
    simpa [iterate,copyReverse,round,hv] using h

theorem iterate_rep (entry : Nat) (s : State) (xs ys : List Nat)
    (hf : 0 < s.regs 2)
    (hx : ListAt s.heap (s.regs 2) (s.regs 0) xs)
    (hy : ListAt s.heap (s.regs 2) (s.regs 1) ys) :
    ListAt (iterate entry s xs).heap ((iterate entry s xs).regs 2)
      ((iterate entry s xs).regs 1) (xs.reverse++ys) := by
  obtain ⟨hh,hp,hf'⟩ := iterate_heap entry s xs hx
  rw [hh,hp,hf']
  exact copyReverse_rep hf hy xs

theorem iterate_frontier (entry : Nat) (s : State) (xs : List Nat)
    (hx : ListAt s.heap (s.regs 2) (s.regs 0) xs) :
    (iterate entry s xs).regs 2 = s.regs 2+2*xs.length := by
  rw [(iterate_heap entry s xs hx).2.2,copyReverse_frontier]

theorem iterate_frame (entry : Nat) (s : State) (xs : List Nat)
    (hx : ListAt s.heap (s.regs 2) (s.regs 0) xs) (i : Nat) (hi : i < s.regs 2) :
    (iterate entry s xs).heap i = s.heap i := by
  rw [(iterate_heap entry s xs hx).1]
  exact copyReverse_below s.heap (s.regs 2) (s.regs 1) xs i hi

def reverseProgram : Program := #[
  .const 6 1,.const 7 2,
  .jz 0 13,.load 3 0,.add 5 0 6,.load 4 5,
  .store 2 3,.add 5 2 6,.store 5 1,.mov 1 2,
  .add 2 2 7,.mov 0 4,.jump 2,.halt]

theorem reverseProgram_hasLoop : HasLoop reverseProgram 2 13 := by
  unfold HasLoop
  decide

def setup (s : State) : State :=
  { (s.writeReg 6 1).writeReg 7 2 with pc := 2 }

def finish (s : State) : State := {s with pc := 13,halted := true}

def reverseResult (s : State) (xs : List Nat) : State :=
  finish (iterate 2 (setup s) xs)

theorem setup_exec (s : State) (hp : s.pc = 0) (hh : s.halted = false) :
    Exec reverseProgram 2 s (setup s) := by
  apply (exec_iff_runSteps _ _ _ _).mpr
  simp [runSteps,step,reverseProgram,execInstr,State.writeReg,State.next,hp,hh,setup]

theorem iterate_halted (entry : Nat) (s : State) (xs : List Nat) :
    (iterate entry s xs).halted = s.halted := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => exact ih (round entry s)

theorem iterate_aux_reg (entry : Nat) (s : State) (xs : List Nat)
    (r : Nat) (hr : 6 ≤ r) : (iterate entry s xs).regs r = s.regs r := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    rw [iterate,ih]
    simp [round,show r ≠ 0 by omega,show r ≠ 1 by omega,
      show r ≠ 2 by omega,show r ≠ 3 by omega,show r ≠ 4 by omega,
      show r ≠ 5 by omega]

theorem reverse_exec (s : State) (xs : List Nat) (hp : s.pc = 0)
    (hh : s.halted = false) (hx : ListAt s.heap (s.regs 2) (s.regs 0) xs) :
    Exec reverseProgram (11*xs.length+4) s (reverseResult s xs) := by
  have hstart := setup_exec s hp hh
  have hlo := loop_exec reverseProgram 2 13 (setup s) xs reverseProgram_hasLoop rfl
    (by simpa [setup,State.writeReg] using hh)
    (by simp [setup,State.writeReg]) (by simp [setup,State.writeReg])
    (by simpa [setup,State.writeReg] using hx)
  have hend : Exec reverseProgram 1 (leave 13 (iterate 2 (setup s) xs)) (reverseResult s xs) := by
    apply Exec.one
    simp [step,reverseProgram,leave,iterate_halted,setup,State.writeReg,hh,
      execInstr,reverseResult,finish]
  have h := hstart.trans (hlo.trans hend)
  simpa only [show 2+(11*xs.length+1+1) = 11*xs.length+4 by omega] using h

theorem reverse_result_rep (s : State) (xs ys : List Nat)
    (hf : 0 < s.regs 2)
    (hx : ListAt s.heap (s.regs 2) (s.regs 0) xs)
    (hy : ListAt s.heap (s.regs 2) (s.regs 1) ys) :
    ListAt (reverseResult s xs).heap ((reverseResult s xs).regs 2)
      ((reverseResult s xs).regs 1) (xs.reverse++ys) := by
  simpa [reverseResult,finish,setup,State.writeReg] using
    iterate_rep 2 (setup s) xs ys (by simpa [setup,State.writeReg] using hf)
      (by simpa [setup,State.writeReg] using hx) (by simpa [setup,State.writeReg] using hy)

theorem reverse_result_frontier (s : State) (xs : List Nat)
    (hx : ListAt s.heap (s.regs 2) (s.regs 0) xs) :
    (reverseResult s xs).regs 2 = s.regs 2+2*xs.length := by
  simpa [reverseResult,finish,setup,State.writeReg] using
    iterate_frontier 2 (setup s) xs (by simpa [setup,State.writeReg] using hx)

theorem reverse_result_frame (s : State) (xs : List Nat)
    (hx : ListAt s.heap (s.regs 2) (s.regs 0) xs) (i : Nat) (hi : i < s.regs 2) :
    (reverseResult s xs).heap i = s.heap i := by
  exact iterate_frame 2 (setup s) xs
    (by simpa [setup,State.writeReg] using hx) i (by simpa [setup,State.writeReg] using hi)

end REWB.WordRAM.Lists
