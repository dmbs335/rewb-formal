import REWB.WordRAMArithmetic
import REWB.WordRAMListHeap

/-! A single executable RAM program folds LCM over a null-terminated
two-cell linked list. The program receives a pointer and a heap, initializes
its accumulator to one, and discovers the end by loading successor links.
The logical list and its length occur only in the specification and proof.
The Euclidean inner loop is actual code at PC 7, not a host-function call. -/
namespace REWB.WordRAM.LCMFold

open Arithmetic ListHeap

def program : Program :=
  #[.const 7 1,.const 8 1,.jz 5 17,.mov 0 8,.load 1 5,.mov 3 0,.mov 4 1,
    .jz 0 12,.mod 2 1 0,.mov 1 0,.mov 0 2,.jump 7,
    .mul 0 3 4,.div 8 0 1,.add 6 5 7,.load 5 6,.jump 2,.halt]

def extras (a b ptr addr acc : Nat) (rest : Nat → Nat) : Nat → Nat :=
  fun r => if r=3 then a else if r=4 then b else if r=5 then ptr else
    if r=6 then addr else if r=7 then 1 else if r=8 then acc else rest r

def state (pc m n tmp a b ptr addr acc : Nat) (heap rest : Nat → Nat) : State :=
  frame pc m n tmp heap (extras a b ptr addr acc rest)

def input (ptr : Nat) (heap : Heap) : State :=
  ⟨0,(fun r => if r=5 then ptr else 0),heap,false⟩

def loopSteps (acc : Nat) : List Nat → Nat
  | [] => 2
  | x::xs => gcdLoopSteps acc x + 10 + loopSteps (Nat.lcm acc x) xs

def steps (xs : List Nat) : Nat := 2 + loopSteps 1 xs

def Result (heap : Heap) (value : Nat) (s : State) : Prop :=
  s.regs 8 = value ∧ s.regs 5 = 0 ∧ s.halted = true ∧ s.heap = heap

theorem loop_at : LoopAt program 7 := by unfold LoopAt program; decide

theorem nodePrefix (m n tmp a b ptr addr acc x : Nat) (heap rest : Nat → Nat)
    (hp : ptr ≠ 0) (hx : heap ptr = x) :
    Exec program 5 (state 2 m n tmp a b ptr addr acc heap rest)
      (state 7 acc x tmp acc x ptr addr acc heap rest) := by
  apply (exec_iff_runSteps _ _ _ _).mpr
  simp [runSteps,step,program,state,frame,registers,extras,execInstr,
    State.writeReg,State.next,hp,hx]
  funext r
  by_cases h0 : r=0 <;> simp_all [registers,extras]
  by_cases h1 : r=1 <;> simp_all [registers,extras]
  by_cases h2 : r=2 <;> simp_all [registers,extras]
  by_cases h3 : r=3 <;> simp_all [registers,extras]

theorem suffix (acc x tmp ptr addr q : Nat) (heap rest : Nat → Nat)
    (hq : heap (ptr+1) = q) :
    Exec program 5 (state 12 0 (Nat.gcd acc x) tmp acc x ptr addr acc heap rest)
      (state 2 (acc*x) (Nat.gcd acc x) tmp acc x q (ptr+1)
        (Nat.lcm acc x) heap rest) := by
  apply (exec_iff_runSteps _ _ _ _).mpr
  simp [runSteps,step,program,state,frame,registers,extras,execInstr,
    State.writeReg,State.next,hq,Nat.lcm]
  funext r
  by_cases h0 : r=0 <;> simp_all [registers,extras]
  by_cases h1 : r=1 <;> simp_all [registers,extras]
  by_cases h2 : r=2 <;> simp_all [registers,extras]
  by_cases h3 : r=3 <;> simp_all [registers,extras]
  by_cases h4 : r=4 <;> simp_all [registers,extras]
  by_cases h5 : r=5 <;> simp_all [registers,extras]
  by_cases h6 : r=6 <;> simp_all [registers,extras]
  by_cases h7 : r=7 <;> simp_all [registers,extras]

theorem exit (m n tmp a b addr acc : Nat) (heap rest : Nat → Nat) :
    Exec program 2 (state 2 m n tmp a b 0 addr acc heap rest)
      {state 17 m n tmp a b 0 addr acc heap rest with halted := true} := by
  apply (exec_iff_runSteps _ _ _ _).mpr
  simp [runSteps,step,program,state,frame,registers,extras,execInstr]

theorem startup (ptr : Nat) (heap : Heap) :
    Exec program 2 (input ptr heap)
      (state 2 0 0 0 0 0 ptr 0 1 heap (fun _=>0)) := by
  apply (exec_iff_runSteps _ _ _ _).mpr
  simp [runSteps,step,program,input,state,frame,registers,extras,execInstr,
    State.writeReg,State.next]
  funext r
  by_cases h0 : r=0 <;> simp_all [registers,extras]
  by_cases h1 : r=1 <;> simp_all [registers,extras]
  by_cases h2 : r=2 <;> simp_all [registers,extras]
  by_cases h3 : r=3 <;> simp_all [registers,extras]
  by_cases h4 : r=4 <;> simp_all [registers,extras]
  by_cases h5 : r=5 <;> simp_all [registers,extras]
  by_cases h6 : r=6 <;> simp_all [registers,extras]
  by_cases h7 : r=7 <;> simp_all [registers,extras]

theorem loop_exec (heap rest : Nat → Nat) (limit ptr : Nat) (xs : List Nat)
    (hx : ListAt heap limit ptr xs) (m n tmp a b addr acc : Nat) :
    ∃ out, Exec program (loopSteps acc xs)
      (state 2 m n tmp a b ptr addr acc heap rest) out ∧
      Result heap (xs.foldl Nat.lcm acc) out := by
  induction xs generalizing ptr m n tmp a b addr acc with
  | nil =>
    have hp := hx.nil_pointer
    subst ptr
    refine ⟨{state 17 m n tmp a b 0 addr acc heap rest with halted:=true},
      exit m n tmp a b addr acc heap rest, ?_⟩
    simp [Result,state,frame,registers,extras]
  | cons x xs ih =>
    obtain ⟨q,hp,ha,hv,hn,ht⟩ := hx.cons_fields
    obtain ⟨out,he,hr⟩ := ih q ht (acc*x) (Nat.gcd acc x)
      (if acc=0 then tmp else 0) acc x (ptr+1) (Nat.lcm acc x)
    have hpre := nodePrefix m n tmp a b ptr addr acc x heap rest (by omega) hv
    have hg := gcd_loop program 7 acc x tmp heap (extras acc x ptr addr acc rest) loop_at
    have hs := suffix acc x (if acc=0 then tmp else 0) ptr addr q heap rest hn
    have hall := ((hpre.trans hg).trans hs).trans he
    refine ⟨out, ?_, ?_⟩
    · have hc : (5+gcdLoopSteps acc x)+5+loopSteps (Nat.lcm acc x) xs =
          loopSteps acc (x::xs) := by simp only [loopSteps]; omega
      rw [hc] at hall
      exact hall
    · simpa using hr

theorem exec (heap : Heap) (limit ptr : Nat) (xs : List Nat)
    (hx : ListAt heap limit ptr xs) :
    ∃ out, Exec program (steps xs) (input ptr heap) out ∧
      Result heap (xs.foldl Nat.lcm 1) out := by
  obtain ⟨out,he,hr⟩ := loop_exec heap (fun _=>0) limit ptr xs hx 0 0 0 0 0 0 1
  exact ⟨out,(startup ptr heap).trans he,hr⟩

theorem loopSteps_cap (M acc : Nat) (xs : List Nat) (hM : 0 < M)
    (ha : acc ∣ M) (hx : ∀ x ∈ xs, x ∣ M) :
    loopSteps acc xs ≤ 2 + (5*M+11)*xs.length := by
  induction xs generalizing acc with
  | nil => simp [loopSteps]
  | cons x xs ih =>
    have hacc : acc ≤ M := Nat.le_of_dvd hM ha
    have hg := gcdLoopSteps_bound acc x
    have htail := ih (Nat.lcm acc x) (Nat.lcm_dvd ha (hx x (by simp)))
      (fun y hy => hx y (by simp [hy]))
    simp only [loopSteps,List.length_cons,Nat.mul_add,Nat.mul_one]
    omega

theorem steps_cap (M : Nat) (xs : List Nat) (hM : 0 < M)
    (hx : ∀ x ∈ xs, x ∣ M) : steps xs ≤ 4 + (5*M+11)*xs.length := by
  have h := loopSteps_cap M 1 xs hM (Nat.one_dvd M) hx
  unfold steps
  omega

theorem result_dvd (M acc : Nat) (xs : List Nat) (ha : acc ∣ M)
    (hx : ∀ x ∈ xs, x ∣ M) : xs.foldl Nat.lcm acc ∣ M := by
  induction xs generalizing acc with
  | nil => exact ha
  | cons x xs ih =>
    exact ih (Nat.lcm acc x) (Nat.lcm_dvd ha (hx x (by simp)))
      (fun y hy => hx y (by simp [hy]))

end REWB.WordRAM.LCMFold
