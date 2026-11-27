import REWB.ActualModulusRAM
import REWB.WordRAMLCMFoldWords

/-! One connected RAM trace for folding the modulus fields of a real
conjunction. The input representation lists the atom modulus fields; it
does not supply their aggregate LCM, a list length, or a cost. Constructing
the enclosing formula/event heap representation remains a client task. -/
namespace REWB.ActualModulus.FoldRAM
open AffineProjection WordRAM WordRAM.ListHeap

def rowValues (C : Conj) : List Nat := C.map ActualModulus.atom

theorem rowValues_length (C : Conj) : (rowValues C).length = C.length := List.length_map _

theorem row_fold_value (C : Conj) :
    (rowValues C).foldl Nat.lcm 1 = (ActualModulus.row C).1 := by
  rw [← Calls.row_value]
  simp only [rowValues,Calls.row,Calls.scan_value,List.foldl_map]

theorem rowValues_divides (C : Conj) (M : Nat) (hM : 0 < M)
    (h : ∀ a, a ∈ C → AtomDivides M a) :
    ∀ x, x ∈ rowValues C → x ∣ M := by
  intro x hx
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
  exact ActualModulus.atom_dvd a M hM (h a ha)

theorem row_steps_le (C : Conj) (M : Nat) (hM : 0 < M)
    (h : ∀ a, a ∈ C → AtomDivides M a) :
    LCMFold.steps (rowValues C) ≤ (5*M+11)*(ActualModulus.row C).2 := by
  have hb := LCMFold.steps_cap M (rowValues C) hM (rowValues_divides C M hM h)
  have hc : (rowValues C).length+1 ≤ (ActualModulus.row C).2 := by
    rw [rowValues_length,ActualModulus.row_steps]
    omega
  calc
    LCMFold.steps (rowValues C) ≤ (5*M+11)*((rowValues C).length+1) := by
      rw [Nat.mul_add,Nat.mul_one]
      omega
    _ ≤ (5*M+11)*(ActualModulus.row C).2 := Nat.mul_le_mul_left _ hc

def wordBits (M limit : Nat) : Nat := (limit+M*M+M+18).log2+1

/-- This is a single complete instruction program, including the linked
list loop and every inner Euclidean loop. The pattern modulus bounds are
derived from the real conjunction's atom fields. -/
theorem row_word_refines (C : Conj) (M : Nat) (hM : 0 < M)
    (h : ∀ a, a ∈ C → AtomDivides M a)
    (heap : Heap) (limit ptr : Nat) (hx : ListAt heap limit ptr (rowValues C)) :
    ∃ out,
      WordExec (2^wordBits M limit) LCMFold.program (LCMFold.steps (rowValues C))
        (LCMFold.input ptr heap) out ∧
      out.regs 8 = (ActualModulus.row C).1 ∧ out.regs 5 = 0 ∧
      out.halted = true ∧ out.heap = heap ∧
      LCMFold.steps (rowValues C) ≤ (5*M+11)*(ActualModulus.row C).2 := by
  have hc : limit+M*M+M+18 < 2^wordBits M limit := Nat.lt_log2_self
  obtain ⟨out,hrun,hresult⟩ := LCMFold.word_exec (2^wordBits M limit) M heap limit ptr
    (rowValues C) hx (by omega) (by omega) hM (by omega) (by omega)
    (rowValues_divides C M hM h)
  rw [row_fold_value] at hresult
  exact ⟨out,hrun,hresult.1,hresult.2.1,hresult.2.2.1,hresult.2.2.2,row_steps_le C M hM h⟩

end REWB.ActualModulus.FoldRAM
