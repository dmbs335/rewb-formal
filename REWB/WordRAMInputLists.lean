import REWB.WordRAMListBounds
import REWB.MachineWordBounds

/-! A canonical, explicit input layout for finite-alphabet words, and a
fully instantiated finite-word execution of the copying reverse program.
The layout only encodes the input letters and links; it contains no
precomputed output or execution cost. Its size is exactly two cells per
letter, with address zero reserved for null. -/
namespace REWB.WordRAM.InputLists
open ListHeap Lists
variable {σ : Nat}

def letters (w : List (Fin σ)) : List Nat := w.map Fin.val

def layout (w : List (Fin σ)) : CopyResult :=
  copyReverse (fun _ => 0) 1 0 (letters w).reverse

theorem letters_length (w : List (Fin σ)) : (letters w).length = w.length :=
  List.length_map _

theorem layout_frontier (w : List (Fin σ)) : (layout w).frontier = 1+2*w.length := by
  simp only [layout,copyReverse_frontier,List.length_reverse,letters_length]

theorem layout_rep (w : List (Fin σ)) :
    ListAt (layout w).heap (layout w).frontier (layout w).pointer (letters w) := by
  have h := copyReverse_rep (h := fun _ => 0) (fresh := 1) (acc := 0)
    (ys := []) (by decide) ListAt.nil (letters w).reverse
  simpa only [layout,List.reverse_reverse,List.append_nil] using h

def input (w : List (Fin σ)) : State := {
  regs := fun r => if r = 0 then (layout w).pointer
    else if r = 2 then (layout w).frontier else 0
  heap := (layout w).heap }

theorem input_rep (w : List (Fin σ)) :
    ListAt (input w).heap ((input w).regs 2) ((input w).regs 0) (letters w) := by
  simpa only [input,ite_true,show (2:Nat) ≠ 0 by decide,if_false] using layout_rep w

theorem layout_heap_fits (w : List (Fin σ)) (capacity : Nat)
    (hc : σ+4*w.length+16 < capacity) : ∀ a, (layout w).heap a < capacity := by
  apply copyReverse_values_bounded
  · intro a
    omega
  · intro x hx
    have hx' : x ∈ letters w := List.mem_reverse.mp hx
    obtain ⟨letter,_,he⟩ := List.mem_map.mp hx'
    have hlt := letter.isLt
    omega
  · omega
  · simp only [List.length_reverse,letters_length]
    omega

theorem input_fits (w : List (Fin σ)) (capacity : Nat)
    (hc : σ+4*w.length+16 < capacity) : Fits capacity (input w) := by
  have hf := layout_frontier w
  have hp := (layout_rep w).pointer_lt (by omega)
  refine ⟨by simpa [input] using (show 0 < capacity by omega),?_,layout_heap_fits w capacity hc⟩
  intro r
  simp only [input]
  split
  · omega
  · split <;> omega

/-- The polynomial capacity accounts for input and fresh output cells,
letter values, and the finite program's instruction addresses. -/
theorem layout_capacity (w : List (Fin σ)) :
    σ+4*w.length+16 ≤ MachineWordBounds.cap (σ+20) 1 w.length := by
  simp only [MachineWordBounds.cap,Nat.pow_one,Nat.add_mul,Nat.mul_add,Nat.mul_one]
  omega

def wordWidth (σ n : Nat) : Nat := MachineWordBounds.width (σ+20) 1 n

theorem layout_capacity_fits (w : List (Fin σ)) :
    σ+4*w.length+16 < 2^wordWidth σ w.length :=
  MachineWordBounds.value_fits (layout_capacity w)

theorem wordWidth_logarithmic (σ n : Nat) :
    wordWidth σ n ≤ ((σ+20).log2+2)*((n+2).log2+1) := by
  simpa only [wordWidth,MachineWordBounds.height,Nat.add_assoc] using
    MachineWordBounds.width_le_height (σ+20) 1 n

theorem reverse_input_exec (w : List (Fin σ)) :
    WordExec (2^wordWidth σ w.length) reverseProgram (11*w.length+4)
      (input w) (reverseResult (input w) (letters w)) := by
  have hc := layout_capacity_fits w
  have hf := layout_frontier w
  have h := reverse_word_exec (2^wordWidth σ w.length) (input w) (letters w)
    rfl rfl (input_rep w) (input_fits w _ hc) (by omega)
    (by simpa only [input,show (2:Nat) ≠ 0 by decide,if_false,ite_true,
      hf,letters_length] using (show 1+2*w.length+2*w.length < 2^wordWidth σ w.length by omega))
  simpa only [letters_length] using h

theorem reverse_input_rep (w : List (Fin σ)) :
    let out := reverseResult (input w) (letters w)
    ListAt out.heap (out.regs 2) (out.regs 1) (letters w).reverse := by
  have hf : 0 < (input w).regs 2 := by
    simp only [input,show (2:Nat) ≠ 0 by decide,if_false,ite_true,layout_frontier]
    omega
  have hy : ListAt (input w).heap ((input w).regs 2) ((input w).regs 1) [] := by
    simpa only [input,show (1:Nat) ≠ 0 by decide,show (1:Nat) ≠ 2 by decide,if_false] using
      (ListAt.nil (heap := (input w).heap) (limit := (input w).regs 2))
  simpa only [List.append_nil] using reverse_result_rep (input w) (letters w) [] hf (input_rep w) hy

theorem reverse_input_fits (w : List (Fin σ)) :
    Fits (2^wordWidth σ w.length) (reverseResult (input w) (letters w)) :=
  (reverse_input_exec w).preservesFits (input_fits w _ (layout_capacity_fits w))

end REWB.WordRAM.InputLists
