import REWB.OuterColumn

/-! A concrete immutable endpoint aggregate for a fixed prefix and a finite
Boolean endpoint row.  One backwards pass materializes the DFA-state row at
each position, retaining only its initial-state answer.  Queries therefore
perform one bounded array read; they neither scan endpoints nor reconstruct
a state row.  Missing mask entries are false, and position `v.size` is a
genuine endpoint accepting the empty word when the DFA permits it.

The charged word-RAM work includes each scalar row cell (transition, final
test, Boolean operations, vector read/write), bit/letter accesses, answer
pushes and loop control.  DFA sizes are fixed pattern parameters. -/
namespace REWB.OneUseRange.FarAggregate
variable {α : Type}

def bit (bits : Array Bool) (i : Nat) : Bool := bits[i]?.getD false

def terminal (A : DFA α) (mark : Bool) : Vector Bool A.stateCount × Nat :=
  (Vector.ofFn (fun q => mark && A.final q), 3*A.stateCount)

def advance (A : DFA α) (c : α) (mark : Bool)
    (next : Vector Bool A.stateCount) : Vector Bool A.stateCount × Nat :=
  (Vector.ofFn (fun q => (mark && A.final q) || next.get (A.step q c)),
    6*A.stateCount)

@[simp] theorem terminal_get (A : DFA α) (mark : Bool) (q : Fin A.stateCount) :
    (terminal A mark).1.get q = (mark && A.final q) := by simp [terminal, Vector.get, Vector.getElem_ofFn]

@[simp] theorem advance_get (A : DFA α) (c : α) (mark : Bool)
    (next : Vector Bool A.stateCount) (q : Fin A.stateCount) :
    (advance A c mark next).1.get q =
      ((mark && A.final q) || next.get (A.step q c)) := by simp [advance, Vector.get, Vector.getElem_ofFn]

structure State (k : Nat) where
  row : Vector Bool k
  answers : Array Bool
  work : Nat

/-- The proof bound on the array access is erased.  The recursive call is in
tail position; only the latest materialized DFA row is retained. -/
def sweep (A : DFA α) (v : Array α) (bits : Array Bool) :
    (n : Nat) → n≤v.size → State A.stateCount → State A.stateCount
  | 0, _, st => st
  | n+1, hn, ⟨row,answers,work⟩ =>
    let fresh := advance A (v[n]'(by omega)) (bit bits n) row
    sweep A v bits n (by omega)
      ⟨fresh.1, answers.push (fresh.1.get A.initial), work+fresh.2+6⟩

def initial (A : DFA α) (bits : Array Bool) (g : Nat) : State A.stateCount :=
  let row := terminal A (bit bits g)
  ⟨row.1, #[row.1.get A.initial], row.2+5⟩

structure Index where
  length : Nat
  answers : Array Bool
  work : Nat
  deriving Repr

/-- `answers[j]` stores the answer at original position `length-j`. -/
def build (A : DFA α) (v : Array α) (bits : Array Bool) : Index :=
  let g := v.size
  let st := sweep A v bits g (Nat.le_refl g) (initial A bits g)
  ⟨g, st.answers, st.work+2⟩

def query (idx : Index) (l : Nat) : Bool×Nat :=
  if l≤idx.length then (idx.answers[idx.length-l]?.getD false, 4)
  else (false, 1)

theorem sweep_size (A : DFA α) (v : Array α) (bits : Array Bool)
    (n : Nat) (hn : n≤v.size) (st : State A.stateCount) :
    (sweep A v bits n hn st).answers.size = st.answers.size+n := by
  induction n generalizing st with
  | zero => simp [sweep]
  | succ n ih =>
    cases st
    rw [sweep, ih]
    simp only [Array.size_push]
    omega

theorem sweep_work (A : DFA α) (v : Array α) (bits : Array Bool)
    (n : Nat) (hn : n≤v.size) (st : State A.stateCount) :
    (sweep A v bits n hn st).work = st.work+n*(6*A.stateCount+6) := by
  induction n generalizing st with
  | zero => simp [sweep]
  | succ n ih =>
    cases st
    rw [sweep, ih]
    simp only [advance, Nat.add_mul, Nat.one_mul]
    omega

@[simp] theorem build_length (A : DFA α) (v : Array α) (bits : Array Bool) :
    (build A v bits).length = v.size := rfl

@[simp] theorem build_size (A : DFA α) (v : Array α) (bits : Array Bool) :
    (build A v bits).answers.size = v.size+1 := by
  simp [build, sweep_size, initial]
  omega

theorem build_work_exact (A : DFA α) (v : Array α) (bits : Array Bool) :
    (build A v bits).work = v.size*(6*A.stateCount+6)+3*A.stateCount+7 := by
  simp only [build, sweep_work, initial, terminal]
  omega

theorem build_work (A : DFA α) (v : Array α) (bits : Array Bool) :
    (build A v bits).work ≤ (6*A.stateCount+7)*(v.size+1) := by
  rw [build_work_exact]
  simp only [Nat.mul_add, Nat.mul_one, Nat.add_mul, Nat.mul_comm]
  omega

theorem query_work (idx : Index) (l : Nat) : (query idx l).2≤4 := by
  unfold query
  split <;> simp

theorem query_outside (idx : Index) (l : Nat) (hl : idx.length<l) :
    (query idx l).1=false := by simp [query, Nat.not_le.mpr hl]

end REWB.OneUseRange.FarAggregate
