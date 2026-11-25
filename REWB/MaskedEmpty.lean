import REWB.MaskScan
import REWB.MaskedProgression

/-! The empty-capture branch of the masked all-start query.  A backwards
    pass materializes two finite Boolean vectors at each step, retaining
    only the current vectors and one answer bit per source boundary.  The
    terminal boundary is a genuine candidate target.  Source and target
    masks are independent; a missing array entry denotes false.

    The recursive specification is compiled through a proved foldr
    equality.  Its executable path neither builds function-composition
    chains nor searches all possible target boundaries for each source.
-/
namespace REWB.MaskedEmpty
open MaskedProgression (readMask)
open MarkedDP (MarkedWord)
variable {α : Type}

structure Row (C E : DFA α) where
  suffix : Vector Bool E.stateCount
  gap : Vector Bool C.stateCount

def terminalRow (C E : DFA α) (terminal : Bool) : Row C E :=
  let accept := E.final E.initial
  ⟨Vector.ofFn E.final,
    Vector.ofFn (fun q => (terminal && C.final q) && accept)⟩

def nextRow (C E : DFA α) (x : α × Bool) (tail : Row C E) : Row C E :=
  let suffix := Vector.ofFn (fun q => tail.suffix.get (E.step q x.1))
  let accept := suffix.get E.initial
  ⟨suffix,Vector.ofFn (fun q =>
    ((x.2 && C.final q) && accept) || tail.gap.get (C.step q x.1))⟩

/-- Conservative per-row charge in the unit array-access and scalar model:
    each C cell has at most twelve and each E cell at most six operations;
    the remaining twenty-four cover row construction and loop control.
    Counter bookkeeping itself is excluded, as in MaskedProgression. -/
def rowBudget (C E : DFA α) : Nat := 12*C.stateCount+6*E.stateCount+24

structure Computed (C E : DFA α) where
  head : Row C E
  answers : List Bool
  work : Nat

def terminal (C E : DFA α) (mark : Bool) : Computed C E :=
  let head := terminalRow C E mark
  ⟨head,[head.gap.get C.initial],rowBudget C E⟩

def step (C E : DFA α) (x : α × Bool) (tail : Computed C E) : Computed C E :=
  let head := nextRow C E x tail.head
  ⟨head,head.gap.get C.initial :: tail.answers,tail.work+rowBudget C E⟩

def compute (C E : DFA α) (mark : Bool) : MarkedWord α → Computed C E
  | [] => terminal C E mark
  | x::xs => step C E x (compute C E mark xs)

def computeTR (C E : DFA α) (mark : Bool) (xs : MarkedWord α) : Computed C E :=
  xs.foldr (step C E) (terminal C E mark)

@[csimp] theorem compute_eq_computeTR : @compute = @computeTR := by
  funext α C E mark xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [compute,computeTR,List.foldr_cons] at ih ⊢
    rw [ih]

def markWord (target : Array Bool) (off : Nat) (w : Word α) : MarkedWord α :=
  (w.zipIdx off).map (fun x => (x.1,readMask target x.2))

theorem markWord_eq (target : Array Bool) (off : Nat) (w : Word α) :
    markWord target off w = IndexedMarked.decorate (readMask target) off w := by
  induction w generalizing off with
  | nil => rfl
  | cons c cs ih =>
    change (c,readMask target off)::markWord target (off+1) cs =
      (c,readMask target off)::IndexedMarked.decorate (readMask target) (off+1) cs
    rw [ih]

theorem markWord_length (target : Array Bool) (off : Nat) (w : Word α) :
    (markWord target off w).length = w.length := by
  simp only [markWord,List.length_map,List.length_zipIdx]

def gate (accept : Bool) (source : Array Bool) (bits : List Bool) : Array Bool :=
  ((bits.zipIdx).map (fun x => (accept && readMask source x.2) && x.1)).toArray

structure Result where
  answers : Array Bool
  work : Nat

/-- The outer forty operations per boundary cover length/index decoration,
    foldr reversal, output indexing, source gating and array materialization.
    The B empty-word test is evaluated once. -/
def solve (B C E : DFA α) (w : Word α) (source target : Array Bool) : Result :=
  let n := w.length
  let computed := compute C E (readMask target n) (markWord target 0 w)
  ⟨gate (B.final B.initial) source computed.answers,
    computed.work+40*(n+1)⟩

def Witness (B C E : DFA α) (w : Word α) (target : Array Bool) (s : Nat) : Prop :=
  B.accepts [] ∧ ∃ j, s≤j ∧ j≤w.length ∧ readMask target j=true ∧
    C.accepts (Spec.slice w s j) ∧ E.accepts (Spec.slice w j w.length)

end REWB.MaskedEmpty
