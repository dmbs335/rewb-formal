import REWB.BoundaryIndexTree
import REWB.RegularDFA

/-! Concrete boundary-index color encodings.

Fixed-source-end heavy paths carry a set of admissible A states at each
endpoint. Descending an edge replaces that set by its preimage under the
edge's A transition. The finite subset universe is explicitly enumerated,
encoded by integer ranks, and the entire color map is materialized once.
The transition need not be injective or surjective. -/
namespace REWB.BoundaryIndex.Colors
open REWB.FiniteRelation
variable {α : Type}

/-- The state type is the finite universe of Boolean subsets. The machine
interface supplies the verified finite encoding/decoding machinery. -/
def colorSpace (d : DFA α) : RegularDFA.Machine Unit where
  State := Fin d.stateCount→Bool
  decEq := RegularDFA.functionDecEq (finEnum d.stateCount)
  enumeration := RegularDFA.functionEnum (finEnum d.stateCount)
  initial := fun _=>false
  step := fun s _=>s
  final := fun _=>false

abbrev Color (d : DFA α) := Fin (colorSpace d).enumeration.elems.length

def decode (d : DFA α) (c : Color d) : Fin d.stateCount→Bool := (colorSpace d).decode c

def encode (d : DFA α) (s : Fin d.stateCount→Bool) : Color d := (colorSpace d).encode s

theorem decode_encode (d : DFA α) (s : Fin d.stateCount→Bool) : decode d (encode d s)=s :=
  (colorSpace d).decode_encode s

/-- Input is an already materialized DFA transition vector. Constructing
this map only ranges over the fixed finite color/state universes. -/
def preimageMap (d : DFA α) (tr : Vector (Fin d.stateCount) d.stateCount) :
    Vector (Color d) (colorSpace d).enumeration.elems.length :=
  Vector.ofFn (fun c=>encode d (fun q=>decode d c (tr.get q)))

theorem preimageMap_correct (d : DFA α)
    (tr : Vector (Fin d.stateCount) d.stateCount) (c : Color d) (q : Fin d.stateCount) :
    decode d ((preimageMap d tr).get c) q=decode d c (tr.get q) := by
  simp only [preimageMap,Table.get_ofFn,decode_encode]

/-- An edge transition obtained from any correct range-product index
implements exactly the required preimage. No inverse is constructed. -/
theorem preimageMap_word (d : DFA α) (w : Word α)
    (tr : Vector (Fin d.stateCount) d.stateCount)
    (ht : ∀ q,tr.get q=d.run q w) (c : Color d) (q : Fin d.stateCount) :
    decode d ((preimageMap d tr).get c) q=decode d c (d.run q w) := by
  rw [preimageMap_correct,ht]

/-- A query supplies the current A state and selects every encoded set
containing it. More than one old color may have merged into a new set. -/
def select (d : DFA α) (q : Fin d.stateCount) : Color d→Bool := fun c=>decode d c q

theorem selected_preimage (d : DFA α)
    (tr : Vector (Fin d.stateCount) d.stateCount) (c : Color d) (q : Fin d.stateCount) :
    select d q ((preimageMap d tr).get c)=select d (tr.get q) c :=
  preimageMap_correct d tr c q

/-- Root recoloring implements the backward A-state transformation for
all endpoint classes, including collisions between old colors. -/
theorem recolored_active (d : DFA α) {m h : Nat}
    (tr : Vector (Fin d.stateCount) d.stateCount)
    (t : Tree (colorSpace d).enumeration.elems.length m h)
    (color : Color d) (q : Fin m) :
    (Tree.cache (Tree.recolor (preimageMap d tr) t).1).view.active color q=true ↔
      ∃ old, (preimageMap d tr).get old=color ∧
        (Tree.cache t).view.active old q=true := by
  rw [Tree.recolor_cache,View.rename_active]

/-- Selecting after a preimage transformation is equivalent to selecting
before it with the forward-transformed A state. -/
theorem recolored_selected (d : DFA α) {m h : Nat}
    (tr : Vector (Fin d.stateCount) d.stateCount)
    (t : Tree (colorSpace d).enumeration.elems.length m h)
    (a : Fin d.stateCount) (q : Fin m) :
    (∃ color, select d a color=true ∧
      (Tree.cache (Tree.recolor (preimageMap d tr) t).1).view.active color q=true) ↔
    ∃ old, select d (tr.get a) old=true ∧ (Tree.cache t).view.active old q=true := by
  simp only [recolored_active]
  constructor
  · rintro ⟨color,hs,old,he,ha⟩
    refine ⟨old,?_,ha⟩
    rw [← selected_preimage d tr old a,he]
    exact hs
  · rintro ⟨old,hs,ha⟩
    refine ⟨(preimageMap d tr).get old,?_,old,rfl,ha⟩
    rw [selected_preimage]
    exact hs

end REWB.BoundaryIndex.Colors
