import REWB.OneUseRangeBorderRows
import REWB.OneUseRangeBorderVariants
import REWB.BoundaryRangeNearIndexScanCost

/-! One shared text-built index for the residual near-endpoint case of
one-use range queries. Only first starts and second ends in the two
short endpoint blocks are enumerated. Positive capture lengths remain
represented by dyadic choices; the C-gap is split through one actual
finite state at the midpoint. -/
namespace REWB.OneUseRange.Border
open REWB.BoundaryApplication REWB.BoundaryRange
variable {σ : Nat}

def middle (i t : Nat) : Nat := i+(t-i)/2

def any {Q : Type} (probe : Q→Bool×Nat) : List Q→Bool×Nat
  | [] => (false,1)
  | q::qs =>
    let head:=probe q
    let tail:=any probe qs
    (head.1 || tail.1,head.2+tail.2+3)

theorem any_correct {Q : Type} (probe : Q→Bool×Nat) (qs : List Q) :
    (any probe qs).1=true ↔ ∃q,q∈qs ∧ (probe q).1=true := by
  induction qs with
  | nil => simp only [any,List.not_mem_nil,false_and,exists_false,Bool.false_eq_true]
  | cons q qs ih =>
    simp only [any,Bool.or_eq_true,ih,List.mem_cons]
    constructor
    · rintro (h|⟨v,hv,h⟩)
      · exact ⟨q,Or.inl rfl,h⟩
      · exact ⟨v,Or.inr hv,h⟩
    · rintro ⟨v,hv,h⟩
      rcases hv with rfl|hv
      · exact Or.inl h
      · exact Or.inr ⟨v,hv,h⟩

theorem any_work {Q : Type} (probe : Q→Bool×Nat) (qs : List Q) (budget : Nat)
    (hb : ∀q,q∈qs→(probe q).2≤budget) :
    (any probe qs).2≤qs.length*(budget+3)+1 := by
  induction qs with
  | nil => simp only [any,List.length_nil,Nat.zero_mul,Nat.zero_add,Nat.le_refl]
  | cons q qs ih =>
    have hh:=hb q List.mem_cons_self
    have ht:=ih (fun v hv=>hb v (List.mem_cons_of_mem _ hv))
    simp only [any,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

structure Index (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) where
  size : Nat
  height : Nat
  size_eq : size=w.toArray.size
  height_eq : height=MaskedSuffixClass.height size
  classes : BoundaryBorder.WindowIndex.Index size height
  aranges : Range.Index A
  branges : Range.Index B
  cranges : Range.Index C
  eranges : Range.Index E
  states : List (Fin C.stateCount)
  work : Nat

def build (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ) : Index A B C E w :=
  let classes:=BoundaryBorder.WindowIndex.prepare w.toArray fallback
  let aranges:=Range.build A w
  let branges:=Range.build B w
  let cranges:=Range.build C w
  let eranges:=Range.build E w
  ⟨w.toArray.size,classes.scales,rfl,rfl,classes,aranges,branges,cranges,eranges,List.finRange C.stateCount,
    classes.work+StartIndex.rangeBuildWork A aranges+StartIndex.rangeBuildWork B branges+
      StartIndex.rangeBuildWork C cranges+StartIndex.rangeBuildWork E eranges+2*w.length+C.stateCount+14⟩

def state {A B C E : DFA (Fin σ)} {w : Word (Fin σ)} (idx : Index A B C E w)
    (i : Fin (idx.size+1)) (t : Nat) (q : Fin C.stateCount) : Bool×Nat :=
  let m:=middle i.val t
  let found:=Regular.dyadic (Automata.start C q) B (Automata.stop C q) idx.classes
    (startRanges C idx.cranges q) idx.branges (stopRanges C idx.cranges q) m t i m
  (found.1,found.2+24)

def inner {A B C E : DFA (Fin σ)} {w : Word (Fin σ)} (idx : Index A B C E w)
    (i : Fin (idx.size+1)) (t : Nat) : Bool×Nat :=
  let positive:=any (state idx i t) idx.states
  let empty:=NearIndex.regular C idx.cranges i.val t
  (positive.1 || (B.final B.initial && empty.1),positive.2+empty.2+4)

def queryAt {A B C E : DFA (Fin σ)} {w : Word (Fin σ)} (idx : Index A B C E w)
    (left right i t : Nat) : Bool×Nat :=
  if h : left≤i ∧ i≤t ∧ t≤right ∧ right≤idx.size then
    let start : Fin (idx.size+1):=⟨i,by omega⟩
    let copy:=inner idx start t
    let before:=NearIndex.regular A idx.aranges left i
    let after:=NearIndex.regular E idx.eranges t right
    (before.1 && copy.1 && after.1,copy.2+before.2+after.2+9)
  else (false,5)

def row {A B C E : DFA (Fin σ)} {w : Word (Fin σ)} (idx : Index A B C E w)
    (left right rightGrid i : Nat) : Bool×Nat :=
  NearIndex.scan (queryAt idx left right i) (rightGrid+1) (right-rightGrid)

def query {A B C E : DFA (Fin σ)} {w : Word (Fin σ)} (idx : Index A B C E w)
    (left right leftGrid rightGrid : Nat) : Bool×Nat :=
  NearIndex.scan (row idx left right rightGrid) left (leftGrid-left)

end REWB.OneUseRange.Border
