import REWB.BlockIndex

/-! Replace the logarithmic dyadic query in the integrated matchers by a
    shared block dictionary and a directly addressed macro index.
    Correctness is unconditional; cost is analyzed separately. -/
namespace REWB.BlockRelation
open FiniteRelation
open REWB.Spec (slice)
variable {S α : Type} [DecidableEq S]

def letter (e : Enumeration S) (step : α × Bool → Rel S) (x : α × Bool) :
    MatrixTable.Matrix e := MatrixTable.ofRel e (step x)

def prepare (e : Enumeration S) (step : α × Bool → Rel S) (w : Word α) (b : Nat) :
    BlockIndex.Shared (MatrixTable.Matrix e) :=
  BlockIndex.prepare (MatrixTable.ops e) (letter e step) w b

def column (e : Enumeration S) (I : BlockIndex.Shared (MatrixTable.Matrix e))
    (m : Nat → Bool) : BlockIndex.Column (MatrixTable.Matrix e) :=
  BlockIndex.buildColumn (MatrixTable.ops e) I m

def query (e : Enumeration S) (I : BlockIndex.Shared (MatrixTable.Matrix e))
    (C : BlockIndex.Column (MatrixTable.Matrix e)) (l r : Nat) : Option (Rel S) :=
  (BlockIndex.query (MatrixTable.ops e) I C l r).map MatrixTable.denote

theorem query_correct (e : Enumeration S) (step : α × Bool → Rel S)
    (w : Word α) (b : Nat) (m : Nat → Bool) (l r : Nat)
    (hb : 0<b) (hl : l≤r) (hr : r≤w.length) :
    query e (prepare e step w b) (column e (prepare e step w b) m) l r =
      some (RangeProducts.product (FiniteRelation.ops e)
        ((slice (IndexedMarked.decorate m 0 w) l r).map step)) := by
  unfold query prepare column
  rw [BlockIndex.query_correct (MatrixTable.ops e) (letter e step) w b m l r hb hl hr]
  simp only [Option.map,MatrixTable.denote_product,BlockIndex.word,BlockIndex.map_slice,
    List.map_map,Function.comp_def,letter,MatrixTable.denote_ofRel]

end REWB.BlockRelation

namespace REWB.BlockMatcher
open FiniteRelation
open REWB.Spec (slice)
open REWB.IndexedMarked (decorate)
open REWB.OuterTables (Prepared ReadyTable)
variable {α : Type}

abbrev E1 (P : SevenDFA α) := MatrixTable.Matrix (P1Index.cdEnum P)
abbrev E2 (P : SevenDFA α) := MatrixTable.Matrix (P1Index.rightMachine P).enum
abbrev E3 (P : SevenDFA α) := MatrixTable.Matrix (MarkedTransfer.enum P.D P.C)

structure Shared1 (P : SevenDFA α) where
  first : BlockIndex.Shared (E1 P)
  second : BlockIndex.Shared (E2 P)

structure Column1 (P : SevenDFA α) where
  first : BlockIndex.Column (E1 P)
  second : BlockIndex.Column (E2 P)

def prepare1 (P : SevenDFA α) (w : Word α) (b : Nat) : Shared1 P :=
  ⟨BlockRelation.prepare (P1Index.cdEnum P) (MarkedTransfer.letter P.C P.D) w b,
    BlockRelation.prepare (P1Index.rightMachine P).enum (P1Index.rightMachine P).letter w b⟩

def column1 (P : SevenDFA α) (I : Shared1 P) (m : Nat→Bool) : Column1 P :=
  ⟨BlockRelation.column (P1Index.cdEnum P) I.first m,
    BlockRelation.column (P1Index.rightMachine P).enum I.second m⟩

def query1 (P : SevenDFA α) (I : Shared1 P) (C : Column1 P) (terminal : Bool)
    (a z t : Nat) (qa : Fin P.A.stateCount) : Option Bool := do
  let x ← BlockRelation.query (P1Index.cdEnum P) I.first C.first a z
  let y ← BlockRelation.query (P1Index.rightMachine P).enum I.second C.second z t
  return pre (P1Index.cdEnum P) x (fun s =>
    pre (P1Index.rightMachine P).enum y ((P1Index.rightMachine P).final terminal)
      (.inl (s,qa))) (.inl P.C.initial)

theorem query1_correct (P : SevenDFA α) (w : Word α) (b : Nat) (m : Nat→Bool)
    (terminal : Bool) (a z t : Nat) (qa : Fin P.A.stateCount)
    (hb : 0<b) (haz : a≤z) (hzt : z≤t) (ht : t≤w.length) :
    query1 P (prepare1 P w b) (column1 P (prepare1 P w b) m) terminal a z t qa =
      P1Index.query P (P1Index.build P (decorate m 0 w)) terminal a z t qa := by
  have ht' : t≤(decorate m 0 w).length := by rw [IndexedMarked.decorate_length]; exact ht
  rw [P1Index.query_correct P _ terminal a z t qa haz hzt ht']
  unfold query1 prepare1 column1
  change (do
    let x ← BlockRelation.query (P1Index.cdEnum P)
      (BlockRelation.prepare (P1Index.cdEnum P) (MarkedTransfer.letter P.C P.D) w b)
      (BlockRelation.column (P1Index.cdEnum P)
        (BlockRelation.prepare (P1Index.cdEnum P) (MarkedTransfer.letter P.C P.D) w b) m) a z
    let y ← BlockRelation.query (P1Index.rightMachine P).enum
      (BlockRelation.prepare (P1Index.rightMachine P).enum (P1Index.rightMachine P).letter w b)
      (BlockRelation.column (P1Index.rightMachine P).enum
        (BlockRelation.prepare (P1Index.rightMachine P).enum (P1Index.rightMachine P).letter w b) m) z t
    return pre (P1Index.cdEnum P) x (fun s =>
      pre (P1Index.rightMachine P).enum y ((P1Index.rightMachine P).final terminal)
        (.inl (s,qa))) (.inl P.C.initial)) = _
  rw [BlockRelation.query_correct _ _ w b m a z hb haz (by omega),
    BlockRelation.query_correct _ _ w b m z t hb hzt ht]
  rfl

def prepare2 (P : SevenDFA α) (w : Word α) (b : Nat) : BlockIndex.Shared (E3 P) :=
  BlockRelation.prepare (MarkedTransfer.enum P.D P.C) (MarkedTransfer.letter P.D P.C) w b

def column2 (P : SevenDFA α) (I : BlockIndex.Shared (E3 P)) (m : Nat→Bool) :
    BlockIndex.Column (E3 P) :=
  BlockRelation.column (MarkedTransfer.enum P.D P.C) I m

def query2 (P : SevenDFA α) (I : BlockIndex.Shared (E3 P)) (C : BlockIndex.Column (E3 P))
    (terminal : Bool) (l r : Nat) (q : Fin P.D.stateCount) : Option Bool :=
  (BlockRelation.query (MarkedTransfer.enum P.D P.C) I C l r).map
    (fun x => pre (MarkedTransfer.enum P.D P.C) x
      (pre (MarkedTransfer.enum P.D P.C) (MarkedTransfer.epsilon P.D P.C terminal)
        (MarkedTransfer.final P.D P.C)) (.inl q))

theorem query2_correct (P : SevenDFA α) (w : Word α) (b : Nat) (m : Nat→Bool)
    (terminal : Bool) (l r : Nat) (q : Fin P.D.stateCount)
    (hb : 0<b) (hl : l≤r) (hr : r≤w.length) :
    query2 P (prepare2 P w b) (column2 P (prepare2 P w b) m) terminal l r q =
      (IndexedMarked.query P.D P.C terminal
        (IndexedMarked.build P.D P.C (decorate m 0 w)).1 l r (.inl q)).answer := by
  have hr' : r≤(decorate m 0 w).length := by rw [IndexedMarked.decorate_length]; exact hr
  rw [IndexedMarked.query_correct _ _ terminal _ l r (.inl q) hl hr']
  unfold query2 prepare2 column2
  rw [BlockRelation.query_correct _ _ w b m l r hb hl hr]
  rfl

def test1 (P : SevenDFA α) (I : Prepared P) (S : Shared1 P) (C : Column1 P)
    (m : Nat→Bool) (t a : Nat) : Bool :=
  let d := OuterTables.common P I a t
  (query1 P S C (m t) a (t-d) t (OuterTables.aAt P I (a-d))).getD false

def test2 (P : SevenDFA α) (I : Prepared P) (S : BlockIndex.Shared (E3 P))
    (C : BlockIndex.Column (E3 P)) (m : Nat→Bool) (t a : Nat) : Bool :=
  let d := OuterTables.common P I a t
  (query2 P S C (m a) (a-d) a (OuterTables.dAt P I a (t-d))).getD false

theorem test1_eq [DecidableEq α] (P : SevenDFA α) (w : Word α) (b : Nat)
    (m : Nat→Bool) (t a : Nat) (hb : 0<b) (hat : a≤t) (ht : t≤w.length) :
    test1 P (OuterTables.prepare P w) (prepare1 P w b) (column1 P (prepare1 P w b) m)
      m t a =
      Integrated.test1 P (OuterTables.prepare P w) m (P1Index.build P (decorate m 0 w)) t a := by
  have hc := OuterTables.common_correct P w a t hat ht
  have hd := OuterColumn.maxCommon_isMax w a t
  have hbound : OuterTables.common P (OuterTables.prepare P w) a t≤t-a := by
    rw [hc]
    exact hd.1.2.1
  unfold test1 Integrated.test1
  dsimp only
  rw [query1_correct P w b m _ a _ t _ hb (by omega) (by omega) ht]

theorem test2_eq [DecidableEq α] (P : SevenDFA α) (w : Word α) (b : Nat)
    (m : Nat→Bool) (t a : Nat) (hb : 0<b) (hat : a≤t) (ht : t≤w.length) :
    test2 P (OuterTables.prepare P w) (prepare2 P w b) (column2 P (prepare2 P w b) m)
      m t a =
      Integrated.test2 P (OuterTables.prepare P w) m
        (IndexedMarked.build P.D P.C (decorate m 0 w)).1 t a := by
  unfold test2 Integrated.test2
  dsimp only
  rw [query2_correct P w b m _ _ a _ hb (by omega) (by omega)]

private theorem any_congr_on {X : Type} (xs : List X) (f g : X→Bool)
    (h : ∀ x, x∈xs→f x=g x) : xs.any f=xs.any g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (f x || xs.any f)=(g x || xs.any g)
    rw [h x (by simp),ih (fun y hy=>h y (by simp [hy]))]

def col1 (P : SevenDFA α) (I : Prepared P) (R : ReadyTable P)
    (S : Shared1 P) (t : Nat) : Bool :=
  let m := fun p => OuterTables.readyAt P R p t
  let C := column1 P S m
  (List.range (t+1)).any (test1 P I S C m t)

def col2 (P : SevenDFA α) (w : Word α) (I : Prepared P) (R : ReadyTable P)
    (S : BlockIndex.Shared (E3 P)) (t : Nat) : Bool :=
  let r := fun p => OuterTables.readyAt P R p t
  let row := MaskScan.first2Row P w r
  let m := MaskScan.accepted P.B row
  let C := column2 P S m
  (List.range (t+1)).any (test2 P I S C m t)

theorem col1_eq [DecidableEq α] (P : SevenDFA α) (w : Word α)
    (b : Nat) (R : ReadyTable P) (t : Nat) (hb : 0<b) (ht : t≤w.length) :
    col1 P (OuterTables.prepare P w) R (prepare1 P w b) t =
      Integrated.col1 P w (OuterTables.prepare P w) R t := by
  unfold col1 Integrated.col1
  dsimp only
  apply any_congr_on
  intro a ha
  have hat : a≤t := by have h := List.mem_range.mp ha; omega
  exact test1_eq P w b _ t a hb hat ht

theorem col2_eq [DecidableEq α] (P : SevenDFA α) (w : Word α)
    (b : Nat) (R : ReadyTable P) (t : Nat) (hb : 0<b) (ht : t≤w.length) :
    col2 P w (OuterTables.prepare P w) R (prepare2 P w b) t =
      Integrated.col2 P w (OuterTables.prepare P w) R t := by
  unfold col2 Integrated.col2
  dsimp only
  apply any_congr_on
  intro a ha
  have hat : a≤t := by have h := List.mem_range.mp ha; omega
  exact test2_eq P w b _ t a hb hat ht

def match1With [DecidableEq α] (P : SevenDFA α) (w : Word α) (b : Nat) : Bool :=
  let I := OuterTables.prepare P w
  let R := OuterTables.buildReady P w I
  let S := prepare1 P w b
  (List.range (I.n+1)).any (col1 P I R S)

def match2With [DecidableEq α] (P : SevenDFA α) (w : Word α) (b : Nat) : Bool :=
  let I := OuterTables.prepare P w
  let R := OuterTables.buildReady P w I
  let S := prepare2 P w b
  (List.range (I.n+1)).any (col2 P w I R S)

theorem match1With_eq [DecidableEq α] (P : SevenDFA α) (w : Word α) (b : Nat)
    (hb : 0<b) : match1With P w b=Integrated.match1 P w := by
  unfold match1With Integrated.match1
  dsimp only
  apply any_congr_on
  intro t ht
  have h : t<w.length+1 := List.mem_range.mp ht
  exact col1_eq P w b _ t hb (by omega)

theorem match2With_eq [DecidableEq α] (P : SevenDFA α) (w : Word α) (b : Nat)
    (hb : 0<b) : match2With P w b=Integrated.match2 P w := by
  unfold match2With Integrated.match2
  dsimp only
  apply any_congr_on
  intro t ht
  have h : t<w.length+1 := List.mem_range.mp ht
  exact col2_eq P w b _ t hb (by omega)

def width (n : Nat) : Nat := max 1 (Nat.log2 (n+2)/2)

theorem width_pos (n : Nat) : 0<width n := by
  exact Nat.lt_of_lt_of_le (by decide : 0<1) (Nat.le_max_left _ _)

def match1 [DecidableEq α] (P : SevenDFA α) (w : Word α) : Bool :=
  match1With P w (width w.length)

def match2 [DecidableEq α] (P : SevenDFA α) (w : Word α) : Bool :=
  match2With P w (width w.length)

theorem match1_correct [DecidableEq α] (P : SevenDFA α) (w : Word α) :
    match1 P w=true ↔ MatchesWithin P.nested1 w 2 := by
  rw [match1,match1With_eq P w _ (width_pos _),Integrated.match1_correct]

theorem match2_correct [DecidableEq α] (P : SevenDFA α) (w : Word α) :
    match2 P w=true ↔ MatchesWithin P.nested2 w 2 := by
  rw [match2,match2With_eq P w _ (width_pos _),Integrated.match2_correct]

end REWB.BlockMatcher
