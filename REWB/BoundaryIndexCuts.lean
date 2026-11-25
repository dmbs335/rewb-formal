import REWB.BoundaryIndexQuery

/-! A preprocessed switch index with a per-query closed interval of allowed
cut positions. Two immutable indexes store fully enabled and fully disabled
switches. A query composes three range products and an explicit epsilon
switch at the right cut bound. It does not scan the candidate cut lengths
or rebuild a query-dependent mask. -/
namespace REWB.BoundaryIndex.Cuts
open REWB.FiniteRelation
open REWB.Spec (slice)
variable {α : Type}

def marked (flag : Bool) (w : Word α) : MarkedDP.MarkedWord α :=
  w.map (fun c=>(c,flag))

theorem marked_decorate (flag : Bool) (w : Word α) (off : Nat) :
    marked flag w=IndexedMarked.decorate (fun _=>flag) off w := by
  induction w generalizing off with
  | nil => rfl
  | cons c cs ih =>
    change (c,flag)::marked flag cs=(c,flag)::IndexedMarked.decorate (fun _=>flag) (off+1) cs
    rw [ih]

theorem marked_length (flag : Bool) (w : Word α) : (marked flag w).length=w.length :=
  List.length_map _

theorem marked_slice (flag : Bool) (w : Word α) (l r : Nat) :
    slice (marked flag w) l r=marked flag (slice w l r) := by
  simp only [slice,marked,List.map_drop,List.map_take]

theorem pre_letter (d b : DFA α) (c : α) (flag : Bool)
    (v : MarkedTransfer.Phase d b→Bool) (p : MarkedTransfer.Phase d b) :
    pre (MarkedTransfer.enum d b) (MarkedTransfer.letter d b (c,flag)) v p=
      pre (MarkedTransfer.enum d b) (MarkedTransfer.epsilon d b flag)
        (fun q=>v (MarkedTransfer.advance d b c q)) p := by
  rw [MarkedTransfer.letter,pre_comp]
  congr 1
  funext q
  rw [pre_deterministic]

theorem closed_left (d b : DFA α) (w : Word α)
    (v : MarkedTransfer.Phase d b→Bool) (q : Fin d.stateCount) :
    pre (MarkedTransfer.enum d b) (MarkedTransfer.transfer d b (marked false w)) v (.inl q)=
      v (.inl (d.run q w)) := by
  induction w generalizing q with
  | nil => exact pre_ident _ _ _
  | cons c cs ih =>
    change pre (MarkedTransfer.enum d b) (comp (MarkedTransfer.enum d b)
      (MarkedTransfer.letter d b (c,false)) (MarkedTransfer.transfer d b (marked false cs))) v (.inl q)=_
    rw [pre_comp,pre_letter,MarkedTransfer.epsilon_left]
    simp only [Bool.false_and,Bool.or_false,MarkedTransfer.advance]
    exact ih _

theorem closed_right (d b : DFA α) (w : Word α)
    (v : MarkedTransfer.Phase d b→Bool) (q : Fin b.stateCount) :
    pre (MarkedTransfer.enum d b) (MarkedTransfer.transfer d b (marked false w)) v (.inr q)=
      v (.inr (b.run q w)) := by
  induction w generalizing q with
  | nil => exact pre_ident _ _ _
  | cons c cs ih =>
    change pre (MarkedTransfer.enum d b) (comp (MarkedTransfer.enum d b)
      (MarkedTransfer.letter d b (c,false)) (MarkedTransfer.transfer d b (marked false cs))) v (.inr q)=_
    rw [pre_comp,pre_letter,MarkedTransfer.epsilon_right]
    exact ih _

def suffixDFA (b : DFA α) (z : Word α) : DFA α :=
  ⟨b.stateCount,b.initial,b.step,fun q=>b.final (b.run q z)⟩

theorem suffix_run (b : DFA α) (z w : Word α) (q : Fin b.stateCount) :
    (suffixDFA b z).run q w=b.run q w := by
  induction w generalizing q with
  | nil => rfl
  | cons c cs ih => exact ih _

theorem suffix_accepts (b : DFA α) (z w : Word α) :
    (suffixDFA b z).accepts w ↔ b.accepts (w++z) := by
  change b.final (b.run ((suffixDFA b z).run b.initial w) z)=true ↔
    b.final (b.run b.initial (w++z))=true
  rw [suffix_run,DFA.run_append]

theorem closed_final (d b : DFA α) (z : Word α) :
    pre (MarkedTransfer.enum d b) (MarkedTransfer.transfer d b (marked false z))
      (MarkedTransfer.final d b)=MarkedTransfer.final d (suffixDFA b z) := by
  funext p
  cases p with
  | inl q => rw [closed_left]; rfl
  | inr q => rw [closed_right]; rfl

theorem suffix_epsilon (d b : DFA α) (z : Word α) (flag : Bool) :
    MarkedTransfer.epsilon d (suffixDFA b z) flag=MarkedTransfer.epsilon d b flag := by
  funext p q
  cases p <;> cases q <;> rfl

theorem suffix_advance (d b : DFA α) (z : Word α) (c : α) :
    MarkedTransfer.advance d (suffixDFA b z) c=MarkedTransfer.advance d b c := by
  funext p
  cases p <;> rfl

theorem suffix_letter (d b : DFA α) (z : Word α) (c : α×Bool) :
    MarkedTransfer.letter d (suffixDFA b z) c=MarkedTransfer.letter d b c := by
  simp only [MarkedTransfer.letter,suffix_epsilon,suffix_advance]
  rfl

theorem suffix_transfer (d b : DFA α) (z : Word α) (w : MarkedDP.MarkedWord α) :
    MarkedTransfer.transfer d (suffixDFA b z) w=MarkedTransfer.transfer d b w := by
  have hl : MarkedTransfer.letter d (suffixDFA b z)=MarkedTransfer.letter d b :=
    funext (suffix_letter d b z)
  simp only [MarkedTransfer.transfer,hl]
  rfl

def windowRelation (d b : DFA α) (x y z : Word α) : Rel (MarkedTransfer.Phase d b) :=
  let e := MarkedTransfer.enum d b
  comp e (comp e (comp e
    (MarkedTransfer.transfer d b (marked false x))
    (MarkedTransfer.transfer d b (marked true y)))
    (MarkedTransfer.epsilon d b true))
    (MarkedTransfer.transfer d b (marked false z))

theorem window_run (d b : DFA α) (x y z : Word α) (q : Fin d.stateCount) :
    pre (MarkedTransfer.enum d b) (windowRelation d b x y z) (MarkedTransfer.final d b) (.inl q)=
      MarkedTransfer.run d (suffixDFA b z) true (marked true y) (.inl (d.run q x)) := by
  unfold windowRelation
  rw [pre_comp,closed_final,pre_comp,pre_comp,closed_left]
  unfold MarkedTransfer.run
  rw [suffix_transfer,suffix_epsilon]
  rfl

theorem window_factor (d b : DFA α) (x y z : Word α) (q : Fin d.stateCount) :
    pre (MarkedTransfer.enum d b) (windowRelation d b x y z) (MarkedTransfer.final d b) (.inl q)=true ↔
      ∃ i, i≤y.length ∧ d.final (d.run q (x++y.take i))=true ∧ b.accepts (y.drop i++z) := by
  rw [window_run,marked_decorate true y 0]
  have hh := IndexedMarked.switch_iff_offset d (suffixDFA b z) (fun _=>true) 0 y (d.run q x)
  simpa only [true_and,suffix_accepts,DFA.run_append] using hh

structure Index (d b : DFA α) where
  closed : DyadicIndex.Tree (MatrixTable.Matrix (MarkedTransfer.enum d b))
  opened : DyadicIndex.Tree (MatrixTable.Matrix (MarkedTransfer.enum d b))
  exit : MatrixTable.Matrix (MarkedTransfer.enum d b)

/-- The count is the number of matrix products in the two actual index
constructions. Leaf matrix construction has fixed pattern-only cost. -/
def build (d b : DFA α) (w : Word α) : Index d b×Nat :=
  let closed := IndexedMarked.build d b (marked false w)
  let opened := IndexedMarked.build d b (marked true w)
  (⟨closed.1,opened.1,MatrixTable.ofRel _ (MarkedTransfer.epsilon d b true)⟩,closed.2+opened.2)

theorem build_products (d b : DFA α) (w : Word α) :
    (build d b w).2=2*((Nat.log2 w.length+1)*w.length) := by
  simp only [build,IndexedMarked.build_cost,marked_length,Nat.two_mul]

structure Result where
  answer : Option Bool
  products : Nat
  visits : Nat

/-- Allowed cuts are a≤i≤bnd. The explicit exit matrix retains i=bnd,
including a=bnd, a=l, and bnd=r. -/
def query (d b : DFA α) (idx : Index d b) (l a bnd r : Nat) (q : Fin d.stateCount) : Result :=
  let o := MatrixTable.ops (MarkedTransfer.enum d b)
  let left := DyadicIndex.query o idx.closed l a
  let middle := DyadicIndex.query o idx.opened a bnd
  let right := DyadicIndex.query o idx.closed bnd r
  let ans := left.answer.bind (fun x=>middle.answer.bind (fun y=>right.answer.map (fun z=>
    pre (MarkedTransfer.enum d b)
      (MatrixTable.denote (o.mul (o.mul (o.mul x y) idx.exit) z))
      (MarkedTransfer.final d b) (.inl q))))
  ⟨ans,left.products+middle.products+right.products+3,
    left.visits+middle.visits+right.visits⟩

theorem range_value (d b : DFA α) (w : Word α) (flag : Bool) (l r : Nat)
    (hl : l≤r) (hr : r≤w.length) :
    (DyadicIndex.query (MatrixTable.ops (MarkedTransfer.enum d b))
      (IndexedMarked.build d b (marked flag w)).1 l r).answer=
    some (RangeProducts.product (MatrixTable.ops (MarkedTransfer.enum d b))
      (MarkedTransfer.matrixLetters d b (marked flag (slice w l r)))) := by
  have hh := (DyadicIndex.queryFor_spec (MatrixTable.ops (MarkedTransfer.enum d b))
    (MarkedTransfer.matrixLetters d b (marked flag w)) l r hl
    (by simpa only [MarkedTransfer.matrixLetters_length,marked_length] using hr)).1
  simpa only [IndexedMarked.build,MarkedTransfer.matrixLetters_slice,marked_slice] using hh

private theorem denote_ops_mul (d b : DFA α)
    (x y : MatrixTable.Matrix (MarkedTransfer.enum d b)) :
    MatrixTable.denote ((MatrixTable.ops (MarkedTransfer.enum d b)).mul x y)=
      comp (MarkedTransfer.enum d b) (MatrixTable.denote x) (MatrixTable.denote y) :=
  MatrixTable.denote_mul _ _ _

theorem query_value (d b : DFA α) (w : Word α) (l a bnd r : Nat) (q : Fin d.stateCount)
    (hla : l≤a) (hab : a≤bnd) (hbr : bnd≤r) (hr : r≤w.length) :
    (query d b (build d b w).1 l a bnd r q).answer=some
      (pre (MarkedTransfer.enum d b)
        (windowRelation d b (slice w l a) (slice w a bnd) (slice w bnd r))
        (MarkedTransfer.final d b) (.inl q)) := by
  simp only [query,build]
  rw [range_value d b w false l a hla (by omega),
    range_value d b w true a bnd hab (by omega),range_value d b w false bnd r hbr hr]
  simp only [Option.bind,Option.map,denote_ops_mul,
    MatrixTable.denote_ofRel,MarkedTransfer.matrix_product_correct,windowRelation]

private theorem take_slice (w : Word α) (l i r : Nat)
    (hli : l≤i) (hir : i≤r) (hr : r≤w.length) :
    (slice w l r).take (i-l)=slice w l i := by
  have hh := OuterColumn.slice_length w l i hli (by omega)
  rw [OuterColumn.slice_split w l i r hli hir,← hh,List.take_left]

private theorem drop_slice (w : Word α) (l i r : Nat)
    (hli : l≤i) (hir : i≤r) (hr : r≤w.length) :
    (slice w l r).drop (i-l)=slice w i r := by
  have hh := OuterColumn.slice_length w l i hli (by omega)
  rw [OuterColumn.slice_split w l i r hli hir,← hh,List.drop_left]

theorem query_correct (d b : DFA α) (w : Word α) (l a bnd r : Nat) (q : Fin d.stateCount)
    (hla : l≤a) (hab : a≤bnd) (hbr : bnd≤r) (hr : r≤w.length) :
    (query d b (build d b w).1 l a bnd r q).answer=some true ↔
      ∃ i, a≤i ∧ i≤bnd ∧ d.final (d.run q (slice w l i))=true ∧ b.accepts (slice w i r) := by
  rw [query_value _ _ _ _ _ _ _ _ hla hab hbr hr,Option.some.injEq,window_factor]
  have hlen := OuterColumn.slice_length w a bnd hab (by omega)
  constructor
  · rintro ⟨j,hj,hd,hb⟩
    have hai : a≤a+j := by omega
    have hib : a+j≤bnd := by omega
    have haij : a+j-a=j := by omega
    rw [← haij,take_slice w a (a+j) bnd hai hib (by omega),
      ← OuterColumn.slice_split w l a (a+j) hla hai] at hd
    rw [← haij,drop_slice w a (a+j) bnd hai hib (by omega),
      ← OuterColumn.slice_split w (a+j) bnd r hib hbr] at hb
    exact ⟨a+j,hai,hib,hd,hb⟩
  · rintro ⟨i,hai,hib,hd,hb⟩
    refine ⟨i-a,by omega,?_,?_⟩
    · rw [take_slice w a i bnd hai hib (by omega),
        ← OuterColumn.slice_split w l a i hla hai]
      exact hd
    · rw [drop_slice w a i bnd hai hib (by omega),
        ← OuterColumn.slice_split w i bnd r hib hbr]
      exact hb

theorem range_bounds (d b : DFA α) (w : Word α) (flag : Bool) (l r : Nat)
    (hl : l≤r) (hr : r≤w.length) :
    (DyadicIndex.query (MatrixTable.ops (MarkedTransfer.enum d b))
      (IndexedMarked.build d b (marked flag w)).1 l r).products≤1 ∧
    (DyadicIndex.query (MatrixTable.ops (MarkedTransfer.enum d b))
      (IndexedMarked.build d b (marked flag w)).1 l r).visits≤Nat.log2 w.length+2 := by
  have hh := (DyadicIndex.queryFor_spec (MatrixTable.ops (MarkedTransfer.enum d b))
    (MarkedTransfer.matrixLetters d b (marked flag w)) l r hl
    (by simpa only [MarkedTransfer.matrixLetters_length,marked_length] using hr)).2
  simpa only [IndexedMarked.build,MarkedTransfer.matrixLetters_length,marked_length] using hh

theorem query_bounds (d b : DFA α) (w : Word α) (l a bnd r : Nat) (q : Fin d.stateCount)
    (hla : l≤a) (hab : a≤bnd) (hbr : bnd≤r) (hr : r≤w.length) :
    (query d b (build d b w).1 l a bnd r q).products≤6 ∧
    (query d b (build d b w).1 l a bnd r q).visits≤3*(Nat.log2 w.length+2) := by
  have h1 := range_bounds d b w false l a hla (by omega)
  have h2 := range_bounds d b w true a bnd hab (by omega)
  have h3 := range_bounds d b w false bnd r hbr hr
  simp only [query,build]
  constructor <;> omega

end REWB.BoundaryIndex.Cuts
