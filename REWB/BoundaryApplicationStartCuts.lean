import REWB.BoundaryApplicationRange
import REWB.BoundaryIndexFixedEnd

/-! Fixed-start compressed-edge cut summaries. One shared materialized
switch index has B states before the cut and C×E states after it. A query
accepts a dynamic C-state subset and returns all reached E states. The
same cut drives all three automata, and the terminal epsilon transition
retains both ends of a closed cut interval. -/
namespace REWB.BoundaryApplication.StartCuts
open REWB.BoundaryIndex
open REWB.FiniteRelation
open REWB.Spec (slice)
variable {α : Type}

abbrev Row (d : DFA α) := Vector Bool d.stateCount

def retarget (d : DFA α) (final : Fin d.stateCount→Bool) : DFA α :=
  ⟨d.stateCount,d.initial,d.step,final⟩

theorem retarget_run (d : DFA α) (final : Fin d.stateCount→Bool) (w : Word α)
    (q : Fin d.stateCount) : (retarget d final).run q w=d.run q w := by
  induction w generalizing q with
  | nil => rfl
  | cons c cs ih => exact ih _

theorem retarget_epsilon (b d : DFA α) (final : Fin d.stateCount→Bool) (flag : Bool) :
    MarkedTransfer.epsilon b (retarget d final) flag=MarkedTransfer.epsilon b d flag := by
  funext p q
  cases p <;> cases q <;> rfl

theorem retarget_advance (b d : DFA α) (final : Fin d.stateCount→Bool) (c : α) :
    MarkedTransfer.advance b (retarget d final) c=MarkedTransfer.advance b d c := by
  funext p
  cases p <;> rfl

theorem retarget_transfer (b d : DFA α) (final : Fin d.stateCount→Bool) (w : MarkedDP.MarkedWord α) :
    MarkedTransfer.transfer b (retarget d final) w=MarkedTransfer.transfer b d w := by
  have hl : MarkedTransfer.letter b (retarget d final)=MarkedTransfer.letter b d := by
    funext x
    simp only [MarkedTransfer.letter,retarget_epsilon,retarget_advance]
    rfl
  simp only [MarkedTransfer.transfer,hl]
  rfl

abbrev rightDFA (C E : DFA α) := BoundaryIndex.FixedEnd.leftDFA C E

def rightFinal (C E : DFA α) (accepted : Row C) (q : Fin E.stateCount) : Fin (rightDFA C E).stateCount→Bool :=
  fun r=>let p:=(BoundaryIndex.FixedEnd.pairMachine C E).decode r
    accepted.get p.1 && decide (p.2=q)

def final (B C E : DFA α) (accepted : Row C) (q : Fin E.stateCount) :
    MarkedTransfer.Phase B (rightDFA C E)→Bool
  | .inl _ => false
  | .inr r => rightFinal C E accepted q r

theorem right_accepts (C E : DFA α) (accepted : Row C) (q : Fin E.stateCount) (w : Word α) :
    (retarget (rightDFA C E) (rightFinal C E accepted q)).accepts w ↔
      accepted.get (C.run C.initial w)=true ∧ E.run E.initial w=q := by
  unfold DFA.accepts
  rw [retarget_run]
  change rightFinal C E accepted q
    ((BoundaryIndex.FixedEnd.pairMachine C E).toDFA.run
      ((BoundaryIndex.FixedEnd.pairMachine C E).encode (C.initial,E.initial)) w)=true ↔ _
  unfold rightFinal
  rw [RegularDFA.Machine.toDFA_run,RegularDFA.Machine.decode_encode,BoundaryIndex.FixedEnd.pair_run]
  simp only [Bool.and_eq_true,decide_eq_true_eq]

structure Index (B C E : DFA α) where
  tree : IndexedMarked.Index B (rightDFA C E)
  exit : MatrixTable.Matrix (MarkedTransfer.enum B (rightDFA C E))
  length : Nat
  products : Nat

def build (B C E : DFA α) (w : Word α) : Index B C E :=
  let out:=IndexedMarked.build B (rightDFA C E) (Cuts.marked true w)
  ⟨out.1,MatrixTable.ofRel _ (MarkedTransfer.epsilon B (rightDFA C E) true),w.length,out.2⟩

theorem build_products (B C E : DFA α) (w : Word α) :
    (build B C E w).products=(w.length.log2+1)*w.length := by
  simp only [build,IndexedMarked.build_cost,Cuts.marked_length]

structure Result (E : DFA α) where
  states : Row E
  products : Nat
  visits : Nat
  rowWork : Nat

def query (B C E : DFA α) (idx : Index B C E) (l r : Nat) (beta : Fin B.stateCount)
    (accepted : Row C) : Result E :=
  let e:=MarkedTransfer.enum B (rightDFA C E)
  let o:=MatrixTable.ops e
  let part:=DyadicIndex.query o idx.tree l r
  let matrix:=o.mul (part.answer.getD o.one) idx.exit
  let cells:=Vector.ofFn fun q : Fin E.stateCount=>Counted.scan
    (fun t=>MatrixTable.denote matrix (.inl beta) t && final B C E accepted q t) e.elems
  ⟨Vector.ofFn (fun q=>(cells.get q).1),part.products+1,part.visits,Counted.rowWork cells⟩

theorem query_row (B C E : DFA α) (idx : Index B C E) (l r : Nat) (beta : Fin B.stateCount)
    (accepted : Row C) (q : Fin E.stateCount) :
    (query B C E idx l r beta accepted).states.get q=
      pre (MarkedTransfer.enum B (rightDFA C E))
        (MatrixTable.denote ((MatrixTable.ops (MarkedTransfer.enum B (rightDFA C E))).mul
          ((DyadicIndex.query (MatrixTable.ops (MarkedTransfer.enum B (rightDFA C E))) idx.tree l r).answer.getD
            (MatrixTable.ops (MarkedTransfer.enum B (rightDFA C E))).one) idx.exit))
        (final B C E accepted q) (.inl beta) := by
  simp only [query,Table.get_ofFn,Counted.scan_value,pre,any]

theorem query_run (B C E : DFA α) (w : Word α) (l r : Nat) (hl : l≤r) (hr : r≤w.length)
    (beta : Fin B.stateCount) (accepted : Row C) (q : Fin E.stateCount) :
    (query B C E (build B C E w) l r beta accepted).states.get q=
      MarkedTransfer.run B (retarget (rightDFA C E) (rightFinal C E accepted q)) true
        (Cuts.marked true (slice w l r)) (.inl beta) := by
  have hh:=(DyadicIndex.queryFor_spec (MatrixTable.ops (MarkedTransfer.enum B (rightDFA C E)))
    (MarkedTransfer.matrixLetters B (rightDFA C E) (Cuts.marked true w)) l r hl
      (by simpa only [MarkedTransfer.matrixLetters_length,Cuts.marked_length] using hr)).1
  rw [query_row]
  simp only [build,IndexedMarked.build] at hh ⊢
  rw [hh,Option.getD_some,MarkedTransfer.matrixLetters_slice,Cuts.marked_slice]
  change pre _ (MatrixTable.denote (MatrixTable.mul _ _ _)) _ _=_
  rw [MatrixTable.denote_mul,MarkedTransfer.matrix_product_correct,MatrixTable.denote_ofRel,pre_comp]
  unfold MarkedTransfer.run
  rw [retarget_transfer,retarget_epsilon]
  have hf : final B C E accepted q=
      MarkedTransfer.final B (retarget (rightDFA C E) (rightFinal C E accepted q)) := by
    funext t
    cases t <;> rfl
  rw [hf]
  rfl

theorem query_correct_relative (B C E : DFA α) (w : Word α) (l r : Nat) (hl : l≤r) (hr : r≤w.length)
    (beta : Fin B.stateCount) (accepted : Row C) (q : Fin E.stateCount) :
    (query B C E (build B C E w) l r beta accepted).states.get q=true ↔
      ∃i,i≤(slice w l r).length ∧
        B.final (B.run beta ((slice w l r).take i))=true ∧
        accepted.get (C.run C.initial ((slice w l r).drop i))=true ∧
        E.run E.initial ((slice w l r).drop i)=q := by
  rw [query_run B C E w l r hl hr beta accepted q,Cuts.marked_decorate true _ 0]
  have hh:=IndexedMarked.switch_iff_offset B (retarget (rightDFA C E) (rightFinal C E accepted q))
    (fun _=>true) 0 (slice w l r) beta
  simpa only [true_and,right_accepts] using hh

private theorem take_slice (w : Word α) (l i r : Nat) (hli : l≤i) (hir : i≤r) (hr : r≤w.length) :
    (slice w l r).take (i-l)=slice w l i := by
  have hh:=OuterColumn.slice_length w l i hli (by omega)
  rw [OuterColumn.slice_split w l i r hli hir,← hh,List.take_left]

private theorem drop_slice (w : Word α) (l i r : Nat) (hli : l≤i) (hir : i≤r) (hr : r≤w.length) :
    (slice w l r).drop (i-l)=slice w i r := by
  have hh:=OuterColumn.slice_length w l i hli (by omega)
  rw [OuterColumn.slice_split w l i r hli hir,← hh,List.drop_left]

theorem query_correct (B C E : DFA α) (w : Word α) (l r : Nat) (hl : l≤r) (hr : r≤w.length)
    (beta : Fin B.stateCount) (accepted : Row C) (q : Fin E.stateCount) :
    (query B C E (build B C E w) l r beta accepted).states.get q=true ↔
      ∃i,l≤i ∧ i≤r ∧ B.final (B.run beta (slice w l i))=true ∧
        accepted.get (C.run C.initial (slice w i r))=true ∧ E.run E.initial (slice w i r)=q := by
  rw [query_correct_relative B C E w l r hl hr beta accepted q]
  have hlen:=OuterColumn.slice_length w l r hl hr
  constructor
  · rintro ⟨i,hi,hb,hc,he⟩
    have hli : l≤l+i := by omega
    have hir : l+i≤r := by omega
    have heq : l+i-l=i := by omega
    rw [← heq,take_slice w l (l+i) r hli hir hr] at hb
    rw [← heq,drop_slice w l (l+i) r hli hir hr] at hc he
    exact ⟨l+i,hli,hir,hb,hc,he⟩
  · rintro ⟨i,hli,hir,hb,hc,he⟩
    refine ⟨i-l,by omega,?_,?_,?_⟩
    · rwa [take_slice w l i r hli hir hr]
    · rwa [drop_slice w l i r hli hir hr]
    · rwa [drop_slice w l i r hli hir hr]

theorem query_bounds (B C E : DFA α) (w : Word α) (l r : Nat) (hl : l≤r) (hr : r≤w.length)
    (beta : Fin B.stateCount) (accepted : Row C) :
    (query B C E (build B C E w) l r beta accepted).products≤2 ∧
    (query B C E (build B C E w) l r beta accepted).visits≤w.length.log2+2 ∧
    (query B C E (build B C E w) l r beta accepted).rowWork=
      E.stateCount*((MarkedTransfer.enum B (rightDFA C E)).elems.length+1) := by
  have hh:=(DyadicIndex.queryFor_spec (MatrixTable.ops (MarkedTransfer.enum B (rightDFA C E)))
    (MarkedTransfer.matrixLetters B (rightDFA C E) (Cuts.marked true w)) l r hl
      (by simpa only [MarkedTransfer.matrixLetters_length,Cuts.marked_length] using hr)).2
  simp only [query,build,IndexedMarked.build]
  refine ⟨by omega,?_,?_⟩
  · simpa only [MarkedTransfer.matrixLetters_length,Cuts.marked_length] using hh.2
  · apply Counted.rowWork_uniform
    intro q
    simp only [Table.get_ofFn,Counted.scan_steps]

def Result.work (r : Result E) : Nat := r.products+8*r.visits+r.rowWork

theorem query_work (B C E : DFA α) (w : Word α) (l r : Nat) (hl : l≤r) (hr : r≤w.length)
    (beta : Fin B.stateCount) (accepted : Row C) :
    (query B C E (build B C E w) l r beta accepted).work≤
      2+8*(w.length.log2+2)+E.stateCount*((MarkedTransfer.enum B (rightDFA C E)).elems.length+1) := by
  have hh:=query_bounds B C E w l r hl hr beta accepted
  unfold Result.work
  omega

end REWB.BoundaryApplication.StartCuts
