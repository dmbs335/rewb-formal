import REWB.BoundaryApplicationStartSummary

/-! Executable top-down state propagation on a forward compressed edge.
The inherited E subset is pushed through the edge; newly accepted cuts
come from the shared switch index. Both rows are materialized, including
noninjective E transitions. The payload keeps the incoming state so a
query can stop strictly before the stored child depth. -/
namespace REWB.BoundaryApplication.StartStep
open REWB.Spec (slice)
open REWB.BoundaryIndex REWB.FiniteRelation
variable {α : Type} {k : Nat}

def image (row : Vector Bool k) (f : Range.Map k) : Vector Bool k×Nat :=
  let cells:=Vector.ofFn (fun q : Fin k=>Counted.scan
    (fun p=>row.get p && decide (f.get p=q)) (List.ofFn id))
  (Vector.ofFn (fun q=>(cells.get q).1),Counted.rowWork cells)

theorem image_get (row : Vector Bool k) (f : Range.Map k) (q : Fin k) :
    (image row f).1.get q=true ↔ ∃p,row.get p=true ∧ f.get p=q := by
  simp only [image,Table.get_ofFn,Counted.scan_value]
  change any (finEnum k) _=true ↔ _
  simp only [any_true,Bool.and_eq_true,decide_eq_true_eq]

theorem image_steps (row : Vector Bool k) (f : Range.Map k) : (image row f).2=k*(k+1) := by
  apply Counted.rowWork_uniform
  intro q
  simp only [Table.get_ofFn,Counted.scan_steps,List.length_ofFn]

structure Entry (B C E : DFA α) where
  start : Nat
  depth : Nat
  parentDepth : Nat
  beta : Fin B.stateCount
  incoming : StartCuts.Row E
  accepted : StartCuts.Row C

structure Result (E : DFA α) where
  states : StartCuts.Row E
  work : Nat

def query (B C E : DFA α) (cuts : StartCuts.Index B C E) (cranges : Range.Index C)
    (eranges : Range.Index E) (entry : Entry B C E) (m : Nat) : Result E :=
  let fresh:=StartPartial.query B C E cuts cranges (entry.start+entry.parentDepth)
    (entry.start+m) (entry.start+entry.depth) entry.beta entry.accepted
  let emap:=Range.query E eranges (entry.start+entry.parentDepth) (entry.start+m)
  let old:=image entry.incoming emap.map
  let row:=Vector.ofFn (fun q=>old.1.get q || fresh.states.get q)
  ⟨row,fresh.work+emap.work+old.2+E.stateCount+4⟩

theorem query_correct (B C E : DFA α) (w : Word α) (entry : Entry B C E) (m : Nat)
    (hp : entry.parentDepth≤m) (hm : m≤entry.depth) (hd : entry.start+entry.depth≤w.length)
    (q : Fin E.stateCount) :
    (query B C E (StartCuts.build B C E w) (Range.build C w) (Range.build E w) entry m).states.get q=true ↔
      (∃p,entry.incoming.get p=true ∧ E.run p (slice w (entry.start+entry.parentDepth) (entry.start+m))=q) ∨
      (∃i,entry.start+entry.parentDepth≤i ∧ i≤entry.start+m ∧
        B.final (B.run entry.beta (slice w (entry.start+entry.parentDepth) i))=true ∧
        entry.accepted.get (C.run C.initial (slice w i (entry.start+entry.depth)))=true ∧
        E.run E.initial (slice w i (entry.start+m))=q) := by
  simp only [query,Table.get_ofFn,Bool.or_eq_true,image_get]
  rw [StartPartial.query_correct B C E w _ _ _ (by omega) (by omega) hd]
  simp only [Range.query_correct E w (entry.start+entry.parentDepth) (entry.start+m)
    (by omega) (by omega)]

def budget (B C E : DFA α) (n : Nat) : Nat :=
  9+24*(n.log2+2)+2*C.stateCount+2*E.stateCount+E.stateCount*(E.stateCount+1)+
    E.stateCount*((MarkedTransfer.enum B (StartCuts.rightDFA C E)).elems.length+1)

theorem query_work (B C E : DFA α) (w : Word α) (entry : Entry B C E) (m : Nat)
    (hp : entry.parentDepth≤m) (hm : m≤entry.depth) (hd : entry.start+entry.depth≤w.length) :
    (query B C E (StartCuts.build B C E w) (Range.build C w) (Range.build E w) entry m).work≤
      budget B C E w.length := by
  have hc:=StartPartial.query_work B C E w (entry.start+entry.parentDepth) (entry.start+m)
    (entry.start+entry.depth) (by omega) (by omega) hd entry.beta entry.accepted
  have he:=Range.query_work E w (entry.start+entry.parentDepth) (entry.start+m) (by omega) (by omega)
  simp only [query,image_steps,budget]
  omega

structure Bottom (B E : DFA α) where
  beta : Fin B.stateCount
  states : StartCuts.Row E
  work : Nat

def advance (B C E : DFA α) (cuts : StartCuts.Index B C E) (branges : Range.Index B)
    (cranges : Range.Index C) (eranges : Range.Index E) (entry : Entry B C E) : Bottom B E :=
  let bmap:=Range.query B branges (entry.start+entry.parentDepth) (entry.start+entry.depth)
  let result:=query B C E cuts cranges eranges entry entry.depth
  ⟨bmap.map.get entry.beta,result.states,result.work+bmap.work+2⟩

theorem advance_beta (B C E : DFA α) (w : Word α) (entry : Entry B C E)
    (hp : entry.parentDepth≤entry.depth) (hd : entry.start+entry.depth≤w.length) :
    (advance B C E (StartCuts.build B C E w) (Range.build B w) (Range.build C w) (Range.build E w) entry).beta=
      B.run entry.beta (slice w (entry.start+entry.parentDepth) (entry.start+entry.depth)) :=
  Range.query_correct B w _ _ (by omega) hd entry.beta

theorem advance_work (B C E : DFA α) (w : Word α) (entry : Entry B C E)
    (hp : entry.parentDepth≤entry.depth) (hd : entry.start+entry.depth≤w.length) :
    (advance B C E (StartCuts.build B C E w) (Range.build B w) (Range.build C w) (Range.build E w) entry).work≤
      budget B C E w.length+B.stateCount+8*(w.length.log2+2)+3 := by
  have hq:=query_work B C E w entry entry.depth hp (Nat.le_refl _) hd
  have hb:=Range.query_work B w (entry.start+entry.parentDepth) (entry.start+entry.depth) (by omega) hd
  simp only [advance]
  omega

def accept (E : DFA α) (row : StartCuts.Row E) : Bool×Nat :=
  Counted.scan (fun q=>row.get q && E.final q) (List.ofFn id)

theorem accept_correct (E : DFA α) (row : StartCuts.Row E) :
    (accept E row).1=true ↔ ∃q,row.get q=true ∧ E.final q=true := by
  simp only [accept,Counted.scan_value]
  change any (finEnum E.stateCount) _=true ↔ _
  simp only [any_true,Bool.and_eq_true]

theorem accept_work (E : DFA α) (row : StartCuts.Row E) : (accept E row).2=E.stateCount := by
  simp only [accept,Counted.scan_steps,List.length_ofFn]

end REWB.BoundaryApplication.StartStep
