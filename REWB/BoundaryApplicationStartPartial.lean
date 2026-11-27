import REWB.BoundaryApplicationStartCuts

/-! An actual compressed-edge cutoff query. The C condition lives at a
child depth beyond the cutoff. One shared C range query pulls it back;
the switch index then enumerates all allowed cuts only in its finite
matrix, without enumerating text positions. -/
namespace REWB.BoundaryApplication.StartPartial
open REWB.Spec (slice)
open REWB.BoundaryIndex
variable {α : Type}

def pull (C : DFA α) (accepted : StartCuts.Row C) (f : Range.Map C.stateCount) : StartCuts.Row C :=
  Vector.ofFn (fun q=>accepted.get (f.get q))

@[simp] theorem pull_get (C : DFA α) (accepted : StartCuts.Row C) (f : Range.Map C.stateCount)
    (q : Fin C.stateCount) : (pull C accepted f).get q=accepted.get (f.get q) :=
  Table.get_ofFn _ _

structure Result (E : DFA α) where
  cuts : StartCuts.Result E
  tailWork : Nat

def Result.states {E : DFA α} (r : Result E) : StartCuts.Row E := r.cuts.states
def Result.work {E : DFA α} (r : Result E) : Nat := r.cuts.work+r.tailWork

def query (B C E : DFA α) (cuts : StartCuts.Index B C E) (ranges : Range.Index C)
    (l m d : Nat) (beta : Fin B.stateCount) (accepted : StartCuts.Row C) : Result E :=
  let tail:=Range.query C ranges m d
  let cut:=StartCuts.query B C E cuts l m beta (pull C accepted tail.map)
  ⟨cut,tail.work+C.stateCount+1⟩

theorem query_correct (B C E : DFA α) (w : Word α) (l m d : Nat)
    (hl : l≤m) (hm : m≤d) (hd : d≤w.length) (beta : Fin B.stateCount)
    (accepted : StartCuts.Row C) (q : Fin E.stateCount) :
    (query B C E (StartCuts.build B C E w) (Range.build C w) l m d beta accepted).states.get q=true ↔
      ∃i,l≤i ∧ i≤m ∧ B.final (B.run beta (slice w l i))=true ∧
        accepted.get (C.run C.initial (slice w i d))=true ∧ E.run E.initial (slice w i m)=q := by
  simp only [query,Result.states]
  rw [StartCuts.query_correct B C E w l m hl (by omega)]
  simp only [pull_get,Range.query_correct C w m d hm hd]
  have hc (i : Nat) (hi : i≤m) :
      C.run (C.run C.initial (slice w i m)) (slice w m d)=C.run C.initial (slice w i d) := by
    rw [OuterColumn.slice_split w i m d hi hm,DFA.run_append]
  constructor
  · rintro ⟨i,hli,him,hb,hc',he⟩
    exact ⟨i,hli,him,hb,by rwa [hc i him] at hc',he⟩
  · rintro ⟨i,hli,him,hb,hc',he⟩
    exact ⟨i,hli,him,hb,by rwa [hc i him],he⟩

theorem query_work (B C E : DFA α) (w : Word α) (l m d : Nat)
    (hl : l≤m) (hm : m≤d) (hd : d≤w.length) (beta : Fin B.stateCount)
    (accepted : StartCuts.Row C) :
    (query B C E (StartCuts.build B C E w) (Range.build C w) l m d beta accepted).work≤
      4+16*(w.length.log2+2)+2*C.stateCount+
        E.stateCount*((MarkedTransfer.enum B (StartCuts.rightDFA C E)).elems.length+1) := by
  have hc:=StartCuts.query_work B C E w l m hl (by omega) beta
    (pull C accepted (Range.query C (Range.build C w) m d).map)
  have ht:=Range.query_work C w m d hm hd
  simp only [Result.work,query]
  omega

end REWB.BoundaryApplication.StartPartial
