import REWB.BoundaryApplicationStartCost

/-! Kernel regressions for the actual fixed-start query. The complete
index is connected through query_correct; witnesses are checked on the
original slices, without evaluating large transition matrices in proofs. -/
namespace REWB.BoundaryApplication.StartRegression
open REWB.Spec (slice)
variable {σ : Nat}

/-- All four empty-word acceptance conditions survive the empty text,
zero boundary, source/target duplicate strings, and zero-length cuts. -/
theorem empty_query (A B C E : DFA (Fin σ)) (fallback : Fin σ) :
    (StartIndex.query B C E (StartIndex.build A B C E [] fallback 0 (Nat.le_refl 0)) 0 0).value=true ↔
      A.final A.initial=true ∧ B.final B.initial=true ∧ C.final C.initial=true ∧ E.final E.initial=true := by
  rw [StartIndex.query_correct A B C E [] fallback 0 (Nat.le_refl 0) 0 (Nat.le_refl 0) 0 (Nat.le_refl 0) (Nat.le_refl 0)]
  constructor
  · rintro ⟨i,_,L,_,_,_,hA,hB,hC,hE⟩
    refine ⟨?_,?_,?_,?_⟩
    · simpa only [DFA.accepts,slice,List.drop_nil,List.take_nil,DFA.run] using hA
    · simpa only [DFA.accepts,slice,List.drop_nil,List.take_nil,DFA.run] using hB
    · simpa only [DFA.accepts,slice,List.drop_nil,List.take_nil,DFA.run] using hC
    · simpa only [DFA.accepts,slice,List.drop_nil,List.take_nil,DFA.run] using hE
  · rintro ⟨hA,hB,hC,hE⟩
    exact ⟨0,Nat.le_refl 0,0,Nat.le_refl 0,Nat.le_refl 0,rfl,hA,hB,hC,hE⟩

def allWords : DFA (Fin 2) := ⟨1,0,fun _ _=>0,fun _=>true⟩
def epsilon : DFA (Fin 2) := ⟨2,0,fun _ _=>1,fun q=>decide (q=0)⟩
def witnessWord : Word (Fin 2) := [0,1,1,0,1,1]

/-- Source 0 and target 3 share the descriptor `011`. The query ends
after its first letter, strictly inside their common compressed edge;
the accepted E suffix is epsilon at the query's right boundary. -/
theorem strict_partial_query :
    (StartIndex.query allWords allWords epsilon
      (StartIndex.build epsilon allWords allWords epsilon witnessWord 0 3 (by decide)) 3 4).value=true := by
  apply (StartIndex.query_correct epsilon allWords allWords epsilon witnessWord 0 3 (by decide)
    3 (by decide) 4 (by decide) (by decide)).mpr
  refine ⟨0,by decide,1,by decide,by decide,?_,?_,?_,?_,?_⟩
  all_goals first | decide | (unfold DFA.accepts; decide)

/-- Requiring both the repeated factor and its following suffix to be
empty rejects a nonempty query interval; epsilon is not accepted at an
unrelated internal position. -/
theorem epsilon_not_both :
    (StartIndex.query epsilon allWords epsilon
      (StartIndex.build epsilon epsilon allWords epsilon witnessWord 0 3 (by decide)) 3 4).value=false := by
  cases hv : (StartIndex.query epsilon allWords epsilon
      (StartIndex.build epsilon epsilon allWords epsilon witnessWord 0 3 (by decide)) 3 4).value with
  | false => rfl
  | true =>
    obtain ⟨i,_,L,_,hL,_,_,hB,_,hE⟩:=
      (StartIndex.query_correct epsilon epsilon allWords epsilon witnessWord 0 3 (by decide)
        3 (by decide) 4 (by decide) (by decide)).mp hv
    have hlen : L=0 ∨ L=1 := by change 3+L≤4 at hL; omega
    rcases hlen with hz | ho
    · subst L
      have hn : ¬epsilon.accepts (slice witnessWord 3 4) := by unfold DFA.accepts; decide
      exact False.elim (hn hE)
    · subst L
      have hn : ¬epsilon.accepts (slice witnessWord 3 4) := by unfold DFA.accepts; decide
      exact False.elim (hn hB)

/-- A reset transition coalesces both live E states into one materialized
state; the image operation does not require an inverse transition. -/
theorem noninjective_E_image :
    (StartStep.image (Vector.ofFn (fun _ : Fin 2=>true)) (Vector.ofFn (fun _ : Fin 2=>1))).1.get 0=false ∧
    (StartStep.image (Vector.ofFn (fun _ : Fin 2=>true)) (Vector.ofFn (fun _ : Fin 2=>1))).1.get 1=true := by
  decide

end REWB.BoundaryApplication.StartRegression
