import REWB.BoundaryApplicationSeparatedCost

/-! Kernel regressions for empty cuts, genuinely separated boundaries,
the source-side cutoff, noninjective color coalescence, and the exact E
endpoint-after-letter convention. No native evaluator is used in proofs. -/
namespace REWB.BoundaryApplication.Separated.Regression
open REWB.Spec (slice)
variable {σ : Nat}

theorem empty_query (A B C D E : DFA (Fin σ)) (fallback : Fin σ) :
    (query E (build A B C D E [] fallback 0 0 (Nat.le_refl 0)) 0).1=true ↔
      A.final A.initial=true ∧ B.final B.initial=true ∧ C.final C.initial=true ∧
        D.final D.initial=true ∧ E.final E.initial=true := by
  rw [query_iff_cuts A B C D E [] fallback 0 0 (Nat.le_refl 0) (Nat.le_refl 0) 0 (Nat.le_refl 0)]
  constructor
  · rintro ⟨a,L,t,_,_,_,_,_,hA,hB,hC,hD,hE⟩
    simp only [DFA.accepts,slice,List.drop_nil,List.take_nil,DFA.run] at hA hB hC hD hE
    exact ⟨hA,hB,hC,hD,hE⟩
  · rintro ⟨hA,hB,hC,hD,hE⟩
    exact ⟨0,0,0,Nat.le_refl 0,Nat.le_refl 0,Nat.le_refl 0,Nat.le_refl 0,rfl,hA,hB,hC,hD,hE⟩

def allWords : DFA (Fin 2) := ⟨1,0,fun _ _=>0,fun _=>true⟩
def epsilon : DFA (Fin 2) := ⟨2,0,fun _ _=>1,fun q=>decide (q=0)⟩
def nonempty : DFA (Fin 2) := ⟨2,0,fun _ _=>1,fun q=>decide (q=1)⟩
def word : Word (Fin 2) := [0,1,0]

/-- The matching zeroes surround two different fixed boundaries. A, C,
D and E are epsilon, fixing source=1 and target=3 uniquely. -/
theorem distinct_boundaries :
    (query epsilon (build epsilon nonempty epsilon epsilon epsilon word 0 1 2 (by decide)) 3).1=true := by
  apply (query_iff_cuts epsilon nonempty epsilon epsilon epsilon word 0 1 2 (by decide) (by decide) 3 (by decide)).mpr
  refine ⟨1,1,3,by decide,by decide,by decide,by decide,?_,?_,?_,?_,?_,?_⟩
  all_goals first | decide | (unfold DFA.accepts; decide)

/-- Moving g0 before the first source letter removes every nonempty
repeat even though the target side and g1 are unchanged. -/
theorem source_boundary_respected :
    (query epsilon (build epsilon nonempty epsilon epsilon epsilon word 0 0 2 (by decide)) 3).1=false := by
  cases hv : (query epsilon (build epsilon nonempty epsilon epsilon epsilon word 0 0 2 (by decide)) 3).1 with
  | false => rfl
  | true =>
    obtain ⟨a,L,t,ha,hL,_,_,_,_,hB,_,_,_⟩:=
      (query_iff_cuts epsilon nonempty epsilon epsilon epsilon word 0 0 2 (by decide) (by decide) 3 (by decide)).mp hv
    have ha0 : a=0 := by omega
    have hL0 : L=0 := by omega
    subst a
    subst L
    have hn : ¬nonempty.accepts (slice word 0 0) := by unfold DFA.accepts; decide
    exact False.elim (hn hB)

theorem noninjective_source_colors :
    (StartStep.image (Vector.ofFn (fun _ : Fin 2=>true)) (Vector.ofFn (fun _ : Fin 2=>1))).1.get 0=false ∧
    (StartStep.image (Vector.ofFn (fun _ : Fin 2=>true)) (Vector.ofFn (fun _ : Fin 2=>1))).1.get 1=true := by
  decide

def onlyTwo : Vector Bool (word.length+1) := Vector.ofFn (fun i=>decide (i.val=2))

/-- Cell 2 seeds after the second letter. Its epsilon suffix is accepted
at right=2 and rejected after the following zero or before the endpoint. -/
theorem endpoint_after_letter :
    (Suffix.query epsilon (Suffix.build epsilon word onlyTwo) 1).1=false ∧
    (Suffix.query epsilon (Suffix.build epsilon word onlyTwo) 2).1=true ∧
    (Suffix.query epsilon (Suffix.build epsilon word onlyTwo) 3).1=false := by
  refine ⟨?_,?_,?_⟩
  · cases hv : (Suffix.query epsilon (Suffix.build epsilon word onlyTwo) 1).1 with
    | false => rfl
    | true =>
      obtain ⟨target,ht,hbit,_⟩:=(Suffix.query_correct epsilon word onlyTwo 1 (by decide)).mp hv
      have hb : target.val=2 := by simpa only [onlyTwo,BoundaryIndex.Table.get_ofFn,decide_eq_true_eq] using hbit
      omega
  · apply (Suffix.query_correct epsilon word onlyTwo 2 (by decide)).mpr
    refine ⟨⟨2,by decide⟩,by decide,?_,?_⟩
    · simp only [onlyTwo,BoundaryIndex.Table.get_ofFn,decide_true]
    · unfold DFA.accepts; decide
  · cases hv : (Suffix.query epsilon (Suffix.build epsilon word onlyTwo) 3).1 with
    | false => rfl
    | true =>
      obtain ⟨target,_,hbit,hE⟩:=(Suffix.query_correct epsilon word onlyTwo 3 (by decide)).mp hv
      have hb : target.val=2 := by simpa only [onlyTwo,BoundaryIndex.Table.get_ofFn,decide_eq_true_eq] using hbit
      rw [hb] at hE
      have hn : ¬epsilon.accepts (slice word 2 3) := by unfold DFA.accepts; decide
      exact False.elim (hn hE)

end REWB.BoundaryApplication.Separated.Regression
