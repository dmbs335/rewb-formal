import REWB.BoundaryIndexColors

/-! End-to-end queries for a finite stream of text letters and inserted
colored endpoints. The query uses the stream prefix ending at the requested
right boundary; accepted endpoints are characterized by the exact intervening
word. Old tree versions and prefixes remain independently queryable. -/
namespace REWB.BoundaryIndex.TokenIndex
variable {α : Type} {k h : Nat}

/-- Padding to a power of two does not introduce an endpoint or a letter. -/
def build (d : DFA α) (xs : List (Token α k)) (h : Nat) : Tree k d.stateCount h×Nat :=
  let out := Tree.build (xs.map (atom d)).toArray h 0
  (out.1,xs.length*Tree.leafBudget k d.stateCount+out.2)

theorem build_good (d : DFA α) (xs : List (Token α k)) (h : Nat) :
    Tree.Good (build d xs h).1 := Tree.build_good _ _ _

/-- n is a boundary in the letter/endpoint stream. Erasing markers gives
the corresponding boundary in the input text. -/
def query (d : DFA α) (select : Fin k→Bool) (t : Tree k d.stateCount h) (n : Nat) : Bool×Nat :=
  let part := Tree.queryPrefix t n
  let out := Counted.accepted d select part.1
  (out.1,part.2+out.2)

theorem query_steps (d : DFA α) (select : Fin k→Bool)
    (t : Tree k d.stateCount h) (n : Nat) :
    (query d select t n).2≤(h+1)*Tree.queryBudget k d.stateCount+k+k*d.stateCount := by
  have hp := Tree.queryPrefix_steps t n
  simp only [query,Counted.accepted_steps]
  omega

/-- A complete exact query over the actual built finite array. No inverse
DFA transition, injective color map, or supplied answer oracle is assumed. -/
theorem query_build_correct (d : DFA α) (select : Fin k→Bool)
    (xs : List (Token α k)) (h n : Nat) (hn : n≤xs.length) (hc : n≤2^h) :
    (query d select (build d xs h).1 n).1=true ↔
      ∃ pre post c, xs.take n=pre++Token.mark c::post ∧
        select c=true ∧ d.accepts (erase post) := by
  have hv : (Tree.queryPrefix (build d xs h).1 n).1.view=trace d (xs.take n) := by
    unfold build
    rw [Tree.queryPrefix_build _ h n (by simpa using hn) hc]
    simp only [← List.map_take,List.map_map,trace,Function.comp_def]
  simp only [query,Counted.accepted_value]
  exact accepted_trace d select _ _ hv

/-- Lazy relabeling preserves all endpoint possibilities, including when
multiple old colors merge. The returned right-boundary suffix is exact. -/
theorem recolored_query_correct (d : DFA α) (select : Fin k→Bool)
    (xs : List (Token α k)) (h n : Nat) (hn : n≤xs.length) (hc : n≤2^h)
    (g : Vector (Fin k) k) :
    (query d select (Tree.recolor g (build d xs h).1).1 n).1=true ↔
      ∃ pre post c, xs.take n=pre++Token.mark c::post ∧
        select (g.get c)=true ∧ d.accepts (erase post) := by
  have hv : (Tree.queryPrefix (Tree.recolor g (build d xs h).1).1 n).1.view=
      View.rename g.get (trace d (xs.take n)) := by
    rw [Tree.queryPrefix_correct _ (Tree.recolor_good _ _ (build_good _ _ _)),
      Tree.recolor_leaves,← List.map_take,← View.rename_product]
    congr 1
    unfold build
    rw [Tree.build_take _ h n (by simpa using hn) hc]
    simp only [← List.map_take,List.map_map,trace,Function.comp_def]
  simp only [query,Counted.accepted_value,accepted_true,hv,View.rename_active,
    trace_active,Active,DFA.accepts]
  constructor
  · rintro ⟨color,q,hs,⟨old,he,pre,post,hx,hr⟩,hf⟩
    exact ⟨pre,post,old,hx,he ▸ hs,by rw [hr]; exact hf⟩
  · rintro ⟨pre,post,old,hx,hs,hf⟩
    exact ⟨g.get old,d.run d.initial (erase post),hs,
      ⟨old,rfl,pre,post,hx,rfl⟩,hf⟩

/-- Automatic logarithmic height and fully charged input-cell generation. -/
def buildFor (d : DFA α) (xs : List (Token α k)) :
    Tree k d.stateCount (Tree.heightFor xs.length)×Nat :=
  build d xs (Tree.heightFor xs.length)

theorem buildFor_good (d : DFA α) (xs : List (Token α k)) :
    Tree.Good (buildFor d xs).1 := build_good _ _ _

theorem buildFor_steps (d : DFA α) (xs : List (Token α k)) :
    (buildFor d xs).2≤xs.length*Tree.leafBudget k d.stateCount+
      2*(xs.length+1)*(Tree.joinBudget k d.stateCount+Tree.leafBudget k d.stateCount) := by
  have he := Tree.build_steps ((xs.map (atom d)).toArray) (Tree.heightFor xs.length) 0
  have hh := Nat.mul_le_mul_right (Tree.joinBudget k d.stateCount+Tree.leafBudget k d.stateCount)
    (Tree.capacity_upper xs.length)
  simp only [buildFor,build]
  omega

theorem queryFor_correct (d : DFA α) (select : Fin k→Bool)
    (xs : List (Token α k)) (n : Nat) (hn : n≤xs.length) :
    (query d select (buildFor d xs).1 n).1=true ↔
      ∃ pre post c, xs.take n=pre++Token.mark c::post ∧
        select c=true ∧ d.accepts (erase post) :=
  query_build_correct _ _ _ _ _ hn (Nat.le_trans hn (Tree.capacity xs.length))

theorem queryFor_steps (d : DFA α) (select : Fin k→Bool)
    (xs : List (Token α k)) (n : Nat) :
    (query d select (buildFor d xs).1 n).2≤
      (Nat.log2 xs.length+2)*Tree.queryBudget k d.stateCount+k+k*d.stateCount :=
  query_steps _ _ _ _

end REWB.BoundaryIndex.TokenIndex
