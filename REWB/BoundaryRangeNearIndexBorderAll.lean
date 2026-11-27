import REWB.BoundaryRangeNearIndexBorderCost

/-! All four near regions from actual text construction. The union has
one semantic contract: the split p lies before the next grid boundary.
No supplied matching relation or boundary program occurs in the builder. -/
namespace REWB.BoundaryRange.NearIndex.Full
variable {σ : Nat}

structure Index (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ)) (g0 g : Nat) where
  branches : NearIndex.Index A B C K D E w g0 g
  border : Border.Index A B C K D E w
  work : Nat

def build (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g0 g : Nat) (h0g : g0≤g) (hg : g≤w.length) : Index A B C K D E w g0 g :=
  let branches:=NearIndex.build A B C K D E w fallback g0 g h0g hg
  let border:=Border.build A B C K D E w fallback
  ⟨branches,border,branches.work+border.work+1⟩

def query {A B C K D E : DFA (Fin σ)} {w : Word (Fin σ)} {g0 g : Nat}
    (idx : Index A B C K D E w g0 g) (left right : Nat) : Bool×Nat :=
  let branches:=NearIndex.queryThree idx.branches left right
  let border:=Border.query idx.border left right idx.branches.lower idx.branches.upper
  (branches.1 || border.1,branches.2+border.2+1)

theorem query_correct (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g0 g : Nat) (h0g : g0≤g) (hg : g≤w.length) (left right : Nat)
    (h0l : g0≤left) (hlg : left≤g) (hr : right≤w.length) :
    (query (build A B C K D E w fallback g0 g h0g hg) left right).1=true ↔
      Case A B C K D E w left right g0 g .nearSeparated ∨
      Case A B C K D E w left right g0 g .nearEnd ∨
      Case A B C K D E w left right g0 g .nearStart ∨
      Case A B C K D E w left right g0 g .nearBorder := by
  change ((NearIndex.queryThree (NearIndex.build A B C K D E w fallback g0 g h0g hg) left right).1 ||
    (Border.query (Border.build A B C K D E w fallback) left right g0 g).1)=true ↔ _
  rw [Bool.or_eq_true,NearIndex.queryThree_correct A B C K D E w fallback g0 g h0g hg left right h0l hlg hr,
    Border.query_correct A B C K D E w fallback left right g0 g hg hr]
  simp only [or_assoc]

theorem query_iff (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g0 g : Nat) (h0g : g0≤g) (hg : g≤w.length) (left right : Nat)
    (h0l : g0≤left) (hlg : left≤g) (hr : right≤w.length) :
    (query (build A B C K D E w fallback g0 g h0g hg) left right).1=true ↔
      ∃a p j,At A B C K D E w left right a p j ∧ p<g := by
  rw [query_correct A B C K D E w fallback g0 g h0g hg left right h0l hlg hr]
  constructor
  · rintro (h|h|h|h)
    all_goals
      obtain ⟨a,p,j,hAt,hReg⟩:=h
      exact ⟨a,p,j,hAt,hReg.1⟩
  · rintro ⟨a,p,j,hAt,hpg⟩
    by_cases ha : a≤g0
    · by_cases hj : g≤j
      · exact Or.inl ⟨a,p,j,hAt,hpg,ha,hj⟩
      · exact Or.inr (Or.inr (Or.inl ⟨a,p,j,hAt,hpg,ha,by omega⟩))
    · by_cases hj : g≤j
      · exact Or.inr (Or.inl ⟨a,p,j,hAt,hpg,by omega,hj⟩)
      · exact Or.inr (Or.inr (Or.inr ⟨a,p,j,hAt,hpg,by omega,by omega⟩))

theorem build_work (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g0 g : Nat) (h0g : g0≤g) (hg : g≤w.length) :
    (build A B C K D E w fallback g0 g h0g hg).work≤
      NearIndex.buildBound A B C K D E w.length+Border.buildBound A B C K D E w.length+1 := by
  have hl:=NearIndex.build_work A B C K D E w fallback g0 g h0g hg
  have hb:=Border.build_work A B C K D E w fallback
  exact Nat.add_le_add_right (Nat.add_le_add hl hb) 1

theorem query_work (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (g0 g : Nat) (h0g : g0≤g) (hg : g≤w.length) (left right : Nat)
    (h0l : g0≤left) (hlg : left≤g) (hr : right≤w.length) :
    (query (build A B C K D E w fallback g0 g h0g hg) left right).2≤
      NearIndex.threeBudget A B C K D E w.length (g-left) (g-g0)+
        Border.queryBudget A B C K D E w.length (g-g0)+1 := by
  have hl:=NearIndex.queryThree_work A B C K D E w fallback g0 g h0g hg left right h0l hlg hr
  have hb:=Border.query_work A B C K D E w fallback left right g0 g hr
  exact Nat.add_le_add_right (Nat.add_le_add hl hb) 1

end REWB.BoundaryRange.NearIndex.Full
