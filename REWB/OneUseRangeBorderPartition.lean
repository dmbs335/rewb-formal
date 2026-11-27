import REWB.OneUseRangeBorderCost

/-! The two far regions may overlap. Every remaining witness has its
first start and second end in the two short endpoint blocks and is
decided by the actual midpoint query. The far predicates here are
explicit slice predicates, pending their separate all-start caches. -/
namespace REWB.OneUseRange.Border
variable {σ : Nat}

def FarTarget (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (left right grid : Nat) : Prop :=
  ∃i t,At A B C E w left right i t ∧ t≤grid

def FarSource (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (left right grid : Nat) : Prop :=
  ∃i t,At A B C E w left right i t ∧ grid≤i

theorem partition (A B C E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (left right leftGrid rightGrid : Nat) :
    Spec.oneUseRange A B C E w left right ↔
      left≤right ∧ right≤w.length ∧
        (FarTarget A B C E w left right rightGrid ∨ FarSource A B C E w left right leftGrid ∨
          (query (build A B C E w fallback) left right leftGrid rightGrid).1=true) := by
  rw [oneUse_iff]
  constructor
  · rintro ⟨hl,hr,i,t,h⟩
    refine ⟨hl,hr,?_⟩
    by_cases ht : t≤rightGrid
    · exact Or.inl ⟨i,t,h,ht⟩
    · by_cases hi : leftGrid≤i
      · exact Or.inr (Or.inl ⟨i,t,h,hi⟩)
      · exact Or.inr (Or.inr ((query_correct A B C E w fallback left right leftGrid rightGrid hr).mpr
          ⟨i,t,h,by omega,by omega⟩))
  · rintro ⟨hl,hr,h⟩
    refine ⟨hl,hr,?_⟩
    rcases h with ⟨i,t,h,_⟩|⟨i,t,h,_⟩|h
    · exact ⟨i,t,h⟩
    · exact ⟨i,t,h⟩
    · obtain ⟨i,t,h,_,_⟩:=(query_correct A B C E w fallback left right leftGrid rightGrid hr).mp h
      exact ⟨i,t,h⟩

end REWB.OneUseRange.Border
