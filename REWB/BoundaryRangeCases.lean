import REWB.OuterColumn

/-! Exact geometric dispatch of the boundary-aware one-use predicate.
The split is either at or beyond the next block boundary, or inside
the short block. The latter has four source-end/target-start cases.
This module states no cost bound for the individual matching queries.
-/
namespace REWB.BoundaryRange
open REWB.Spec (slice)
variable {α : Type}

/-- A repeated suffix of the first endpoint and prefix of the second,
including length zero. The source prefix and target suffix are explicit. -/
def Copy (A B E : DFA α) (w : Word α) (a j right : Nat) : Prop :=
  ∃L,L≤a ∧ j+L≤right ∧
    slice w (a-L) a=slice w j (j+L) ∧
    A.accepts (slice w 0 (a-L)) ∧ B.accepts (slice w (a-L) a) ∧
    E.accepts (slice w (j+L) right)

theorem copy_target_bound (A B E : DFA α) (w : Word α) (a j right : Nat)
    (h : Copy A B E w a j right) : j≤right := by
  obtain ⟨L,_,hL,_⟩:=h
  omega

/-- The three exposed endpoints. The hidden endpoints are recovered
from the single common length in `Copy`. -/
def At (A B C K D E : DFA α) (w : Word α) (left right a p j : Nat) : Prop :=
  a≤p ∧ p≤j ∧ left≤p ∧
    C.accepts (slice w a p) ∧ K.accepts (slice w left p) ∧
    D.accepts (slice w p j) ∧ Copy A B E w a j right

theorem at_bounds (A B C K D E : DFA α) (w : Word α) (left right a p j : Nat)
    (h : At A B C K D E w left right a p j) :
    a≤p ∧ p≤j ∧ j≤right ∧ left≤p :=
  ⟨h.1,h.2.1,copy_target_bound A B E w a j right h.2.2.2.2.2.2,h.2.2.1⟩

theorem boundary_iff (A B C K D E : DFA α) (w : Word α) (left right : Nat) :
    Spec.boundaryRange A B C K D E w left right ↔
      left≤right ∧ right≤w.length ∧ ∃a p j,At A B C K D E w left right a p j := by
  constructor
  · rintro ⟨hl,hr,i,a,p,j,t,hia,hap,hpj,hjt,htr,hlp,he,hA,hB,hC,hK,hD,hE⟩
    have heLen:=congrArg List.length he
    rw [OuterColumn.slice_length w i a hia (by omega),
      OuterColumn.slice_length w j t hjt (by omega)] at heLen
    have hi : a-(a-i)=i := by omega
    have ht : j+(a-i)=t := by omega
    refine ⟨hl,hr,a,p,j,hap,hpj,hlp,hC,hK,hD,a-i,by omega,?_,?_,?_,?_,?_⟩
    · omega
    · simpa only [hi,ht] using he
    · simpa only [hi] using hA
    · simpa only [hi] using hB
    · simpa only [ht] using hE
  · rintro ⟨hl,hr,a,p,j,hap,hpj,hlp,hC,hK,hD,L,hLa,hLr,he,hA,hB,hE⟩
    exact ⟨hl,hr,a-L,a,p,j,j+L,by omega,hap,hpj,by omega,hLr,hlp,he,hA,hB,hC,hK,hD,hE⟩

inductive Region where
  | farLeft
  | farRight
  | nearSeparated
  | nearEnd
  | nearStart
  | nearBorder
  deriving DecidableEq,Repr

def regionOf (g0 g a p j : Nat) : Region :=
  if g≤p then
    if a≤g then .farLeft else .farRight
  else if a≤g0 then
    if g≤j then .nearSeparated else .nearStart
  else
    if g≤j then .nearEnd else .nearBorder

def InRegion (g0 g a p j : Nat) : Region→Prop
  | .farLeft => g≤p ∧ a≤g
  | .farRight => g≤p ∧ g<a
  | .nearSeparated => p<g ∧ a≤g0 ∧ g≤j
  | .nearEnd => p<g ∧ g0<a ∧ g≤j
  | .nearStart => p<g ∧ a≤g0 ∧ j<g
  | .nearBorder => p<g ∧ g0<a ∧ j<g

theorem regionOf_correct (g0 g a p j : Nat) :
    InRegion g0 g a p j (regionOf g0 g a p j) := by
  by_cases hp : g≤p
  · by_cases ha : a≤g
    · simp only [regionOf,if_pos hp,if_pos ha,InRegion]
      exact ⟨hp,ha⟩
    · simp only [regionOf,if_pos hp,if_neg ha,InRegion]
      exact ⟨hp,by omega⟩
  · by_cases ha : a≤g0
    · by_cases hj : g≤j
      · simp only [regionOf,if_neg hp,if_pos ha,if_pos hj,InRegion]
        exact ⟨by omega,ha,hj⟩
      · simp only [regionOf,if_neg hp,if_pos ha,if_neg hj,InRegion]
        exact ⟨by omega,ha,by omega⟩
    · by_cases hj : g≤j
      · simp only [regionOf,if_neg hp,if_neg ha,if_pos hj,InRegion]
        exact ⟨by omega,by omega,hj⟩
      · simp only [regionOf,if_neg hp,if_neg ha,if_neg hj,InRegion]
        exact ⟨by omega,by omega,by omega⟩

theorem region_unique (g0 g a p j : Nat) (c : Region)
    (hc : InRegion g0 g a p j c) : regionOf g0 g a p j=c := by
  cases c <;> simp only [InRegion] at hc
  · simp [regionOf,hc.1,hc.2]
  · simp [regionOf,hc.1,Nat.not_le.mpr hc.2]
  · simp [regionOf,Nat.not_le.mpr hc.1,hc.2.1,hc.2.2]
  · simp [regionOf,Nat.not_le.mpr hc.1,Nat.not_le.mpr hc.2.1,hc.2.2]
  · simp [regionOf,Nat.not_le.mpr hc.1,hc.2.1,Nat.not_le.mpr hc.2.2]
  · simp [regionOf,Nat.not_le.mpr hc.1,Nat.not_le.mpr hc.2.1,Nat.not_le.mpr hc.2.2]

def Case (A B C K D E : DFA α) (w : Word α) (left right g0 g : Nat) (c : Region) : Prop :=
  ∃a p j,At A B C K D E w left right a p j ∧ InRegion g0 g a p j c

theorem partition (A B C K D E : DFA α) (w : Word α) (left right g0 g : Nat) :
    Spec.boundaryRange A B C K D E w left right ↔
      left≤right ∧ right≤w.length ∧ ∃c,Case A B C K D E w left right g0 g c := by
  rw [boundary_iff]
  constructor
  · rintro ⟨hl,hr,a,p,j,h⟩
    exact ⟨hl,hr,regionOf g0 g a p j,a,p,j,h,regionOf_correct g0 g a p j⟩
  · rintro ⟨hl,hr,c,a,p,j,h,_⟩
    exact ⟨hl,hr,a,p,j,h⟩

theorem six_cases (A B C K D E : DFA α) (w : Word α) (left right g0 g : Nat) :
    Spec.boundaryRange A B C K D E w left right ↔
      left≤right ∧ right≤w.length ∧
        (Case A B C K D E w left right g0 g .farLeft ∨
         Case A B C K D E w left right g0 g .farRight ∨
         Case A B C K D E w left right g0 g .nearSeparated ∨
         Case A B C K D E w left right g0 g .nearEnd ∨
         Case A B C K D E w left right g0 g .nearStart ∨
         Case A B C K D E w left right g0 g .nearBorder) := by
  rw [partition]
  constructor
  · rintro ⟨hl,hr,c,hc⟩
    refine ⟨hl,hr,?_⟩
    cases c
    · exact Or.inl hc
    · exact Or.inr (Or.inl hc)
    · exact Or.inr (Or.inr (Or.inl hc))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hc)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hc))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hc))))
  · rintro ⟨hl,hr,hc⟩
    refine ⟨hl,hr,?_⟩
    rcases hc with h|h|h|h|h|h
    · exact ⟨.farLeft,h⟩
    · exact ⟨.farRight,h⟩
    · exact ⟨.nearSeparated,h⟩
    · exact ⟨.nearEnd,h⟩
    · exact ⟨.nearStart,h⟩
    · exact ⟨.nearBorder,h⟩

/-- Every endpoint enumerated in the near cases stays inside a single
block. The first-copy start remains unrestricted and may precede it. -/
theorem near_bounds (A B C K D E : DFA α) (w : Word α)
    (left right g0 g a p j : Nat) (hg0 : g0≤left)
    (h : At A B C K D E w left right a p j) (hp : p<g) :
    g0≤p ∧ p<g ∧
      (g0<a → g0<a ∧ a<g) ∧ (j<g → left≤j ∧ j<g) := by
  obtain ⟨ha,hpj,_,hl⟩:=at_bounds A B C K D E w left right a p j h
  exact ⟨by omega,hp,fun hh=>⟨hh,by omega⟩,fun hh=>⟨by omega,hh⟩⟩

end REWB.BoundaryRange
