import REWB.BoundaryRangePrimitives

/-! Finite-state handling of the split p. The same-block branch chooses
its source end and target start, then uses one regular gap query; it
does not enumerate a third block endpoint. The far-left branch is an
actual separated query with a fixed intermediate C state. -/
namespace REWB.BoundaryRange
open REWB.Spec (slice)
open REWB.BoundaryApplication
variable {α : Type}

theorem split_gap (C K D : DFA α) (w : Word α) (left a j : Nat)
    (haj : a≤j) (hlj : left≤j) (hj : j≤w.length) :
    let b:=max a left
    let c:=(Range.query C (Range.build C w) a b).map.get C.initial
    let k:=(Range.query K (Range.build K w) left b).map.get K.initial
    (Automata.gap C K D c k).accepts (slice w b j) ↔
      ∃p,a≤p ∧ left≤p ∧ p≤j ∧ C.accepts (slice w a p) ∧
        K.accepts (slice w left p) ∧ D.accepts (slice w p j) := by
  dsimp only
  have hb : max a left≤j := Nat.max_le.mpr ⟨haj,hlj⟩
  rw [Automata.gap_slice C K D w _ _ (max a left) j hb hj]
  rw [Range.query_correct C w a (max a left) (Nat.le_max_left _ _) (by omega),
    Range.query_correct K w left (max a left) (Nat.le_max_right _ _) (by omega)]
  constructor
  · rintro ⟨p,hbp,hpj,hC,hK,hD⟩
    refine ⟨p,by omega,by omega,hpj,?_,?_,hD⟩
    · change C.final (C.run C.initial (slice w a p))=true
      rw [OuterColumn.slice_split w a (max a left) p (Nat.le_max_left _ _) hbp,DFA.run_append]
      exact hC
    · change K.final (K.run K.initial (slice w left p))=true
      rw [OuterColumn.slice_split w left (max a left) p (Nat.le_max_right _ _) hbp,DFA.run_append]
      exact hK
  · rintro ⟨p,hap,hlp,hpj,hC,hK,hD⟩
    have hbp : max a left≤p := Nat.max_le.mpr ⟨hap,hlp⟩
    refine ⟨p,hbp,hpj,?_,?_,hD⟩
    · change C.final (C.run C.initial (slice w a p))=true at hC
      rw [OuterColumn.slice_split w a (max a left) p (Nat.le_max_left _ _) hbp,DFA.run_append] at hC
      exact hC
    · change K.final (K.run K.initial (slice w left p))=true at hK
      rw [OuterColumn.slice_split w left (max a left) p (Nat.le_max_right _ _) hbp,DFA.run_append] at hK
      exact hK

theorem nearBorder_step (A B C K D E : DFA α) (w : Word α) (left right g0 g : Nat)
    (hr : right≤w.length) :
    Case A B C K D E w left right g0 g .nearBorder ↔
      ∃a j,g0<a ∧ a≤j ∧ left≤j ∧ j<g ∧ j≤right ∧ Copy A B E w a j right ∧
        (Automata.gap C K D
          ((Range.query C (Range.build C w) a (max a left)).map.get C.initial)
          ((Range.query K (Range.build K w) left (max a left)).map.get K.initial)).accepts
            (slice w (max a left) j) := by
  constructor
  · rintro ⟨a,p,j,hAt,hRegion⟩
    obtain ⟨hap,hpj,hlp,hC,hK,hD,hcopy⟩:=hAt
    obtain ⟨_,ha,hj⟩:=hRegion
    have hjr:=copy_target_bound A B E w a j right hcopy
    refine ⟨a,j,ha,by omega,by omega,hj,hjr,hcopy,?_⟩
    exact (split_gap C K D w left a j (by omega) (by omega) (by omega)).mpr
      ⟨p,hap,hlp,hpj,hC,hK,hD⟩
  · rintro ⟨a,j,ha,haj,hlj,hjg,hjr,hcopy,hGap⟩
    obtain ⟨p,hap,hlp,hpj,hC,hK,hD⟩:=
      (split_gap C K D w left a j haj hlj (by omega)).mp hGap
    exact ⟨a,p,j,⟨hap,hpj,hlp,hC,hK,hD,hcopy⟩,by change p<g ∧ g0<a ∧ j<g; omega⟩

theorem farLeft_step {σ : Nat} (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ))
    (fallback : Fin σ) (left right g0 g : Nat) (hlg : left≤g) (hg : g≤w.length)
    (hr : right≤w.length) :
    Case A B C K D E w left right g0 g .farLeft ↔
      ∃c : Fin C.stateCount,
        (Separated.query E (Separated.build A B (Automata.stop C c)
          (Automata.gap C K D c ((Range.query K (Range.build K w) left g).map.get K.initial))
          E w fallback g g hg) right).1=true := by
  constructor
  · rintro ⟨a,p,j,hAt,hRegion⟩
    obtain ⟨hap,hpj,hlp,hC,hK,hD,hcopy⟩:=hAt
    obtain ⟨hgp,hag⟩:=hRegion
    let c:=C.run C.initial (slice w a g)
    have hjr:=copy_target_bound A B E w a j right hcopy
    refine ⟨c,(separated_copy _ _ _ _ _ w fallback g g right (Nat.le_refl _) hg hr).mpr ?_⟩
    refine ⟨a,j,hag,by omega,hcopy,(Automata.stop_accepts C c _).mpr rfl,?_⟩
    rw [Automata.gap_slice C K D w c _ g j (by omega) (by omega)]
    refine ⟨p,hgp,hpj,?_,?_,hD⟩
    · change C.final (C.run C.initial (slice w a p))=true at hC
      rw [OuterColumn.slice_split w a g p hag hgp,DFA.run_append] at hC
      exact hC
    · rw [Range.query_correct K w left g hlg hg]
      change K.final (K.run K.initial (slice w left p))=true at hK
      rw [OuterColumn.slice_split w left g p hlg hgp,DFA.run_append] at hK
      exact hK
  · rintro ⟨c,hQuery⟩
    obtain ⟨a,j,hag,hgj,hcopy,hC0,hGap⟩:=
      (separated_copy _ _ _ _ _ w fallback g g right (Nat.le_refl _) hg hr).mp hQuery
    have hjr:=copy_target_bound A B E w a j right hcopy
    have hC0:=(Automata.stop_accepts C c _).mp hC0
    obtain ⟨p,hgp,hpj,hC,hK,hD⟩:=
      (Automata.gap_slice C K D w c _ g j hgj (by omega)).mp hGap
    refine ⟨a,p,j,⟨by omega,hpj,by omega,?_,?_,hD,hcopy⟩,hgp,hag⟩
    · change C.final (C.run C.initial (slice w a p))=true
      rw [OuterColumn.slice_split w a g p hag hgp,DFA.run_append,hC0]
      exact hC
    · rw [Range.query_correct K w left g hlg hg] at hK
      change K.final (K.run K.initial (slice w left p))=true
      rw [OuterColumn.slice_split w left g p hlg hgp,DFA.run_append]
      exact hK

end REWB.BoundaryRange
