import REWB.BoundaryRangeGaps
import REWB.BoundaryRangeReverse

/-! The remaining far-split case reduces to finitely many reversed
masked all-start instances. Their target mask selects the first-copy
end and the K state reached there. A static E aggregate can then answer
every right endpoint without rerunning the masked solver. -/
namespace REWB.BoundaryRange
open REWB.Spec (slice)
open REWB.BoundaryApplication
variable {α : Type}

def farMask (K : DFA α) (w : Word α) (g : Nat) (q k : Fin K.stateCount) (a : Nat) : Bool :=
  decide (g<a) && decide (K.run q (slice w g a)=k)

theorem farMask_true (K : DFA α) (w : Word α) (g : Nat) (q k : Fin K.stateCount) (a : Nat) :
    farMask K w g q k a=true ↔ g<a ∧ K.run q (slice w g a)=k := by
  simp only [farMask,Bool.and_eq_true,decide_eq_true_eq]

theorem through_state (K : DFA α) (w : Word α) (left g a p : Nat)
    (hlg : left≤g) (hga : g≤a) (hap : a≤p) (hg : g≤w.length)
    (k : Fin K.stateCount)
    (hk : K.run ((Range.query K (Range.build K w) left g).map.get K.initial) (slice w g a)=k) :
    K.run K.initial (slice w left p)=K.run k (slice w a p) := by
  rw [Range.query_correct K w left g hlg hg] at hk
  rw [OuterColumn.slice_split w left a p (by omega) hap,DFA.run_append,
    OuterColumn.slice_split w left g a hlg hga,DFA.run_append,hk]

theorem farRight_step (A B C K D E : DFA α) (w : Word α)
    (left right g0 g : Nat) (hlg : left≤g) (hg : g≤w.length) (hr : right≤w.length) :
    let q:=(Range.query K (Range.build K w) left g).map.get K.initial
    Case A B C K D E w left right g0 g .farRight ↔
      ∃k : Fin K.stateCount,∃t,t≤right ∧
        Spec.maskedStart (Automata.reverse B)
          (Automata.reverse (Automata.gap C K D C.initial k)) (Automata.reverse A)
          w.reverse (fun y=>farMask K w g q k (w.length-y)) (w.length-t) ∧
        E.accepts (slice w t right) := by
  dsimp only
  constructor
  · rintro ⟨a,p,j,hAt,hRegion⟩
    obtain ⟨hap,hpj,hlp,hC,hK,hD,L,hLa,hLr,he,hA,hB,hE⟩:=hAt
    obtain ⟨hgp,hga⟩:=hRegion
    let k:=K.run ((Range.query K (Range.build K w) left g).map.get K.initial) (slice w g a)
    have hGap : (Automata.gap C K D C.initial k).accepts (slice w a j) := by
      rw [Automata.gap_slice C K D w C.initial k a j (by omega) (by omega)]
      refine ⟨p,hap,hpj,hC,?_,hD⟩
      change K.final (K.run K.initial (slice w left p))=true at hK
      rw [through_state K w left g a p hlg (by omega) hap hg k rfl] at hK
      exact hK
    refine ⟨k,j+L,hLr,?_,hE⟩
    apply (masked_reverse A B (Automata.gap C K D C.initial k) w
      (farMask K w g ((Range.query K (Range.build K w) left g).map.get K.initial) k)
      (j+L) (by omega)).mpr
    exact ⟨a-L,a,j,by omega,by omega,by omega,
      (farMask_true _ _ _ _ _ _).mpr ⟨hga,rfl⟩,he,hA,hB,hGap⟩
  · rintro ⟨k,t,htr,hMasked,hE⟩
    have hBefore:=(masked_reverse A B (Automata.gap C K D C.initial k) w
      (farMask K w g ((Range.query K (Range.build K w) left g).map.get K.initial) k)
      t (by omega)).mp hMasked
    obtain ⟨a,j,hm,haj,hcopy,hGap⟩:=
      (beforeEnd_copy A B (Automata.gap C K D C.initial k) E w _ right hr).mp
        ⟨t,htr,hBefore,hE⟩
    obtain ⟨hga,hk⟩:=(farMask_true _ _ _ _ _ _).mp hm
    have hjr:=copy_target_bound A B E w a j right hcopy
    obtain ⟨p,hap,hpj,hC,hK,hD⟩:=
      (Automata.gap_slice C K D w C.initial k a j haj (by omega)).mp hGap
    refine ⟨a,p,j,⟨hap,hpj,by omega,hC,?_,hD,hcopy⟩,by change g≤p ∧ g<a; omega⟩
    change K.final (K.run K.initial (slice w left p))=true
    rw [through_state K w left g a p hlg (by omega) hap hg k hk]
    exact hK

end REWB.BoundaryRange
