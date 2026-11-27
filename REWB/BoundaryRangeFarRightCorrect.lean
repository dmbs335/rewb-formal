import REWB.BoundaryRangeFarRightIndex

/-! Exact original-coordinate semantics of the finite far-right cache.
The only input provenance premise is `Ready` for the materialized
all-start output arrays of the actual pending masks. -/
namespace REWB.BoundaryRange.FarRight
open REWB.BoundaryApplication REWB.OneUseRange REWB.Spec
variable {σ : Nat}

theorem reverse_suffix (E : DFA α) (w : Word α) (right y : Nat)
    (hr : right≤w.length) (hy : y≤w.length) (hry : w.length-right≤y) :
    (Automata.reverse E).accepts (slice w.reverse (w.length-right) y) ↔
      E.accepts (slice w (w.length-y) right) := by
  rw [Automata.reverse_accepts,reverse_slice w (w.length-right) y hry hy,List.reverse_reverse]
  have hh : w.length-(w.length-right)=right := by omega
  rw [hh]

theorem query_bits (K E : DFA (Fin σ)) (w : Word (Fin σ)) (grid : Nat) (bits : Input K)
    (left right : Nat) (hl : left≤grid) (hr : right≤w.length) :
    (query K (build K E w grid bits) left right).1=true ↔
      let q:=(Range.query K (Range.build K w) left grid).map.get K.initial
      ∃k : Fin K.stateCount,∃t,t≤right ∧ FarAggregate.bit ((bits.get q).get k) (w.length-t)=true ∧
        E.accepts (slice w t right) := by
  let q:=(Range.query K (Range.build K w) left grid).map.get K.initial
  unfold query
  change ((if left≤grid ∧ right≤w.length then _ else _) : Bool×Nat).1=true ↔ _
  rw [if_pos ⟨hl,hr⟩]
  dsimp only
  rw [build_get,FarAggregate.query_correct]
  simp only [List.size_toArray,List.length_reverse,List.toList_toArray]
  change (∃y,w.length-right≤y ∧ y≤w.length ∧
      FarAggregate.bit (unionRow K w.length (bits.get q)).bits y=true ∧
      (Automata.reverse E).accepts (slice w.reverse (w.length-right) y)) ↔
    ∃k : Fin K.stateCount,∃t,t≤right ∧ FarAggregate.bit ((bits.get q).get k) (w.length-t)=true ∧
      E.accepts (slice w t right)
  constructor
  · rintro ⟨y,hry,hy,hbits,hE⟩
    obtain ⟨k,hk⟩:=(unionRow_correct K w.length (bits.get q) y hy).mp hbits
    have hy' : w.length-(w.length-y)=y := by omega
    refine ⟨k,w.length-y,by omega,?_,(reverse_suffix E w right y hr hy hry).mp hE⟩
    simpa only [hy'] using hk
  · rintro ⟨k,t,htr,hk,hE⟩
    have ht : t≤w.length := by omega
    have ht' : w.length-(w.length-t)=t := by omega
    refine ⟨w.length-t,by omega,by omega,(unionRow_correct K w.length (bits.get q) (w.length-t) (by omega)).mpr ⟨k,hk⟩,?_⟩
    apply (reverse_suffix E w right (w.length-t) hr (by omega) (by omega)).mpr
    simpa only [ht'] using hE

theorem query_correct (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ)) (grid : Nat) (bits : Input K)
    (ready : Ready A B C K D w grid bits) (left right g0 : Nat)
    (hl : left≤grid) (hg : grid≤w.length) (hr : right≤w.length) :
    (query K (build K E w grid bits) left right).1=true ↔
      Case A B C K D E w left right g0 grid .farRight := by
  have hh:=farRight_step A B C K D E w left right g0 grid hl hg hr
  dsimp only at hh
  rw [query_bits K E w grid bits left right hl hr,hh]
  dsimp only
  constructor
  · rintro ⟨k,t,htr,hb,hE⟩
    exact ⟨k,t,htr,(ready_original A B C K D w grid bits ready _ k (w.length-t) (by omega)).mp hb,hE⟩
  · rintro ⟨k,t,htr,hb,hE⟩
    exact ⟨k,t,htr,(ready_original A B C K D w grid bits ready _ k (w.length-t) (by omega)).mpr hb,hE⟩

end REWB.BoundaryRange.FarRight
