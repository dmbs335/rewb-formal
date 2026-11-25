import REWB.BoundaryRangeNearIndex

/-! Exact slice semantics for queries against the eager variant table.
The equalities below eliminate only cached lookups, never insert a new
builder into the executable query. -/
namespace REWB.BoundaryRange.NearIndex
open REWB.BoundaryApplication
open REWB.BoundaryIndex
open REWB.Spec (slice)
variable {σ : Nat}

theorem cKey_variant (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ))
    (fallback : Fin σ) (g0 g : Nat) (h0g : g0≤g) (hg : g≤w.length) (p : Nat) :
    cVariant C (cKey (build A B C K D E w fallback g0 g h0g hg) p).1=
      Automata.tail C (Range.query C (Range.build C w) g0 p).map := by
  change Automata.finish C (Colors.decode C (TableColor.choose C (TableColor.build C)
    (fun q=>C.final ((Range.query C (Range.build C w) g0 p).map.get q))).1)=_
  rw [TableColor.choose_correct]
  rfl

theorem dKey_variant (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ))
    (fallback : Fin σ) (g0 g : Nat) (h0g : g0≤g) (hg : g≤w.length) (p : Nat) :
    dVariant D (dKey (build A B C K D E w fallback g0 g h0g hg) p).1=
      Automata.start D ((Range.query D (Range.build D w) p g).map.get D.initial) := rfl

theorem separated_correct (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ))
    (fallback : Fin σ) (g0 g : Nat) (h0g : g0≤g) (hg : g≤w.length)
    (p right : Nat) (h0p : g0≤p) (hpg : p≤g) (hr : right≤w.length) :
    (separated (build A B C K D E w fallback g0 g h0g hg) p right).1=true ↔
      ∃a j,a≤g0 ∧ g≤j ∧ Copy A B E w a j right ∧
        C.accepts (slice w a p) ∧ D.accepts (slice w p j) := by
  simp only [separated,build_separated,cKey_variant,dKey_variant]
  exact nearSeparated_step A B C D E w fallback g0 p g right h0p hpg hg hr

theorem fixedEnd_correct (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ))
    (fallback : Fin σ) (g0 g : Nat) (h0g : g0≤g) (hg : g≤w.length)
    (p right : Nat) (hpg : p≤g) (hr : right≤w.length)
    (a : Fin (w.length+1)) (ha : a.val≤g) :
    (fixedEnd (build A B C K D E w fallback g0 g h0g hg) p a right).1=true ↔
      ∃j,g≤j ∧ Copy A B E w a.val j right ∧ D.accepts (slice w p j) := by
  simp only [fixedEnd,build_end,dKey_variant]
  exact nearEnd_step A B D E w fallback p g right hpg hg hr a ha

theorem fixedStart_correct (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ))
    (fallback : Fin σ) (g0 g : Nat) (h0g : g0≤g) (hg : g≤w.length)
    (p right : Nat) (h0p : g0≤p) (hp : p≤w.length) (hr : right≤w.length)
    (j : Fin (w.length+1)) (hpj : p≤j.val) (hjr : j.val≤right) :
    (fixedStart (build A B C K D E w fallback g0 g h0g hg) p j right).1=true ↔
      ∃a,a≤g0 ∧ Copy A B E w a j.val right ∧ C.accepts (slice w a p) := by
  simp only [fixedStart,build_start]
  rw [cKey_variant]
  exact nearStart_step A B C E w fallback g0 p right h0p hp hr j hpj hjr

end REWB.BoundaryRange.NearIndex
