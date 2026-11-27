import REWB.BoundaryRangeAutomata
import REWB.BoundaryApplicationCoverageComplete
import REWB.BoundaryApplicationStartCost
import REWB.BoundaryApplicationSeparatedCost

/-! The three constructed boundary indexes in common copy coordinates.
These are the actual builders and queries; only word boundaries and
finite automata are inputs to the equivalences below. -/
namespace REWB.BoundaryRange
open REWB.Spec (slice)
open REWB.BoundaryApplication
variable {σ : Nat}

theorem separated_copy (A B C D E : DFA (Fin σ)) (w : Word (Fin σ))
    (fallback : Fin σ) (g0 g right : Nat) (h0g : g0≤g) (hg : g≤w.length)
    (hr : right≤w.length) :
    (Separated.query E (Separated.build A B C D E w fallback g0 g hg) right).1=true ↔
      ∃a j,a≤g0 ∧ g≤j ∧ Copy A B E w a j right ∧
        C.accepts (slice w a g0) ∧ D.accepts (slice w g j) := by
  rw [Separated.query_iff_cuts A B C D E w fallback g0 g h0g hg right hr]
  constructor
  · rintro ⟨a,L,t,ha,hL,hgL,ht,he,hA,hB,hC,hD,hE⟩
    have htL : t-L+L=t := by omega
    refine ⟨a,t-L,ha,by omega,⟨L,hL,?_,?_,hA,hB,?_⟩,hC,hD⟩
    · omega
    · simpa only [htL] using he
    · simpa only [htL] using hE
  · rintro ⟨a,j,ha,hgj,⟨L,hL,hR,he,hA,hB,hE⟩,hC,hD⟩
    have hjL : j+L-L=j := by omega
    refine ⟨a,L,j+L,ha,hL,by omega,hR,?_,hA,hB,hC,?_,hE⟩
    · simpa only [hjL] using he
    · simpa only [hjL] using hD

theorem fixedEnd_copy (A B D E : DFA (Fin σ)) (w : Word (Fin σ))
    (fallback : Fin σ) (g : Nat) (hg : g≤w.length)
    (a : Fin (w.length+1)) (ha : a.val≤g) (right : Nat) (hr : right≤w.length) :
    (HeavyIndex.query A B D E w (HeavyIndex.build A B D E w fallback g hg) a right).value=true ↔
      ∃j,g≤j ∧ Copy A B E w a.val j right ∧ D.accepts (slice w g j) := by
  rw [Coverage.query_iff_cuts A B D E w fallback g hg a ha right hr]
  constructor
  · rintro ⟨t,L,ht,hL,hgL,he,hA,hB,hD,hE⟩
    have htL : t-L+L=t := by omega
    refine ⟨t-L,by omega,⟨L,hL,?_,?_,hA,hB,?_⟩,hD⟩
    · omega
    · simpa only [htL] using he
    · simpa only [htL] using hE
  · rintro ⟨j,hgj,⟨L,hL,hR,he,hA,hB,hE⟩,hD⟩
    have hjL : j+L-L=j := by omega
    refine ⟨j+L,L,hR,hL,by omega,?_,hA,hB,?_,hE⟩
    · simpa only [hjL] using he
    · simpa only [hjL] using hD

theorem fixedStart_copy (A B C E : DFA (Fin σ)) (w : Word (Fin σ))
    (fallback : Fin σ) (g : Nat) (hg : g≤w.length)
    (j : Fin (w.length+1)) (hj : g≤j.val) (right : Nat)
    (hjr : j.val≤right) (hr : right≤w.length) :
    (StartIndex.query B C E (StartIndex.build A B C E w fallback g hg) j right).value=true ↔
      ∃a,a≤g ∧ Copy A B E w a j.val right ∧ C.accepts (slice w a g) := by
  rw [StartIndex.query_iff_cuts A B C E w fallback g hg j hj right hjr hr]
  constructor
  · rintro ⟨i,L,hi,hL,hR,he,hA,hB,hC,hE⟩
    have hiL : i+L-L=i := by omega
    refine ⟨i+L,by omega,⟨L,by omega,hR,?_,?_,?_,hE⟩,hC⟩
    · simpa only [hiL] using he
    · simpa only [hiL] using hA
    · rw [hiL,he]
      exact hB
  · rintro ⟨a,ha,⟨L,hL,hR,he,hA,hB,hE⟩,hC⟩
    have haL : a-L+L=a := by omega
    refine ⟨a-L,L,by omega,by omega,hR,?_,hA,?_,?_,hE⟩
    · simpa only [haL] using he
    · rwa [←he]
    · simpa only [haL] using hC

theorem nearSeparated_step (A B C D E : DFA (Fin σ)) (w : Word (Fin σ))
    (fallback : Fin σ) (g0 p g right : Nat) (h0p : g0≤p) (hpg : p≤g)
    (hg : g≤w.length) (hr : right≤w.length) :
    let C':=Automata.tail C (Range.query C (Range.build C w) g0 p).map
    let D':=Automata.start D ((Range.query D (Range.build D w) p g).map.get D.initial)
    (Separated.query E (Separated.build A B C' D' E w fallback g0 g hg) right).1=true ↔
      ∃a j,a≤g0 ∧ g≤j ∧ Copy A B E w a j right ∧
        C.accepts (slice w a p) ∧ D.accepts (slice w p j) := by
  dsimp only
  rw [separated_copy _ _ _ _ _ w fallback g0 g right (by omega) hg hr]
  constructor
  · rintro ⟨a,j,ha,hgj,hcopy,hC,hD⟩
    exact ⟨a,j,ha,hgj,hcopy,
      (Automata.tail_slice C w a g0 p ha h0p (by omega)).mp hC,
      (Automata.start_slice D w p g j hpg hgj hg).mp hD⟩
  · rintro ⟨a,j,ha,hgj,hcopy,hC,hD⟩
    exact ⟨a,j,ha,hgj,hcopy,
      (Automata.tail_slice C w a g0 p ha h0p (by omega)).mpr hC,
      (Automata.start_slice D w p g j hpg hgj hg).mpr hD⟩

theorem nearEnd_step (A B D E : DFA (Fin σ)) (w : Word (Fin σ))
    (fallback : Fin σ) (p g right : Nat) (hpg : p≤g) (hg : g≤w.length)
    (hr : right≤w.length) (a : Fin (w.length+1)) (ha : a.val≤g) :
    let D':=Automata.start D ((Range.query D (Range.build D w) p g).map.get D.initial)
    (HeavyIndex.query A B D' E w (HeavyIndex.build A B D' E w fallback g hg) a right).value=true ↔
      ∃j,g≤j ∧ Copy A B E w a.val j right ∧ D.accepts (slice w p j) := by
  dsimp only
  rw [fixedEnd_copy _ _ _ _ w fallback g hg a ha right hr]
  constructor
  · rintro ⟨j,hgj,hcopy,hD⟩
    exact ⟨j,hgj,hcopy,(Automata.start_slice D w p g j hpg hgj hg).mp hD⟩
  · rintro ⟨j,hgj,hcopy,hD⟩
    exact ⟨j,hgj,hcopy,(Automata.start_slice D w p g j hpg hgj hg).mpr hD⟩

theorem nearStart_step (A B C E : DFA (Fin σ)) (w : Word (Fin σ))
    (fallback : Fin σ) (g0 p right : Nat) (h0p : g0≤p) (hp : p≤w.length)
    (hr : right≤w.length) (j : Fin (w.length+1)) (hpj : p≤j.val) (hjr : j.val≤right) :
    let C':=Automata.tail C (Range.query C (Range.build C w) g0 p).map
    (StartIndex.query B C' E (StartIndex.build A B C' E w fallback g0 (by omega)) j right).value=true ↔
      ∃a,a≤g0 ∧ Copy A B E w a j.val right ∧ C.accepts (slice w a p) := by
  dsimp only
  rw [fixedStart_copy _ _ _ _ w fallback g0 (by omega) j (by omega) right hjr hr]
  constructor
  · rintro ⟨a,ha,hcopy,hC⟩
    exact ⟨a,ha,hcopy,(Automata.tail_slice C w a g0 p ha h0p hp).mp hC⟩
  · rintro ⟨a,ha,hcopy,hC⟩
    exact ⟨a,ha,hcopy,(Automata.tail_slice C w a g0 p ha h0p hp).mpr hC⟩

end REWB.BoundaryRange
