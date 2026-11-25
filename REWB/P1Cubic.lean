import REWB.SmallPeriodP1
import REWB.P1ShortBranch

/-! Complete small-period P1 dispatch for cubic target runs whose outer
    copy is at least one period long. The inner source may have any
    length and need not itself be contained in a run. -/
namespace REWB.P1Cubic
open REWB.Periodic REWB.RunGeometry
variable {α : Type} {σ : Nat}

structure Witness (P : SevenDFA α) (f : Nat→α) (n : Nat) (T : Bounds) where
  outerStart : Nat
  target : P1Target.Layout Nat
  earlierStart : Nat
  target_ok : P1Target.Witness P (shift f T.lo) (T.hi-T.lo) outerStart
    ((segment f 0 n).drop T.hi) target
  long_outer : T.period≤target.e-outerStart
  earlier : earlierStart+(target.t-target.j)≤T.lo+outerStart
  equal_inner : segment f earlierStart (target.t-target.j)=
    P2Periodic.factor (shift f T.lo) target.j target.t
  prefix_ok : P.A.accepts (segment f 0 earlierStart)
  gap_ok : P.C.accepts (Spec.slice (segment f 0 n)
    (earlierStart+(target.t-target.j)) (T.lo+outerStart))

def solve (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat) : Bool :=
  (P1Events.solve P f n Q).answer || (P1ShortBranch.solve P f n Q).answer

theorem solve_sound (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat)
    (h : solve P f n Q=true) : MatchesWithin P.nested1 (segment f 0 n) 2 := by
  rw [solve,Bool.or_eq_true] at h
  rcases h with h|h
  · exact SmallPeriodP1.solve_sound P f n Q h
  · exact P1ShortBranch.solve_sound P f n Q h

theorem solve_complete (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n Q : Nat)
    (T : Bounds) (hT : T.Valid f n) (hq : T.period≤Q)
    (hc : 3*T.period≤T.hi-T.lo) (w : Witness P f n T) : solve P f n Q=true := by
  rw [solve,Bool.or_eq_true]
  by_cases hshort : w.target.t-w.target.j<3*T.period
  · exact Or.inr (P1ShortBranch.solve_complete P f n Q T hT hq hc
      ⟨w.outerStart,w.target,w.earlierStart,w.target_ok,hshort,w.long_outer,
        w.earlier,w.equal_inner,w.prefix_ok,w.gap_ok⟩)
  · exact Or.inl (SmallPeriodP1.solve_complete_long P f n Q T hT hq
      ⟨w.outerStart,w.target,w.earlierStart,w.target_ok,by omega,
        w.earlier,w.equal_inner,w.prefix_ok,w.gap_ok⟩)

end REWB.P1Cubic
