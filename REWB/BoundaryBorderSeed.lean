import REWB.BoundaryBorderSelect

/-! The selector needs only one seed equality at its first source.  All
    other AP seeds follow from the maximal periodic prefix returned by
    the actual LCE.  No list of per-source equalities is supplied.
-/
namespace REWB.BoundaryBorder
open Periodic RunGeometry LCEIndex
variable {α : Type} {σ : Nat}

theorem progression_seed (f : Nat→α) (n first q extent j p : Nat)
    (hs : PeriodPrefix f n first q extent) (hp : first≤p)
    (hbound : p+q≤first+extent) (hmod : (p-first)%q=0)
    (hseed : segment f first q=segment f j q) :
    segment f p q=segment f j q := by
  apply (segment_eq_points f p j q).mpr
  intro i hi
  have he:=period_residue hs.periodic (p-first+i) (by omega)
  have hm : (p-first+i)%q=i := by
    simp only [Nat.add_mod,hmod,Nat.zero_add,Nat.mod_eq_of_lt hi]
  change f (first+(p-first+i))=f (first+((p-first+i)%q)) at he
  rw [show first+(p-first+i)=p+i by omega,hm] at he
  exact he.trans ((segment_eq_points f first j q).mp hseed i hi)

theorem select_from_seed (f : Nat→Fin σ) (n first q lo hi a j : Nat)
    (hq : 0<q) (hs : first+q≤n) (hj : j+q≤n) (ha : a≤n)
    (hspan : hi+q≤first+(extend (prepare f n) n first q).extent)
    (hseed : segment f first q=segment f j q) (p : Nat) :
    (select (prepare f n) n first q lo hi a j).choice.Holds p ↔
      Member first q lo hi p ∧ p≤a ∧ Agree f n p j (a-p) := by
  apply select_correct f n first q lo hi a j hq hs hj ha hspan ?_ p
  intro x hx
  exact progression_seed f n first q _ j x (extend_correct f n first q hs)
    hx.2.2.1 (by have hh:=hx.2.1; omega) hx.2.2.2 hseed

end REWB.BoundaryBorder
