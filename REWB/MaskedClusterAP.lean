import REWB.MaskedClusterOrbit
import REWB.MaskedPeriodicRun

/-! Execute the two-orbit cluster cell against an immutable arbitrary
    mask. The only list of AP queries has at most K*m*n entries, where
    K is computed from fixed state counts. This file's work counter is
    the existing AP-query counter; orbit/formula/window construction is
    explicitly separate and is not asserted free.
-/
namespace REWB.MaskedCluster
open REWB.MaskedPeriodic REWB.AffineProjection REWB.ExponentIntervals
variable {m n : Nat}

def pairWindows (before : OrbitData m) (after : OrbitData n) (lo hi K : Nat) :
    List (Nat×Window) := allWindows K hi (pairFormula before after lo hi)

theorem pairWindows_length (before : OrbitData m) (after : OrbitData n) (lo hi K : Nat) :
    (pairWindows before after lo hi K).length≤K*(m*n) := by
  rw [pairWindows,allWindows_length]
  exact Nat.mul_le_mul_left K (pairFormula_length before after lo hi)

def pairQuery (before : OrbitData m) (after : OrbitData n) (lo hi : Nat)
    (counts : Array Nat) (base q s K : Nat) : MaskedProgression.Answer :=
  queryWindows counts base q K s (pairWindows before after lo hi K)

theorem pairQuery_correct (before : OrbitData m) (after : OrbitData n) (lo hi : Nat)
    (mask : Array Bool) (base len q s S : Nat) (hq : 0<q) (hm : m≤S) (hn : n≤S) :
    (pairQuery before after lo hi (MaskedProgression.build mask base len (common S*q)).counts
      base q s (common S)).answer=true ↔
        ∃ k,PairAccepts before after lo hi k ∧ Marked mask base len q s k := by
  rw [pairQuery,queryWindows_correct _ _ _ _ _ _ _ hq (common_pos S)]
  simp only [pairWindows,allWindows_nat_correct _ _ _ _ (common_pos S)
    (pairFormula_compatible_common before after lo hi S hm hn),pairFormula_correct]
  constructor
  · rintro ⟨k,⟨_,hk⟩,hbase,hbound,hmark⟩
    exact ⟨k,hk,hbase,hbound,hmark⟩
  · rintro ⟨k,hk,hmark⟩
    exact ⟨k,⟨hk.2.1,hk⟩,hmark⟩

theorem pairQuery_work (before : OrbitData m) (after : OrbitData n) (lo hi : Nat)
    (counts : Array Nat) (base q s K : Nat) :
    (pairQuery before after lo hi counts base q s K).slots+
      (pairQuery before after lo hi counts base q s K).arithmetic≤47*(K*(m*n))+1 := by
  have hw:=queryWindows_work counts base q K s (pairWindows before after lo hi K)
  have hl:=Nat.mul_le_mul_left 47 (pairWindows_length before after lo hi K)
  exact Nat.le_trans hw (by omega)

end REWB.MaskedCluster
