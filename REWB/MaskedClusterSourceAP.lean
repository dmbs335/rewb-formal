import REWB.MaskedClusterMatrix

/-! Source-only reporting windows. Restrict the free physical position
    s+k*q with two inequalities before clipping affine windows. No mask
    prefix array is rebuilt, and the common residue modulus is unchanged.
    The target-stage compiler will continue using its full physical
    cursor window independently of this source restriction.
-/
namespace REWB.MaskedCluster
open REWB.MaskedPeriodic REWB.AffineProjection REWB.ExponentIntervals REWB.PhaseSolver
variable {m n : Nat}

structure SourceWindow where
  enabled : Bool
  lo : Nat
  hi : Nat
  deriving Repr

def SourceWindow.allows (window : SourceWindow) (p : Nat) : Bool :=
  window.enabled && decide (window.lo≤p ∧ p<window.hi)

theorem SourceWindow.allows_iff (window : SourceWindow) (p : Nat) :
    window.allows p=true ↔ window.enabled=true ∧ window.lo≤p ∧ p<window.hi := by
  simp only [SourceWindow.allows,Bool.and_eq_true,decide_eq_true_eq]

def positionExpr (s q : Nat) : Aff := .add (.lit s) (.scale (q:Int) (.var 0))

theorem positionExpr_eval (s q k : Nat) :
    (positionExpr s q).eval [(k:Int)]=(s+k*q:Int) := by
  simp only [positionExpr,Aff.eval,List.getElem?_cons_zero,Option.getD_some,
    Int.ofNat_add,Int.ofNat_mul,Int.mul_comm (q:Int) (k:Int)]

def sourceBounds (window : SourceWindow) (s q : Nat) : Formula :=
  both (le (.lit window.lo) (positionExpr s q))
    (le (positionExpr s q) (.lit ((window.hi:Int)-1)))

theorem sourceBounds_correct (window : SourceWindow) (s q k : Nat) :
    Satisfies (sourceBounds window s q) [(k:Int)] ↔ window.lo≤s+k*q ∧ s+k*q<window.hi := by
  simp only [sourceBounds,both_correct,le_correct,positionExpr_eval,Aff.eval]
  omega

def sourceFormula (before : OrbitData m) (after : OrbitData n) (lo hi s q : Nat)
    (window : SourceWindow) : Formula :=
  both (pairFormula before after lo hi) (sourceBounds window s q)

theorem sourceFormula_correct (before : OrbitData m) (after : OrbitData n) (lo hi s q k : Nat)
    (window : SourceWindow) :
    Satisfies (sourceFormula before after lo hi s q window) [(k:Int)] ↔
      PairAccepts before after lo hi k ∧ window.lo≤s+k*q ∧ s+k*q<window.hi := by
  simp only [sourceFormula,both_correct,pairFormula_correct,sourceBounds_correct]

theorem sourceFormula_compatible (before : OrbitData m) (after : OrbitData n) (lo hi s q S : Nat)
    (window : SourceWindow) (hm : m≤S) (hn : n≤S) :
    Compatible (common S) (sourceFormula before after lo hi s q window) :=
  compatible_both _ _ _ (pairFormula_compatible_common before after lo hi S hm hn)
    (compatible_both _ _ _ (compatible_le _ _ _) (compatible_le _ _ _))

theorem sourceFormula_length (before : OrbitData m) (after : OrbitData n) (lo hi s q : Nat)
    (window : SourceWindow) :
    (sourceFormula before after lo hi s q window).length≤m*n := by
  simp only [sourceFormula,sourceBounds,both_length,le,unit,List.length_singleton,
    Nat.one_mul,Nat.mul_one]
  exact pairFormula_length before after lo hi

def sourcePairQuery (before : OrbitData m) (after : OrbitData n) (lo hi : Nat)
    (counts : Array Nat) (base q s K : Nat) (window : SourceWindow) : MaskedProgression.Answer :=
  if window.enabled then
    queryWindows counts base q K s (allWindows K hi (sourceFormula before after lo hi s q window))
  else ⟨false,0,1⟩

theorem sourcePairQuery_correct (before : OrbitData m) (after : OrbitData n) (lo hi : Nat)
    (mask : Array Bool) (base len q s S : Nat) (window : SourceWindow)
    (hq : 0<q) (hm : m≤S) (hn : n≤S) :
    (sourcePairQuery before after lo hi (MaskedProgression.build mask base len (common S*q)).counts
      base q s (common S) window).answer=true ↔
        ∃ k,PairAccepts before after lo hi k ∧ Marked mask base len q s k ∧ window.allows (s+k*q)=true := by
  by_cases he : window.enabled=true
  · simp only [sourcePairQuery,he,if_true]
    rw [queryWindows_correct _ _ _ _ _ _ _ hq (common_pos S)]
    simp only [allWindows_nat_correct _ _ _ _ (common_pos S)
      (sourceFormula_compatible before after lo hi s q S window hm hn),sourceFormula_correct,
      SourceWindow.allows_iff,he,true_and]
    constructor
    · rintro ⟨k,⟨_,hk,hl,hh⟩,hb,hn,hm⟩
      exact ⟨k,hk,⟨hb,hn,hm⟩,hl,hh⟩
    · rintro ⟨k,hk,⟨hb,hn,hm⟩,hl,hh⟩
      exact ⟨k,⟨hk.2.1,hk,hl,hh⟩,hb,hn,hm⟩
  · simp only [sourcePairQuery,he,if_false,Bool.false_eq_true,false_iff]
    rintro ⟨k,_,_,hw⟩
    exact he ((SourceWindow.allows_iff window _).mp hw).1

theorem sourcePairQuery_work (before : OrbitData m) (after : OrbitData n) (lo hi : Nat)
    (counts : Array Nat) (base q s K : Nat) (window : SourceWindow) :
    (sourcePairQuery before after lo hi counts base q s K window).slots+
      (sourcePairQuery before after lo hi counts base q s K window).arithmetic≤47*(K*(m*n))+1 := by
  unfold sourcePairQuery
  split
  · have hw:=queryWindows_work counts base q K s (allWindows K hi (sourceFormula before after lo hi s q window))
    have hl:=Nat.mul_le_mul_left 47 (Nat.mul_le_mul_left K (sourceFormula_length before after lo hi s q window))
    rw [allWindows_length] at hw
    exact Nat.le_trans hw (by omega)
  · simp only
    omega

end REWB.MaskedCluster
