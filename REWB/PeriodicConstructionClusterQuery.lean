import REWB.PeriodicConstructionCluster

/-! Value-equivalent immutable and mutable AP queries including their
actual formula/window construction. A fixed pattern coefficient bounds
the extra work per call, so counted cell traversals can absorb it
without a new dependence on physical periods or text positions. -/
namespace REWB.PeriodicConstruction.Cluster
open REWB.PeriodicConstruction
variable {m n : Nat}

def pairQuery (before : Masked.Input m) (after : Masked.Input n) (lo hi : Nat)
    (counts : Array Nat) (base q s K : Nat) : Result MaskedProgression.Answer :=
  let ws:=pairWindows before after lo hi K
  let out:=MaskedPeriodic.queryWindows counts base q K s ws.1
  (out,ws.2+out.slots+out.arithmetic+1)

theorem pairQuery_value (before : Masked.Input m) (after : Masked.Input n) (lo hi : Nat)
    (counts : Array Nat) (base q s K : Nat) :
    (pairQuery before after lo hi counts base q s K).1=
      MaskedCluster.pairQuery before.data after.data lo hi counts base q s K := by
  simp only [pairQuery,pairWindows_value,MaskedCluster.pairQuery]

theorem pairQuery_extra (before : Masked.Input m) (after : Masked.Input n) (lo hi : Nat)
    (counts : Array Nat) (base q s K : Nat) :
    (pairQuery before after lo hi counts base q s K).2≤
      (MaskedCluster.pairQuery before.data after.data lo hi counts base q s K).slots+
      (MaskedCluster.pairQuery before.data after.data lo hi counts base q s K).arithmetic+
      pairCost m n K+1 := by
  have h:=pairWindows_work before after lo hi K
  unfold pairQuery
  dsimp only
  rw [pairWindows_value]
  unfold MaskedCluster.pairQuery
  omega

theorem pairQuery_inflate (before : Masked.Input m) (after : Masked.Input n) (lo hi : Nat)
    (counts : Array Nat) (base q s K : Nat) :
    (pairQuery before after lo hi counts base q s K).2≤
      (pairCost m n K+2)*
      ((MaskedCluster.pairQuery before.data after.data lo hi counts base q s K).slots+
       (MaskedCluster.pairQuery before.data after.data lo hi counts base q s K).arithmetic+1) := by
  exact Nat.le_trans (pairQuery_extra before after lo hi counts base q s K)
    (by simpa only [Nat.add_assoc] using (Masked.inflate
      ((MaskedCluster.pairQuery before.data after.data lo hi counts base q s K).slots+
       (MaskedCluster.pairQuery before.data after.data lo hi counts base q s K).arithmetic)
      (pairCost m n K+1)))

def sourcePairQuery (before : Masked.Input m) (after : Masked.Input n) (lo hi : Nat)
    (idx : MaskedCluster.Mutable.Index) (q s K : Nat) (window : MaskedCluster.SourceWindow) :
    Result MaskedCluster.Mutable.Answer :=
  if window.enabled then
    let ws:=sourceWindows before after lo hi s q K window
    let out:=MaskedCluster.Mutable.queryWindows idx q K s ws.1
    (out,ws.2+out.work+2)
  else (⟨false,1⟩,2)

theorem sourcePairQuery_value (before : Masked.Input m) (after : Masked.Input n) (lo hi : Nat)
    (idx : MaskedCluster.Mutable.Index) (q s K : Nat) (window : MaskedCluster.SourceWindow) :
    (sourcePairQuery before after lo hi idx q s K window).1=
      MaskedCluster.Mutable.sourcePairQuery before.data after.data lo hi idx q s K window := by
  unfold sourcePairQuery MaskedCluster.Mutable.sourcePairQuery
  split <;> simp only [sourceWindows_value]

theorem sourcePairQuery_extra (before : Masked.Input m) (after : Masked.Input n) (lo hi : Nat)
    (idx : MaskedCluster.Mutable.Index) (q s K : Nat) (window : MaskedCluster.SourceWindow) :
    (sourcePairQuery before after lo hi idx q s K window).2≤
      (MaskedCluster.Mutable.sourcePairQuery before.data after.data lo hi idx q s K window).work+
      sourceCost m n K+2 := by
  unfold sourcePairQuery MaskedCluster.Mutable.sourcePairQuery
  split
  · have h:=sourceWindows_work before after lo hi s q K window
    dsimp only
    rw [sourceWindows_value]
    omega
  · dsimp only
    omega

theorem sourcePairQuery_inflate (before : Masked.Input m) (after : Masked.Input n) (lo hi : Nat)
    (idx : MaskedCluster.Mutable.Index) (q s K : Nat) (window : MaskedCluster.SourceWindow) :
    (sourcePairQuery before after lo hi idx q s K window).2≤
      (sourceCost m n K+3)*
      ((MaskedCluster.Mutable.sourcePairQuery before.data after.data lo hi idx q s K window).work+1) := by
  exact Nat.le_trans (sourcePairQuery_extra before after lo hi idx q s K window)
    (by simpa only [Nat.add_assoc] using (Masked.inflate
      (MaskedCluster.Mutable.sourcePairQuery before.data after.data lo hi idx q s K window).work
      (sourceCost m n K+2)))

end REWB.PeriodicConstruction.Cluster
