import REWB.MaskedPeriodicTextSlices
import REWB.MaskedClusterStage

/-! Actual text factors for one jump in an arithmetic cluster. The
    post-anchor block is taken immediately before the first anchored
    endpoint, so it remains in bounds even for a singleton query window.
    Neither backward transitions nor inverse transformation maps occur.
-/
namespace REWB.MaskedCluster
open REWB.Periodic REWB.Spec REWB.P2Periodic
variable {α : Type}

theorem post_factor (f : Nat→α) (n q H k hi : Nat) (hp : Period f n q)
    (hq : q≤H) (hk : k≤hi) (hb : hi*q+H≤n) :
    factor f (k*q+H) (hi*q+H)=
      repeatWord (segment f (H-q) q) (hi-k) := by
  have hmul : k*q+(hi-k)*q=hi*q := by rw [←Nat.add_mul,Nat.add_sub_of_le hk]
  have hstart : H-q+(k+1)*q=k*q+H := by rw [Nat.add_mul,Nat.one_mul]; omega
  have hlen : hi*q+H-(k*q+H)=(hi-k)*q := by rw [Nat.sub_mul]; omega
  have hs := segment_same_phase hp (H-q) (k+1) ((hi-k)*q) (by omega)
  rw [factor,hlen,←hstart,←hs,segment_repeated hp (H-q) (hi-k) (by omega)]

theorem prefix_factor (w : Word α) (fallback : α) (I s R q lo k : Nat)
    (hp : RunGeometry.OnPeriod (ArrayText.read w.toArray fallback) s R q)
    (hlo : lo≤k) (hI : I≤s+lo*q) (hb : s+k*q≤R) (hn : R≤w.length) :
    slice w I (s+k*q)=slice w I (s+lo*q)++
      repeatWord (slice w s (s+q)) (k-lo) := by
  have hper := (RunGeometry.on_iff _ s R q).mp hp
  have hfac := MaskedPeriodic.Text.zero_gap (shift (ArrayText.read w.toArray fallback) s)
    (R-s) q lo k hper hlo (by omega)
  rw [ArrayText.shifted_factor w fallback s (lo*q) (k*q)
    (Nat.mul_le_mul_right q hlo) (by omega)] at hfac
  by_cases hz : k=lo
  · subst k
    simp only [Nat.sub_self,repeatWord,List.append_nil]
  · have hblock : s+q≤w.length := by
      have hk : 1≤k := by omega
      have hmul:=Nat.mul_le_mul_right q hk
      omega
    rw [MaskedPeriodic.Text.segment_slice w fallback s q hblock] at hfac
    rw [OuterColumn.slice_split w I (s+lo*q) (s+k*q) hI (by have hh:=Nat.mul_le_mul_right q hlo; omega),hfac]

theorem suffix_factor (w : Word α) (fallback : α) (s R q H k hi O : Nat)
    (hp : RunGeometry.OnPeriod (ArrayText.read w.toArray fallback) s R q)
    (hq : q≤H) (hk : k≤hi) (hb : s+hi*q+H≤R) (hn : R≤w.length)
    (hO : s+hi*q+H≤O) (hOn : O≤w.length) :
    slice w (s+k*q+H) O=
      repeatWord (slice w (s+(H-q)) (s+H)) (hi-k)++slice w (s+hi*q+H) O := by
  have hper := (RunGeometry.on_iff _ s R q).mp hp
  have hfac := post_factor (shift (ArrayText.read w.toArray fallback) s) (R-s) q H k hi
    hper hq hk (by omega)
  have hmul:=Nat.mul_le_mul_right q hk
  rw [ArrayText.shifted_factor w fallback s (k*q+H) (hi*q+H) (by omega) (by omega)] at hfac
  have hblock := ArrayText.shifted_factor w fallback s (H-q) H (by omega) (by omega)
  have hlen : H-(H-q)=q := by omega
  simp only [factor,hlen] at hblock
  rw [hblock] at hfac
  simp only [←Nat.add_assoc] at hfac
  rw [OuterColumn.slice_split w (s+k*q+H) (s+hi*q+H) O (by omega) hO,hfac]

end REWB.MaskedCluster
