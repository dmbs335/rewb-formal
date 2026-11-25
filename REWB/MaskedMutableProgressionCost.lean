import REWB.MaskedMutableProgressionAP

/-! Closed logarithmic operation bounds for the actual dynamic source
index. They depend on the physical window length, never on the step or
on the number of residue classes. -/
namespace REWB.MaskedMutableProgression

def Index.LogSized (idx : Index) : Prop := idx.levels=height idx.len

theorem build_logSized (mask : Array Bool) (base len step : Nat) :
    (build mask base len step).index.LogSized := rfl

theorem erase_logSized (idx : Index) (hh : idx.LogSized) (p : Nat) :
    (erase idx p).index.LogSized := by
  unfold Index.LogSized
  rw [erase_levels,erase_len]
  exact hh

theorem height_capacity_le (len : Nat) : 2^(height len)≤4*(len+1)*(len+1) := by
  have hh:=Nat.mul_le_mul_right 2 (Nat.log2_self_le (n:=len+1) (by omega))
  have hp : 2^((len+1).log2+1)≤2*(len+1) := by rw [Nat.pow_succ]; omega
  have hsq:=Nat.mul_le_mul hp hp
  rw [show height len=((len+1).log2+1)+((len+1).log2+1) by unfold height; omega,Nat.pow_add]
  calc
    2^((len+1).log2+1)*2^((len+1).log2+1) ≤ (2*(len+1))*(2*(len+1)) := hsq
    _ = 4*(len+1)*(len+1) := by
      rw [show (4:Nat)=2*2 by decide]
      ac_rfl

theorem build_log_work (mask : Array Bool) (base len step : Nat) :
    (build mask base len step).work≤40*(len+1)*((len+1).log2+1) := by
  have hh:=build_work mask base len step
  let L:=(len+1).log2+1
  have hL : 1≤L := by dsimp [L]; omega
  have hc : 10*height len+14≤34*L := by unfold height; dsimp [L]; omega
  have hm:=Nat.mul_le_mul_left len hc
  have ht : 2*height len+10≤14*L := by unfold height; dsimp [L]; omega
  calc
    (build mask base len step).work ≤ len*(34*L)+14*L := by omega
    _ = (34*len+14)*L := by rw [Nat.add_mul]; ac_rfl
    _ ≤ (40*(len+1))*L := Nat.mul_le_mul_right L (by omega)

theorem member_log_work (idx : Index) (hh : idx.LogSized) (p : Nat) :
    (member idx p).2≤19*((idx.len+1).log2+1) := by
  have hw:=member_work idx p
  rw [hh] at hw
  unfold height at hw
  omega

theorem erase_log_work (idx : Index) (hh : idx.LogSized) (p : Nat) :
    (erase idx p).work≤37*((idx.len+1).log2+1) := by
  have hw:=erase_work idx p
  rw [hh] at hw
  unfold height at hw
  omega

theorem grid_log_work (idx : Index) (hh : idx.LogSized) (start wanted : Nat) :
    (grid idx start wanted).work≤49*((idx.len+1).log2+1) := by
  have hw:=grid_work idx start wanted
  rw [hh] at hw
  unfold height at hw
  omega

theorem ap_log_work (idx : Index) (hh : idx.LogSized) (q K s lo hi r : Nat) :
    (ap idx q K s lo hi r).work≤79*((idx.len+1).log2+1) := by
  have hw:=ap_work idx q K s lo hi r
  rw [hh] at hw
  unfold height at hw
  omega

theorem log_window (len n : Nat) (hn : len≤n) : (len+1).log2≤(n+1).log2 := by
  apply (Nat.le_log2 (n:=n+1) (by omega)).mpr
  exact Nat.le_trans (Nat.log2_self_le (n:=len+1) (by omega)) (by omega)

theorem erase_global_work (idx : Index) (hh : idx.LogSized) (n : Nat) (hn : idx.len≤n) (p : Nat) :
    (erase idx p).work≤37*((n+1).log2+1) := by
  have hw:=erase_log_work idx hh p
  have hl:=log_window idx.len n hn
  omega

theorem ap_global_work (idx : Index) (hh : idx.LogSized) (n : Nat) (hn : idx.len≤n)
    (q K s lo hi r : Nat) : (ap idx q K s lo hi r).work≤79*((n+1).log2+1) := by
  have hw:=ap_log_work idx hh q K s lo hi r
  have hl:=log_window idx.len n hn
  omega

end REWB.MaskedMutableProgression
