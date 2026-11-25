import REWB.MaskedRunCatalogCost
import REWB.MaskedClusterDescriptorAnchor

/-! A dense complete-class descriptor lies in one maximal run, including
its entire AP and the current capture length. This is erased geometry;
execution still extends only the first actual dense adjacent pair. -/
namespace REWB.MaskedRunCatalog
open REWB.Periodic REWB.RunGeometry REWB.MaskedRunDiscovery
variable {α : Type}

theorem descriptor_period (f : Nat→α) (n base L : Nat) (xs : List Nat)
    (d : MaskedClusterDescriptor.Descriptor)
    (hc : Complete f n base L xs) (hg : MaskedClusterDescriptor.Geometry f n base L xs d)
    (hm : 0<d.repetitions) : OnPeriod f d.first (d.last+L) d.period := by
  have hd:=hg.dense hm
  have member (k : Nat) (hk : k≤d.repetitions) : d.first+k*d.period∈xs :=
    ((hg.members _).mpr ⟨k,hk,rfl⟩).1
  have hf : d.first∈xs := by simpa only [Nat.zero_mul,Nat.add_zero] using member 0 (Nat.zero_le _)
  have period (k : Nat) (hk : k≤d.repetitions) :
      OnPeriod f (d.first+k*d.period) (d.first+k*d.period+L) d.period := by
    have he : segment f d.first L=segment f (d.first+k*d.period) L :=
      ((hc d.first).mp hf).2.trans ((hc _).mp (member k hk)).2.symm
    have hp:=MaskedLocalAnchor.period_copy f d.first (d.first+k*d.period) L d.period he hd.2.1.2.1
    apply (on_iff _ _ _ _).mpr
    simpa only [Nat.add_sub_cancel_left] using hp
  have joined (k : Nat) (hk : k≤d.repetitions) :
      OnPeriod f d.first (d.first+k*d.period+L) d.period := by
    induction k with
    | zero => simpa only [Nat.zero_mul,Nat.add_zero] using period 0 (Nat.zero_le _)
    | succ k ih =>
      have hp:=ih (by omega)
      have hn:=period (k+1) hk
      have hadd : (k+1)*d.period=k*d.period+d.period := by rw [Nat.add_mul,Nat.one_mul]
      have hl : d.first≤d.first+(k+1)*d.period := by omega
      have ho : d.first+(k+1)*d.period+d.period≤d.first+k*d.period+L := by
        rw [hadd]
        omega
      have hu:=merge_periods f d.first (d.first+k*d.period+L)
        (d.first+(k+1)*d.period) (d.first+(k+1)*d.period+L) d.period hl ho hp hn
      rw [Nat.max_eq_right (by rw [hadd]; omega)] at hu
      exact hu
  rw [hg.endpoint]
  exact joined d.repetitions (Nat.le_refl _)

theorem run_contains_right (f : Nat→α) (n : Nat) (R : Bounds) (start finish : Nat)
    (hv : R.Valid f n) (hs : R.lo≤start) (hi : start+R.period≤R.hi)
    (hp : OnPeriod f start finish R.period) (hf : finish≤n) : finish≤R.hi := by
  by_cases hle : finish≤R.hi
  · exact hle
  · have hq:=hv.2.2.2.1.1
    have he : f (R.hi-R.period)=f R.hi := by
      have hh:=hp (R.hi-R.period) (by omega) (by omega)
      simpa only [Nat.sub_add_cancel (show R.period≤R.hi by omega)] using hh
    have hnext:=on_extend_right f R.lo R.hi R.period (run_on _ _ _ _ _ hv) hq (by omega) he
    have hp':=(on_iff f R.lo (R.hi+1) R.period).mp hnext
    rw [show R.hi+1-R.lo=R.hi-R.lo+1 by have hh:=hv.1; omega] at hp'
    rcases hv.2.2.2.2.2 with hz|hn
    · omega
    · exact False.elim (hn hp')

end REWB.MaskedRunCatalog
