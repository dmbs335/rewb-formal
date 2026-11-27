import REWB.ResidualSeparatedWindow

/-! Each actual low-start or large-period schedule entry creates at
most one separated window. Period multiples give its equality; the
window includes every compatible nonoverlapping outer copy at that
start. No text scan or further period enumeration occurs here. -/
namespace REWB.ResidualRunWindows
open REWB.Periodic REWB.RunGeometry REWB.ResidualSeparated
variable {α : Type} {σ : Nat}

def candidate (R : Bounds) (p distance : Nat) : Option IndexedGrid.Strip×Nat :=
  if R.lo≤p ∧ p+distance≤R.hi then
    (some ⟨p,min (R.hi-distance) (p+distance),distance⟩,11)
  else (none,5)

theorem candidate_work (R : Bounds) (p distance : Nat) :
    (candidate R p distance).2≤11 := by
  unfold candidate
  split <;> simp

theorem shifted_equal (f : Nat→α) (n : Nat) (R : Bounds) (p r distance : Nat)
    (hR : R.Valid f n) (hp : R.lo≤p) (hpr : p≤r) (hr : r+distance≤R.hi)
    (hd : R.period∣distance) :
    Spec.slice (segment f 0 n) p r=Spec.slice (segment f 0 n) (p+distance) (r+distance) := by
  obtain ⟨k,hk⟩:=hd
  have hn:=hR.2.1
  rw [←GlobalSemanticCoverage.factor_slice f n p r hpr (by omega),
    ←GlobalSemanticCoverage.factor_slice f n (p+distance) (r+distance) (by omega) (by omega)]
  simp only [P2Periodic.factor,Nat.add_sub_add_right]
  apply (segment_eq_points f p (p+distance) (r-p)).mpr
  intro i hi
  have ht:=period_multiple hR.2.2.2.1.2.1 (p+i-R.lo) k
    (by rw [Nat.mul_comm k R.period]; omega)
  change f (R.lo+(p+i-R.lo))=f (R.lo+(p+i-R.lo+k*R.period)) at ht
  have h1 : R.lo+(p+i-R.lo)=p+i := by omega
  have h2 : R.lo+(p+i-R.lo+k*R.period)=p+distance+i := by
    rw [Nat.mul_comm k R.period]
    omega
  simpa only [h1,h2] using ht

theorem candidate_sound (f : Nat→α) (n : Nat) (R : Bounds) (p distance : Nat)
    (hR : R.Valid f n) (hd : R.period∣distance) (c : IndexedGrid.Strip)
    (hc : (candidate R p distance).1=some c) :
    Window (segment f 0 n) c.lo c.hi c.distance := by
  unfold candidate at hc
  split at hc
  · rename_i h
    obtain ⟨hp,hr⟩:=h
    have he : c=⟨p,min (R.hi-distance) (p+distance),distance⟩:=
      (Option.some.inj hc).symm
    subst c
    change Window (segment f 0 n) p (min (R.hi-distance) (p+distance)) distance
    have hmin1:=Nat.min_le_left (R.hi-distance) (p+distance)
    have hmin2:=Nat.min_le_right (R.hi-distance) (p+distance)
    have hn:=hR.2.1
    refine ⟨by omega,by simp only [segment_length]; omega,hmin2,?_⟩
    exact shifted_equal f n R p _ distance hR hp (by omega) (by omega) hd
  · cases hc

theorem candidate_complete (R : Bounds) (p e distance : Nat)
    (hp : R.lo≤p) (hpe : p≤e) (hsep : e≤p+distance) (hr : e+distance≤R.hi) :
    ∃c,(candidate R p distance).1=some c ∧ c.lo=p ∧ e≤c.hi ∧ c.distance=distance := by
  refine ⟨⟨p,min (R.hi-distance) (p+distance),distance⟩,?_,rfl,?_,rfl⟩
  · simp only [candidate,if_pos (show R.lo≤p ∧ p+distance≤R.hi by omega)]
  · change e≤min (R.hi-distance) (p+distance)
    exact Nat.le_min.mpr ⟨by omega,hsep⟩

theorem large_pair_multiple (R : Bounds) (p distance : Nat)
    (hm : (p,distance)∈GlobalCoverage.largePairs R) : R.period∣distance := by
  obtain ⟨k,_,h⟩:=List.mem_flatMap.mp hm
  obtain ⟨i,_,he⟩:=List.mem_map.mp h
  have hd : (k+1)*R.period=distance:=congrArg Prod.snd he
  exact ⟨k+1,by simpa only [Nat.mul_comm] using hd.symm⟩

theorem low_valid (f : Nat→Fin σ) (n stride gap : Nat) (R : Bounds) (p : Nat)
    (hm : (R,p)∈RankIndexSchedule.low f n stride gap) : R.Valid f n := by
  obtain ⟨hR,_⟩:=(GlobalCoverage.lowSchedule_mem gap _ R p).mp hm
  exact RankIndexSchedule.generate_sound f n stride R hR

theorem large_valid (f : Nat→Fin σ) (n stride period : Nat) (R : Bounds) (p distance : Nat)
    (hm : (R,(p,distance))∈RankIndexSchedule.large f n stride period) :
    R.Valid f n ∧ R.period∣distance := by
  obtain ⟨hR,hp⟩:=(GlobalCoverage.largeSchedule_mem _ R p distance).mp hm
  exact ⟨RankIndexSchedule.generate_sound f n stride R (List.mem_filter.mp hR).1,
    large_pair_multiple R p distance hp⟩

theorem low_window (f : Nat→Fin σ) (n stride gap : Nat) (R : Bounds) (p : Nat)
    (hm : (R,p)∈RankIndexSchedule.low f n stride gap) (c : IndexedGrid.Strip)
    (hc : (candidate R p R.period).1=some c) : Window (segment f 0 n) c.lo c.hi c.distance :=
  candidate_sound f n R p R.period (low_valid f n stride gap R p hm) (Nat.dvd_refl _) c hc

theorem large_window (f : Nat→Fin σ) (n stride period : Nat) (R : Bounds) (p distance : Nat)
    (hm : (R,(p,distance))∈RankIndexSchedule.large f n stride period) (c : IndexedGrid.Strip)
    (hc : (candidate R p distance).1=some c) : Window (segment f 0 n) c.lo c.hi c.distance :=
  candidate_sound f n R p distance (large_valid f n stride period R p distance hm).1
    (large_valid f n stride period R p distance hm).2 c hc

end REWB.ResidualRunWindows
