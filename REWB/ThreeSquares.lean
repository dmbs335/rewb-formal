import REWB.RunGeometry

/-! A weak three-prefix-squares lemma proved from Fine-Wilf alone.
    Three distinct primitive-square periods at one start cannot lie
    within one dyadic scale. The proof uses periods q-p and r-q on
    shorter prefixes and extends their gcd across the middle prefix.
    No external square-counting theorem is introduced. -/
namespace REWB.RunGeometry
open REWB.Periodic
variable {α : Type}

theorem three_squares (f : Nat→α) (p q r : Nat)
    (hp : LeastPeriod f (2*p) p)
    (hq : Period f (2*q) q) (hr : Period f (2*r) r)
    (hpq : p<q) (hqr : q<r) : 2*p<r := by
  by_cases h : 2*p<r
  · exact h
  · let d := q-p
    let e := r-q
    let g := Nat.gcd d e
    have hd : 0<d := by dsimp [d]; omega
    have he : 0<e := by dsimp [e]; omega
    have hde : d+e≤p := by dsimp [d,e]; omega
    have hg : 0<g := Nat.gcd_pos_of_pos_left e hd
    have hgd : g≤d := Nat.le_of_dvd hd (Nat.gcd_dvd_left d e)
    have hD : Period f p d := by
      have hh := subtract_period (show p≤q by omega) hp.2.1
        (restrict hq (show 2*p≤2*q by omega))
      rw [show 2*p-p=p by omega] at hh
      exact hh
    have hE : Period f q e := by
      have hh := subtract_period (show q≤r by omega) hq
        (restrict hr (show 2*q≤2*r by omega))
      rw [show 2*q-q=q by omega] at hh
      exact hh
    have hG : Period f p g :=
      fineWilf f p d e hd he (by omega) hD (restrict hE (by omega))
    have hGq : Period f q g :=
      extend_period he (by omega : e≤p) (Nat.gcd_dvd_right d e) hE hG
    have hPq : Period f q p := restrict hp.2.1 (by omega)
    let t := Nat.gcd p g
    have ht : 0<t := Nat.gcd_pos_of_pos_left g hp.1
    have htG : t≤g := Nat.le_of_dvd hg (Nat.gcd_dvd_right p g)
    have hsize : p+g≤q+Nat.gcd p g := by
      have hh : d=q-p := rfl
      omega
    have hTq : Period f q t :=
      fineWilf f q p g hp.1 hg hsize hPq hGq
    have hT : Period f (2*p) t :=
      extend_period hp.1 (Nat.le_refl p) (Nat.gcd_dvd_left p g) hp.2.1
        (restrict hTq (by omega))
    have hmin := hp.2.2 t ht hT
    omega

/-- Dyadic period class: at most two distinct primitive squares can
    start at one position. -/
theorem three_same_scale (f : Nat→α) (n i b p q r : Nat)
    (hp : PrimitiveSquare f n i p) (hq : PrimitiveSquare f n i q)
    (hr : PrimitiveSquare f n i r)
    (hpq : p<q) (hqr : q<r) (hb : b≤p) (hrb : r<2*b) : False := by
  have h := three_squares (shift f i) p q r hp.2 hq.2.2.1 hr.2.2.1 hpq hqr
  omega

end REWB.RunGeometry
