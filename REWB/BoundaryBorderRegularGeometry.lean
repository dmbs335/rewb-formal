import REWB.BoundaryBorderRegularMaps
import REWB.MaskedClusterFactors
import REWB.BoundaryBorderSeed

/-! Physical factorization for a clipped progression of boundary starts.
The source and target periodicity hypotheses concern only the repeated
blocks. All displayed words and arithmetic traversals in this file are
erased proof objects; execution uses the six materialized range maps. -/
namespace REWB.BoundaryBorder.Regular
open REWB.Spec REWB.Periodic REWB.RunGeometry REWB.MaskedCluster
variable {α : Type} {σ : Nat}

def endAt (j a p : Nat) : Nat := j+(a-p)

structure Geometry (w : Word α) (fallback : α) (pLo q m a j r : Nat) : Prop where
  step : 0<q
  count : 0<m
  last : pLo+m*q≤a
  sourceEnd : a≤w.length
  finish : endAt j a pLo≤r
  right : r≤w.length
  source : OnPeriod (ArrayText.read w.toArray fallback) pLo (pLo+m*q) q
  target : OnPeriod (ArrayText.read w.toArray fallback)
    (endAt j a pLo-m*q) (endAt j a pLo) q

theorem Geometry.bounds (w : Word α) (fallback : α) (pLo q m a j r : Nat)
    (hg : Geometry w fallback pLo q m a j r) :
    pLo+q≤pLo+m*q ∧ pLo≤a ∧ q≤endAt j a pLo ∧ m*q≤endAt j a pLo := by
  have hm:=Nat.mul_le_mul_right q (Nat.succ_le_of_lt hg.count)
  have hb:=hg.last
  simp only [Nat.one_mul] at hm
  unfold endAt
  omega

theorem prefix_slice (w : Word α) (fallback : α) (pLo q m a j r k : Nat)
    (hg : Geometry w fallback pLo q m a j r) (hk : k≤m) :
    slice w 0 (pLo+k*q)=slice w 0 pLo++repeatWord (slice w pLo (pLo+q)) k := by
  have hm:=Nat.mul_le_mul_right q hk
  have hb:=hg.last
  have ht:=hg.sourceEnd
  have h:=MaskedCluster.prefix_factor w fallback 0 pLo (pLo+m*q) q 0 k hg.source
    (Nat.zero_le _) (by omega) (by omega) (by omega)
  simpa only [Nat.zero_mul,Nat.add_zero,Nat.sub_zero] using h

theorem capture (w : Word α) (fallback : α) (pLo q m a j r k : Nat)
    (hg : Geometry w fallback pLo q m a j r) (hk : k≤m) :
    slice w (pLo+k*q) a=repeatWord (slice w pLo (pLo+q)) (m-k)++slice w (pLo+m*q) a := by
  have hm:=Nat.mul_le_mul_right q hk
  have hb:=hg.last
  have ha:=hg.sourceEnd
  have h:=MaskedCluster.prefix_factor w fallback (pLo+k*q) pLo (pLo+m*q) q k m hg.source
    hk (Nat.le_refl _) (Nat.le_refl _) (by omega)
  have hs : slice w (pLo+k*q) (pLo+k*q)=[] := by simp only [slice,Nat.sub_self,List.take_zero]
  rw [hs,List.nil_append] at h
  rw [OuterColumn.slice_split w (pLo+k*q) (pLo+m*q) a (by omega) hb,h]

theorem suffix_blocks (w : Word α) (fallback : α) (low q m k r : Nat)
    (hp : OnPeriod (ArrayText.read w.toArray fallback) low (low+m*q) q)
    (hm : 0<m) (hk : k≤m) (hr : low+m*q≤r) (hn : r≤w.length) :
    slice w (low+(m-k)*q) r=
      repeatWord (slice w (low+m*q-q) (low+m*q)) k++slice w (low+m*q) r := by
  have hmul:=Nat.mul_le_mul_right q (Nat.sub_le m k)
  have h:=MaskedCluster.prefix_factor w fallback (low+(m-k)*q) low (low+m*q) q (m-k) m hp
    (Nat.sub_le _ _) (Nat.le_refl _) (Nat.le_refl _) (by omega)
  have hs : slice w (low+(m-k)*q) (low+(m-k)*q)=[] := by simp only [slice,Nat.sub_self,List.take_zero]
  rw [hs,List.nil_append,Nat.sub_sub_self hk] at h
  have hlast : (m-1)*q+q=m*q := by
    have he:=congrArg (fun z=>z*q) (Nat.sub_add_cancel (Nat.succ_le_of_lt hm))
    simpa only [Nat.add_mul,Nat.one_mul] using he
  have he:=MaskedPeriodic.Text.actual_equal_copies w fallback low (low+m*q) q q (m-1)
    hp (by omega) (by omega)
  rw [show low+(m-1)*q=low+m*q-q by omega,
    show low+m*q-q+q=low+m*q by omega] at he
  rw [he] at h
  rw [OuterColumn.slice_split w (low+(m-k)*q) (low+m*q) r (by omega) hr,h]

theorem suffix (w : Word α) (fallback : α) (pLo q m a j r k : Nat)
    (hg : Geometry w fallback pLo q m a j r) (hk : k≤m) :
    slice w (endAt j a (pLo+k*q)) r=
      repeatWord (slice w (endAt j a pLo-q) (endAt j a pLo)) k++
        slice w (endAt j a pLo) r := by
  have hb:=hg.bounds w fallback pLo q m a j r
  have hmk:=Nat.mul_le_mul_right q hk
  have hd : (m-k)*q=m*q-k*q := Nat.sub_mul m k q
  have hsum : endAt j a pLo-m*q+m*q=endAt j a pLo := by omega
  have hp : OnPeriod (ArrayText.read w.toArray fallback) (endAt j a pLo-m*q)
      (endAt j a pLo-m*q+m*q) q := by rw [hsum]; exact hg.target
  have hx:=suffix_blocks w fallback (endAt j a pLo-m*q) q m k r hp hg.count hk
    (by rw [hsum]; exact hg.finish) hg.right
  rw [hsum] at hx
  have hpos : endAt j a pLo-m*q+(m-k)*q=endAt j a (pLo+k*q) := by
    have hl:=hg.last
    unfold endAt at *
    omega
  rwa [hpos] at hx

end REWB.BoundaryBorder.Regular
