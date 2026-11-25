import REWB.BoundaryBorderRegularQuery

/-! The actual LCE selector certifies the periods needed by the regular
acceptance query. Its point branch needs no periodicity; a progression
branch carries the source period before its break and the target period
long enough for every selected capture. These are consequences of the
shared rank index, not supplied component oracles. -/
namespace REWB.BoundaryBorder.Regular
open REWB.Spec REWB.Periodic REWB.RunGeometry
variable {α : Type} {σ : Nat}

def Supported (f : Nat→α) (a j : Nat) : Choice→Prop
  | .empty => True
  | .point _ => True
  | .progression first q lo hi =>
      0<q ∧ OnPeriod f first a q ∧
        ∃extent,OnPeriod f j (j+extent) q ∧
          ∀p,Member first q lo hi p→a-p≤extent

theorem select_supported (f : Nat→Fin σ) (n first q lo hi a j : Nat)
    (hq : 0<q) (hs : first+q≤n) (hj : j+q≤n) :
    Supported f a j (select (LCEIndex.prepare f n) n first q lo hi a j).choice := by
  have sp:=extend_correct f n first q hs
  have tp:=extend_correct f n j q hj
  have source : OnPeriod f first (first+(extend (LCEIndex.prepare f n) n first q).extent) q := by
    apply (on_iff _ _ _ _).mpr
    simpa only [Nat.add_sub_cancel_left] using sp.periodic
  have target : OnPeriod f j (j+(extend (LCEIndex.prepare f n) n j q).extent) q := by
    apply (on_iff _ _ _ _).mpr
    simpa only [Nat.add_sub_cancel_left] using tp.periodic
  simp only [select,choose]
  split
  · rename_i ha
    refine ⟨hq,on_restrict f first _ q first a source (Nat.le_refl _) ha,
      (extend (LCEIndex.prepare f n) n j q).extent,target,?_⟩
    intro p hp
    exact (band_iff first q lo hi a _ p).mp hp |>.2.2
  · split
    · split <;> trivial
    · trivial

theorem select_progression_periods (f : Nat→Fin σ) (n first q lo hi a j : Nat)
    (hq : 0<q) (hs : first+q≤n) (hj : j+q≤n)
    (outFirst outStep lower upper : Nat)
    (he : (select (LCEIndex.prepare f n) n first q lo hi a j).choice=
      .progression outFirst outStep lower upper) :
    0<outStep ∧ OnPeriod f outFirst a outStep ∧
      ∃extent,OnPeriod f j (j+extent) outStep ∧
        ∀p,Member outFirst outStep lower upper p→a-p≤extent := by
  have hh:=select_supported f n first q lo hi a j hq hs hj
  rwa [he] at hh

theorem supported_geometry (w : Word α) (fallback : α) (first q lo hi pLo m a j r : Nat)
    (hs : Supported (ArrayText.read w.toArray fallback) a j (.progression first q lo hi))
    (hp : Member first q lo hi pLo) (hm : 0<m) (hlast : pLo+m*q≤a)
    (ha : a≤w.length) (ht : endAt j a pLo≤r) (hr : r≤w.length) :
    Geometry w fallback pLo q m a j r := by
  rcases hs with ⟨hq,source,extent,target,hbound⟩
  have hb:=hbound pLo hp
  refine ⟨hq,hm,hlast,ha,ht,hr,?_,?_⟩
  · exact on_restrict _ first a q pLo (pLo+m*q) source hp.2.2.1 hlast
  · apply on_restrict _ j (j+extent) q _ _ target
    · unfold endAt
      omega
    · unfold endAt
      omega

end REWB.BoundaryBorder.Regular
