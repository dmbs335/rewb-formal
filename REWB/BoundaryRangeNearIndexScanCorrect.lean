import REWB.BoundaryRangeNearIndexScan

/-! The three bounded loops implement exactly their geometric regions,
including empty captures and coinciding boundaries. -/
namespace REWB.BoundaryRange.NearIndex
open REWB.BoundaryApplication
open REWB.Spec (slice)
variable {σ : Nat}

theorem atSeparated_correct (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ))
    (fallback : Fin σ) (g0 g : Nat) (h0g : g0≤g) (hg : g≤w.length)
    (left right p : Nat) (h0l : g0≤left) (hlp : left≤p) (hpg : p≤g) (hr : right≤w.length) :
    (atSeparated (build A B C K D E w fallback g0 g h0g hg) left right p).1=true ↔
      K.accepts (slice w left p) ∧ ∃a j,a≤g0 ∧ g≤j ∧ Copy A B E w a j right ∧
        C.accepts (slice w a p) ∧ D.accepts (slice w p j) := by
  change ((regular K (Range.build K w) left p).1 &&
    (separated (build A B C K D E w fallback g0 g h0g hg) p right).1)=true ↔ _
  rw [Bool.and_eq_true,regular_correct K w left p hlp (by omega),
    separated_correct A B C K D E w fallback g0 g h0g hg p right (by omega) hpg hr]

theorem atEnd_correct (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ))
    (fallback : Fin σ) (g0 g : Nat) (h0g : g0≤g) (hg : g≤w.length)
    (right p a : Nat) (hap : a≤p) (hpg : p≤g) (hr : right≤w.length) :
    (atEnd (build A B C K D E w fallback g0 g h0g hg) right p a).1=true ↔
      C.accepts (slice w a p) ∧ ∃j,g≤j ∧ Copy A B E w a j right ∧ D.accepts (slice w p j) := by
  have ha : a≤(build A B C K D E w fallback g0 g h0g hg).length := by
    change a≤w.length
    omega
  unfold atEnd
  rw [dif_pos ha]
  change ((regular C (Range.build C w) a p).1 &&
    (fixedEnd (build A B C K D E w fallback g0 g h0g hg) p ⟨a,_⟩ right).1)=true ↔ _
  rw [Bool.and_eq_true,regular_correct C w a p hap (by omega),
    fixedEnd_correct A B C K D E w fallback g0 g h0g hg p right hpg hr ⟨a,_⟩ (by change a≤g; omega)]

theorem endsAt_correct (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ))
    (fallback : Fin σ) (g0 g : Nat) (h0g : g0≤g) (hg : g≤w.length)
    (left right p : Nat) (h0l : g0≤left) (hlp : left≤p) (hpg : p≤g) (hr : right≤w.length) :
    (endsAt (build A B C K D E w fallback g0 g h0g hg) left right p).1=true ↔
      K.accepts (slice w left p) ∧ ∃a,g0<a ∧ a≤p ∧ C.accepts (slice w a p) ∧
        ∃j,g≤j ∧ Copy A B E w a j right ∧ D.accepts (slice w p j) := by
  change ((regular K (Range.build K w) left p).1 &&
    (scan (atEnd (build A B C K D E w fallback g0 g h0g hg) right p) (g0+1) (p-g0)).1)=true ↔ _
  rw [Bool.and_eq_true,regular_correct K w left p hlp (by omega),scan_correct]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨a,ha,hap,h⟩
    have hap' : a≤p := by omega
    exact ⟨a,by omega,hap',(atEnd_correct A B C K D E w fallback g0 g h0g hg right p a hap' hpg hr).mp h⟩
  · rintro ⟨a,ha,hap,h⟩
    exact ⟨a,by omega,by omega,(atEnd_correct A B C K D E w fallback g0 g h0g hg right p a hap hpg hr).mpr h⟩

theorem atStart_correct (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ))
    (fallback : Fin σ) (g0 g : Nat) (h0g : g0≤g) (hg : g≤w.length)
    (right p j : Nat) (h0p : g0≤p) (hpj : p≤j) (hjg : j≤g) (hjr : j≤right)
    (hr : right≤w.length) :
    (atStart (build A B C K D E w fallback g0 g h0g hg) right p j).1=true ↔
      D.accepts (slice w p j) ∧ ∃a,a≤g0 ∧ Copy A B E w a j right ∧ C.accepts (slice w a p) := by
  have hj : j≤(build A B C K D E w fallback g0 g h0g hg).length := by
    change j≤w.length
    omega
  unfold atStart
  rw [dif_pos hj]
  change ((regular D (Range.build D w) p j).1 &&
    (fixedStart (build A B C K D E w fallback g0 g h0g hg) p ⟨j,_⟩ right).1)=true ↔ _
  rw [Bool.and_eq_true,regular_correct D w p j hpj (by omega),
    fixedStart_correct A B C K D E w fallback g0 g h0g hg p right h0p (by omega) hr ⟨j,_⟩ hpj hjr]

theorem startsAt_correct (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ))
    (fallback : Fin σ) (g0 g : Nat) (h0g : g0≤g) (hg : g≤w.length)
    (left right p : Nat) (h0l : g0≤left) (hlp : left≤p) (hpg : p≤g) (hr : right≤w.length) :
    (startsAt (build A B C K D E w fallback g0 g h0g hg) left right p).1=true ↔
      K.accepts (slice w left p) ∧ ∃j,p≤j ∧ j<g ∧ j≤right ∧ D.accepts (slice w p j) ∧
        ∃a,a≤g0 ∧ Copy A B E w a j right ∧ C.accepts (slice w a p) := by
  change ((regular K (Range.build K w) left p).1 &&
    (scan (atStart (build A B C K D E w fallback g0 g h0g hg) right p) p (min g (right+1)-p)).1)=true ↔ _
  rw [Bool.and_eq_true,regular_correct K w left p hlp (by omega),scan_correct]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨j,hpj,hj,h⟩
    have hjg : j<g := by omega
    have hjr : j≤right := by omega
    exact ⟨j,hpj,hjg,hjr,(atStart_correct A B C K D E w fallback g0 g h0g hg
      right p j (by omega) hpj (by omega) hjr hr).mp h⟩
  · rintro ⟨j,hpj,hjg,hjr,h⟩
    exact ⟨j,hpj,by omega,(atStart_correct A B C K D E w fallback g0 g h0g hg
      right p j (by omega) hpj (by omega) hjr hr).mpr h⟩

theorem querySeparated_correct (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ))
    (fallback : Fin σ) (g0 g : Nat) (h0g : g0≤g) (hg : g≤w.length)
    (left right : Nat) (h0l : g0≤left) (hlg : left≤g) (hr : right≤w.length) :
    (querySeparated (build A B C K D E w fallback g0 g h0g hg) left right).1=true ↔
      Case A B C K D E w left right g0 g .nearSeparated := by
  change (scan _ left (g-left)).1=true ↔ _
  rw [scan_correct]
  constructor
  · rintro ⟨p,hlp,hp,h⟩
    have hpg : p<g := by omega
    obtain ⟨hK,a,j,ha,hgj,hcopy,hC,hD⟩:=(atSeparated_correct A B C K D E w fallback g0 g h0g hg
      left right p h0l hlp (by omega) hr).mp h
    exact ⟨a,p,j,⟨by omega,by omega,hlp,hC,hK,hD,hcopy⟩,hpg,ha,hgj⟩
  · rintro ⟨a,p,j,⟨hap,hpj,hlp,hC,hK,hD,hcopy⟩,hpg,ha,hgj⟩
    refine ⟨p,hlp,by omega,?_⟩
    exact (atSeparated_correct A B C K D E w fallback g0 g h0g hg
      left right p h0l hlp (by omega) hr).mpr ⟨hK,a,j,ha,hgj,hcopy,hC,hD⟩

theorem queryEnd_correct (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ))
    (fallback : Fin σ) (g0 g : Nat) (h0g : g0≤g) (hg : g≤w.length)
    (left right : Nat) (h0l : g0≤left) (hlg : left≤g) (hr : right≤w.length) :
    (queryEnd (build A B C K D E w fallback g0 g h0g hg) left right).1=true ↔
      Case A B C K D E w left right g0 g .nearEnd := by
  change (scan _ left (g-left)).1=true ↔ _
  rw [scan_correct]
  constructor
  · rintro ⟨p,hlp,hp,h⟩
    have hpg : p<g := by omega
    obtain ⟨hK,a,ha,hap,hC,j,hgj,hcopy,hD⟩:=(endsAt_correct A B C K D E w fallback g0 g h0g hg
      left right p h0l hlp (by omega) hr).mp h
    exact ⟨a,p,j,⟨hap,by omega,hlp,hC,hK,hD,hcopy⟩,hpg,ha,hgj⟩
  · rintro ⟨a,p,j,⟨hap,hpj,hlp,hC,hK,hD,hcopy⟩,hpg,ha,hgj⟩
    refine ⟨p,hlp,by omega,?_⟩
    exact (endsAt_correct A B C K D E w fallback g0 g h0g hg
      left right p h0l hlp (by omega) hr).mpr ⟨hK,a,ha,hap,hC,j,hgj,hcopy,hD⟩

theorem queryStart_correct (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ))
    (fallback : Fin σ) (g0 g : Nat) (h0g : g0≤g) (hg : g≤w.length)
    (left right : Nat) (h0l : g0≤left) (hlg : left≤g) (hr : right≤w.length) :
    (queryStart (build A B C K D E w fallback g0 g h0g hg) left right).1=true ↔
      Case A B C K D E w left right g0 g .nearStart := by
  change (scan _ left (g-left)).1=true ↔ _
  rw [scan_correct]
  constructor
  · rintro ⟨p,hlp,hp,h⟩
    have hpg : p<g := by omega
    obtain ⟨hK,j,hpj,hjg,hjr,hD,a,ha,hcopy,hC⟩:=(startsAt_correct A B C K D E w fallback g0 g h0g hg
      left right p h0l hlp (by omega) hr).mp h
    exact ⟨a,p,j,⟨by omega,hpj,hlp,hC,hK,hD,hcopy⟩,hpg,ha,hjg⟩
  · rintro ⟨a,p,j,⟨hap,hpj,hlp,hC,hK,hD,hcopy⟩,hpg,ha,hjg⟩
    have hjr:=copy_target_bound A B E w a j right hcopy
    refine ⟨p,hlp,by omega,?_⟩
    exact (startsAt_correct A B C K D E w fallback g0 g h0g hg
      left right p h0l hlp (by omega) hr).mpr ⟨hK,j,hpj,hjg,hjr,hD,a,ha,hcopy,hC⟩

theorem queryThree_correct (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ))
    (fallback : Fin σ) (g0 g : Nat) (h0g : g0≤g) (hg : g≤w.length)
    (left right : Nat) (h0l : g0≤left) (hlg : left≤g) (hr : right≤w.length) :
    (queryThree (build A B C K D E w fallback g0 g h0g hg) left right).1=true ↔
      Case A B C K D E w left right g0 g .nearSeparated ∨
      Case A B C K D E w left right g0 g .nearEnd ∨
      Case A B C K D E w left right g0 g .nearStart := by
  simp only [queryThree,Bool.or_eq_true,querySeparated_correct A B C K D E w fallback g0 g h0g hg left right h0l hlg hr,
    queryEnd_correct A B C K D E w fallback g0 g h0g hg left right h0l hlg hr,
    queryStart_correct A B C K D E w fallback g0 g h0g hg left right h0l hlg hr,or_assoc]

end REWB.BoundaryRange.NearIndex
