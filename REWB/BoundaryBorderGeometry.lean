import REWB.MaskedLocalAnchor

/-! Period-break geometry for suffix/prefix overlap queries.  A candidate
    first copy ends at a fixed boundary a and the second begins at j.
    Within one periodic source component, candidates ending before its
    right period break form a clipped progression.  If a lies beyond that
    break, equality forces a unique source start.  These facts do not
    assume a supplied overlap-length list or enumerate candidate lengths.
-/
namespace REWB.BoundaryBorder
open Periodic RunGeometry LCEIndex
variable {α : Type} {σ : Nat}

/-- The longest q-periodic prefix at a bounded text position. -/
structure PeriodPrefix (f : Nat→α) (n start q extent : Nat) : Prop where
  bounded : start+extent≤n
  periodic : Period (shift f start) extent q
  longest : ∀size,start+size≤n→Period (shift f start) size q→size≤extent

theorem periodPrefix_of_lce (f : Nat→α) (n start q common : Nat)
    (h : IsLCE f n start (start+q) common) :
    PeriodPrefix f n start q (q+common) := by
  refine ⟨by have hb:=h.1.2.1; omega,?_,?_⟩
  · intro i hi
    have he:=(segment_eq_points f start (start+q) common).mp h.1.2.2 i (by omega)
    simpa only [shift,Nat.add_assoc,Nat.add_comm q i] using he
  · intro size hb hp
    by_cases hs : size≤q
    · omega
    · have ha : Agree f n start (start+q) (size-q) := by
        refine ⟨by omega,by omega,(segment_eq_points f start (start+q) (size-q)).mpr ?_⟩
        intro i hi
        have he:=hp i (by omega)
        simpa only [shift,Nat.add_assoc,Nat.add_comm i q] using he
      have hh:=h.2 _ ha
      omega

structure Extended where
  extent : Nat
  work : Nat

def extend (idx : RankIndex.Index) (n start q : Nat) : Extended :=
  let out:=lceMeasured idx n start (start+q)
  ⟨q+out.length,out.countedWork+3⟩

theorem extend_correct (f : Nat→Fin σ) (n start q : Nat) (hb : start+q≤n) :
    PeriodPrefix f n start q (extend (prepare f n) n start q).extent :=
  periodPrefix_of_lce f n start q _ (lceMeasured_correct f n start (start+q) (by omega) hb)

theorem extend_work (idx : RankIndex.Index) (n start q : Nat) :
    (extend idx n start q).work≤13*(n.log2+1)+4 := by
  have hh:=lceMeasured_work idx n start (start+q)
  change (lceMeasured idx n start (start+q)).countedWork+3≤_
  omega

theorem prefix_failure (f : Nat→α) (n start q extent : Nat)
    (hp : PeriodPrefix f n start q extent) (hq : 0<q) (he : q≤extent)
    (hb : start+extent<n) : f (start+extent-q)≠f (start+extent) := by
  intro heq
  have ho : OnPeriod f start (start+extent) q := by
    apply (on_iff f start (start+extent) q).mpr
    simpa only [Nat.add_sub_cancel_left] using hp.periodic
  have hx:=on_extend_right f start (start+extent) q ho hq (by omega) heq
  have hh:=(on_iff f start (start+extent+1) q).mp hx
  rw [show start+extent+1-start=extent+1 by omega] at hh
  have hc:=hp.longest (extent+1) (by omega) hh
  omega

/-- Every sufficiently early start in the same right-maximal periodic
    interval has the same absolute first period break. -/
theorem prefix_from_interval (f : Nat→α) (n left right p q : Nat)
    (hper : OnPeriod f left right q) (hp : left≤p) (hq : 0<q)
    (hpr : p+q≤right) (hr : right≤n)
    (hstop : right=n ∨ f (right-q)≠f right) :
    PeriodPrefix f n p q (right-p) := by
  refine ⟨by omega,?_,?_⟩
  · exact (on_iff f p right q).mp (on_restrict f left right q p right hper hp (Nat.le_refl _))
  · intro size hsize hperiod
    by_cases hs : size≤right-p
    · exact hs
    · exfalso
      rcases hstop with he | hn
      · omega
      · apply hn
        have heq:=hperiod (right-p-q) (by omega)
        change f (p+(right-p-q))=f (p+(right-p-q+q)) at heq
        simpa only [show p+(right-p-q)=right-q by omega,
          show p+(right-p-q+q)=right by omega] using heq

theorem prefix_move (f : Nat→α) (n start q extent p : Nat)
    (hp : PeriodPrefix f n start q extent) (hq : 0<q)
    (hsp : start≤p) (hpr : p+q≤start+extent) :
    PeriodPrefix f n p q (start+extent-p) := by
  have hper : OnPeriod f start (start+extent) q := by
    apply (on_iff f start (start+extent) q).mpr
    simpa only [Nat.add_sub_cancel_left] using hp.periodic
  apply prefix_from_interval f n start (start+extent) p q hper hsp hq hpr hp.bounded
  by_cases he : start+extent=n
  · exact Or.inl he
  · exact Or.inr (prefix_failure f n start q extent hp hq (by omega) (by have hb:=hp.bounded; omega))

theorem copy_period (f : Nat→α) (p j length size q : Nat)
    (heq : segment f p length=segment f j length) (hs : size≤length)
    (hp : Period (shift f p) size q) : Period (shift f j) size q := by
  apply MaskedLocalAnchor.period_copy f p j size q ?_ hp
  apply (segment_eq_points f p j size).mpr
  intro i hi
  exact (segment_eq_points f p j length).mp heq i (by omega)

/-- Equal copies that include the first failed period comparison must
    have that failure at the same relative offset. -/
theorem copy_past_break (f : Nat→α) (n p j q sourceExtent targetExtent length : Nat)
    (hs : PeriodPrefix f n p q sourceExtent)
    (ht : PeriodPrefix f n j q targetExtent)
    (heq : Agree f n p j length) (hb : sourceExtent<length) :
    targetExtent=sourceExtent := by
  have hst : sourceExtent≤targetExtent := ht.longest sourceExtent
    (by have hh:=heq.2.1; omega)
    (copy_period f p j length sourceExtent q heq.2.2 (by omega) hs.periodic)
  apply Nat.le_antisymm ?_ hst
  by_cases hle : targetExtent≤sourceExtent
  · exact hle
  · have hp:=copy_period f j p length (sourceExtent+1) q heq.2.2.symm (by omega)
      (restrict ht.periodic (by omega))
    have hh:=hs.longest (sourceExtent+1) (by have hh:=heq.1; omega) hp
    omega

theorem outside_unique_candidate (f : Nat→α) (n left right p j q targetExtent a : Nat)
    (hper : OnPeriod f left right q) (hp : left≤p) (hq : 0<q)
    (hpr : p+q≤right) (hr : right≤n)
    (hstop : right=n ∨ f (right-q)≠f right)
    (ht : PeriodPrefix f n j q targetExtent) (ha : right<a)
    (heq : Agree f n p j (a-p)) : p=right-targetExtent := by
  have hs:=prefix_from_interval f n left right p q hper hp hq hpr hr hstop
  have he:=copy_past_break f n p j q (right-p) targetExtent (a-p) hs ht heq (by omega)
  omega

/-- Before the first source break, the only extra equality constraint is
    that the target's periodic prefix is long enough.  A cluster supplies
    equality of the initial q letters; no inverse transition is involved. -/
theorem inside_iff (f : Nat→α) (n p j q targetExtent length : Nat)
    (hq : 0<q) (hp : p+length≤n)
    (hper : Period (shift f p) length q)
    (hseed : segment f p q=segment f j q)
    (ht : PeriodPrefix f n j q targetExtent) :
    Agree f n p j length ↔ length≤targetExtent := by
  constructor
  · intro heq
    exact ht.longest length heq.2.1
      (copy_period f p j length length q heq.2.2 (Nat.le_refl _) hper)
  · intro hl
    refine ⟨hp,by have hb:=ht.bounded; omega,(segment_eq_points f p j length).mpr ?_⟩
    intro i hi
    have htper:=restrict ht.periodic hl
    have hs:=period_residue hper i hi
    have he:=period_residue htper i hi
    have hm:=(segment_eq_points f p j q).mp hseed (i%q) (Nat.mod_lt i hq)
    exact hs.trans (hm.trans he.symm)

theorem prefix_unique (f : Nat→α) (n p q a b : Nat)
    (ha : PeriodPrefix f n p q a) (hb : PeriodPrefix f n p q b) : a=b :=
  Nat.le_antisymm (hb.longest a ha.bounded ha.periodic) (ha.longest b hb.bounded hb.periodic)

theorem lce_agree_iff (f : Nat→α) (n p j common length : Nat)
    (h : IsLCE f n p j common) : Agree f n p j length ↔ length≤common :=
  ⟨h.2 length,agree_shorten f n p j common length h.1⟩

end REWB.BoundaryBorder
