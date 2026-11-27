import REWB.ShortOuterReady

/-! Original-coordinate meaning of the materialized F-ready rows.
All existential endpoint searches below occur only in erased proofs. -/
namespace REWB.ShortOuter.Ready
open REWB.Periodic
open REWB.Spec (slice)
variable {α : Type} {σ : Nat}

theorem slice_segment (f : Nat→α) (p width a b : Nat)
    (hab : a≤b) (hb : b≤width) :
    slice (segment f p width) a b=segment f (p+a) (b-a) := by
  rw [slice,SmallPeriodP2.segment_drop f p width a (by omega),
    SmallPeriodP2.segment_take f (p+a) (width-a) (b-a) (by omega)]

theorem slice_segment_read (text : Array (Fin σ)) (fallback : Fin σ)
    (p width a b : Nat) (hab : a≤b) (hb : b≤width) (hpn : p+b≤text.size) :
    slice (segment (ArrayText.read text fallback) p width) a b=
      slice text.toList (p+a) (p+b) := by
  rw [slice_segment _ p width a b hab hb,
    ArrayText.segment_read text fallback (p+a) (b-a) (by omega)]
  simp only [slice]
  congr 1
  omega

theorem get_iff (F G H : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (limit p off : Nat) (hp : p≤text.size) :
    get (build F text fallback (Band.build G H text fallback limit)) p off=true ↔
      ∃len,off≤len ∧ len<limit ∧ p+len≤text.size ∧
        F.accepts (slice text.toList (p+off) (p+len)) ∧
        Band.get (Band.build G H text fallback limit) p len=true := by
  rw [get_row F text fallback _ p off hp]
  simp only [row]
  rw [OneUseRange.FarAggregate.query_correct]
  simp only [List.size_toArray,segment_length,List.toList_toArray]
  constructor
  · rintro ⟨len,ho,hw,hm,hF⟩
    rw [mask_get _ p len hw] at hm
    obtain ⟨hl,hn,_⟩:= (Band.get_iff G H text fallback limit p len).mp hm
    exact ⟨len,ho,hl,hn,by
      rwa [slice_segment_read text fallback p _ off len ho hw hn] at hF,hm⟩
  · rintro ⟨len,ho,hl,hn,hF,hm⟩
    have hw : len≤(Band.build G H text fallback limit).keys.width := by
      simp only [Band.build_keys,Keys.build_width]
      omega
    refine ⟨len,ho,hw,?_,?_⟩
    · rw [mask_get _ p len hw]
      exact hm
    · rwa [slice_segment_read text fallback p _ off len ho hw hn]

theorem get_expanded (F G H : DFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (limit p off : Nat) (hp : p≤text.size) :
    get (build F text fallback (Band.build G H text fallback limit)) p off=true ↔
      ∃len,off≤len ∧ len<limit ∧ p+len≤text.size ∧
        F.accepts (slice text.toList (p+off) (p+len)) ∧
        ∃k,p+len≤k ∧ k+len≤text.size ∧
          slice text.toList p (p+len)=slice text.toList k (k+len) ∧
          G.accepts (slice text.toList (p+len) k) ∧
          H.accepts (slice text.toList (k+len) text.size) := by
  rw [get_iff F G H text fallback limit p off hp]
  constructor
  · rintro ⟨len,ho,hl,hn,hF,hm⟩
    exact ⟨len,ho,hl,hn,hF,(Band.get_iff G H text fallback limit p len).mp hm |>.2.2⟩
  · rintro ⟨len,ho,hl,hn,hF,hk⟩
    exact ⟨len,ho,hl,hn,hF,(Band.get_iff G H text fallback limit p len).mpr ⟨hl,hn,hk⟩⟩

end REWB.ShortOuter.Ready
