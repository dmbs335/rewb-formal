import REWB.ShortOuterPrepared

/-! Erased coordinate bridges for the concrete short-outer tables. -/
namespace REWB.ShortOuter
open REWB.Periodic REWB.P2Periodic
variable {α : Type} {σ : Nat}

theorem full_read (text : Array α) (fallback : α) :
    segment (ArrayText.read text fallback) 0 text.size=text.toList := by
  rw [ArrayText.segment_read text fallback 0 text.size (by omega)]
  simp

theorem factor_read (text : Array α) (fallback : α) (a b : Nat)
    (hab : a≤b) (hb : b≤text.size) :
    factor (ArrayText.read text fallback) a b=Spec.slice text.toList a b :=
  ArrayText.segment_read text fallback a (b-a) (by omega)

theorem prepare_b_correct (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (limit p len : Nat) (hp : p≤text.size) (hl : len≤min limit (text.size+1)) :
    Regular.accepts P.B (prepare P text fallback limit).b p len=true ↔
      P.B.accepts (segment (ArrayText.read text fallback) p len) := by
  simp only [prepare,Regular.accepts,Band.build_keys,Keys.build_width,
    Regular.state_correct P.B text fallback _ p len hp hl,DFA.accepts]

theorem prepare_c_correct (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (limit p len : Nat) (hp : p≤text.size) (hl : len≤min limit (text.size+1)) :
    Regular.accepts P.C (prepare P text fallback limit).c p len=true ↔
      P.C.accepts (segment (ArrayText.read text fallback) p len) := by
  simp only [prepare,Regular.accepts,Band.build_keys,Keys.build_width,
    Regular.state_correct P.C text fallback _ p len hp hl,DFA.accepts]

theorem prepare_d_correct (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (limit p len : Nat) (hp : p≤text.size) (hl : len≤min limit (text.size+1)) :
    Regular.accepts P.D (prepare P text fallback limit).d p len=true ↔
      P.D.accepts (segment (ArrayText.read text fallback) p len) := by
  simp only [prepare,Regular.accepts,Band.build_keys,Keys.build_width,
    Regular.state_correct P.D text fallback _ p len hp hl,DFA.accepts]

theorem prepare_ready_correct (P : SevenDFA (Fin σ)) (text : Array (Fin σ)) (fallback : Fin σ)
    (limit p off : Nat) (hp : p≤text.size) :
    Ready.get (prepare P text fallback limit).ready p off=true ↔
      ∃len,off≤len ∧ len<limit ∧ p+len≤text.size ∧
        P.F.accepts (factor (ArrayText.read text fallback) (p+off) (p+len)) ∧
        ∃k,p+len≤k ∧ k+len≤text.size ∧
          factor (ArrayText.read text fallback) p (p+len)=
            factor (ArrayText.read text fallback) k (k+len) ∧
          P.G.accepts (factor (ArrayText.read text fallback) (p+len) k) ∧
          P.H.accepts (factor (ArrayText.read text fallback) (k+len) text.size) := by
  change Ready.get (Ready.build P.F text fallback (Band.build P.G P.H text fallback limit)) p off=true ↔ _
  rw [Ready.get_expanded P.F P.G P.H text fallback limit p off hp]
  constructor
  · rintro ⟨len,ho,hl,hn,hF,k,hpk,hkn,he,hG,hH⟩
    refine ⟨len,ho,hl,hn,?_,k,hpk,hkn,?_,?_,?_⟩
    · rwa [factor_read text fallback (p+off) (p+len) (by omega) hn]
    · rwa [factor_read text fallback p (p+len) (by omega) hn,
        factor_read text fallback k (k+len) (by omega) hkn]
    · rwa [factor_read text fallback (p+len) k hpk (by omega)]
    · rwa [factor_read text fallback (k+len) text.size hkn (Nat.le_refl _)]
  · rintro ⟨len,ho,hl,hn,hF,k,hpk,hkn,he,hG,hH⟩
    refine ⟨len,ho,hl,hn,?_,k,hpk,hkn,?_,?_,?_⟩
    · rwa [factor_read text fallback (p+off) (p+len) (by omega) hn] at hF
    · rwa [factor_read text fallback p (p+len) (by omega) hn,
        factor_read text fallback k (k+len) (by omega) hkn] at he
    · rwa [factor_read text fallback (p+len) k hpk (by omega)] at hG
    · rwa [factor_read text fallback (k+len) text.size hkn (Nat.le_refl _)] at hH

end REWB.ShortOuter
