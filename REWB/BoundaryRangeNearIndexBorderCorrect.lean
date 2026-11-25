import REWB.BoundaryRangeNearIndexBorder

/-! Exact same-block border semantics. The AP certificate is obtained
from the actual suffix index by Regular.dyadic_correct. The gap chooses
one common split for C/K/D. Both are conjoined at the same (a,j). -/
namespace REWB.BoundaryRange.NearIndex.Border
open REWB.BoundaryApplication
open REWB.Spec (slice)
variable {σ : Nat}

theorem gap_correct (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (left a j : Nat) (haj : a≤j) (hlj : left≤j) (hj : j≤w.length) :
    (gap (build A B C K D E w fallback) left a j).1=true ↔
      (Automata.gap C K D
        ((Range.query C (Range.build C w) a (max a left)).map.get C.initial)
        ((Range.query K (Range.build K w) left (max a left)).map.get K.initial)).accepts
          (slice w (max a left) j) := by
  have hC : (build A B C K D E w fallback).cranges=Range.build C w := rfl
  have hK : (build A B C K D E w fallback).kranges=Range.build K w := rfl
  simp only [gap,hC,hK,build_gap]
  simp only [GapCell.query,buildGap]
  exact NearIndex.regular_correct (Automata.gap C K D
    ((Range.query C (Range.build C w) a (max a left)).map.get C.initial)
    ((Range.query K (Range.build K w) left (max a left)).map.get K.initial))
    w (max a left) j (by omega) hj

theorem gap_iff_split (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (left a j : Nat) (haj : a≤j) (hlj : left≤j) (hj : j≤w.length) :
    (gap (build A B C K D E w fallback) left a j).1=true ↔
      ∃p,a≤p ∧ left≤p ∧ p≤j ∧ C.accepts (slice w a p) ∧
        K.accepts (slice w left p) ∧ D.accepts (slice w p j) := by
  rw [gap_correct A B C K D E w fallback left a j haj hlj hj]
  exact split_gap C K D w left a j haj hlj hj

theorem copy_correct (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (a : Nat) (j : Fin (w.toArray.size+1)) (right : Nat)
    (ha : a≤w.length) (hjr : j.val≤right) (hr : right≤w.length) :
    (copy (build A B C K D E w fallback) a j right).1=true ↔ Copy A B E w a j.val right := by
  change ((BoundaryBorder.Regular.dyadic A B E (BoundaryBorder.WindowIndex.prepare w.toArray fallback)
    (Range.build A w) (Range.build B w) (Range.build E w) a j right).1 ||
    ((NearIndex.regular A (Range.build A w) 0 a).1 && B.final B.initial &&
      (NearIndex.regular E (Range.build E w) j.val right).1))=true ↔ _
  rw [Bool.or_eq_true,Bool.and_eq_true,Bool.and_eq_true,
    BoundaryBorder.Regular.dyadic_correct A B E w fallback a j right ha hr,
    NearIndex.regular_correct A w 0 a (Nat.zero_le _) ha,
    NearIndex.regular_correct E w j.val right hjr hr]
  constructor
  · rintro (⟨p,hpa,hend,he,hA,hB,hE⟩|⟨⟨hA,hB⟩,hE⟩)
    · have hp : a-(a-p)=p := by omega
      refine ⟨a-p,by omega,hend,?_,?_,?_,hE⟩
      · simpa only [hp,BoundaryBorder.Regular.endAt] using he
      · simpa only [hp] using hA
      · simpa only [hp] using hB
    · refine ⟨0,by omega,by omega,?_,?_,?_,?_⟩
      · simp only [Nat.sub_zero,Nat.add_zero,OuterColumn.slice_self]
      · simpa only [Nat.sub_zero] using hA
      · simpa only [Nat.sub_zero,OuterColumn.slice_self,DFA.accepts,DFA.run] using hB
      · simpa only [Nat.add_zero] using hE
  · rintro ⟨L,hLa,hLr,he,hA,hB,hE⟩
    by_cases hL : L=0
    · subst L
      right
      simp only [Nat.sub_zero,Nat.add_zero,OuterColumn.slice_self] at hA hB hE
      exact ⟨⟨hA,hB⟩,hE⟩
    · left
      have hlen : a-(a-L)=L := by omega
      refine ⟨a-L,by omega,?_,?_,hA,hB,?_⟩
      · simpa only [BoundaryBorder.Regular.endAt,hlen] using hLr
      · simpa only [BoundaryBorder.Regular.endAt,hlen] using he
      · simpa only [BoundaryBorder.Regular.endAt,hlen] using hE

theorem queryAt_correct (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (left right a j : Nat) (haj : a≤j) (hlj : left≤j) (hjr : j≤right) (hr : right≤w.length) :
    (queryAt (build A B C K D E w fallback) left right a j).1=true ↔
      Copy A B E w a j right ∧
      (Automata.gap C K D
        ((Range.query C (Range.build C w) a (max a left)).map.get C.initial)
        ((Range.query K (Range.build K w) left (max a left)).map.get K.initial)).accepts
          (slice w (max a left) j) := by
  have hj : j≤(build A B C K D E w fallback).length := by change j≤w.length; omega
  unfold queryAt
  rw [dif_pos hj]
  simp only [Bool.and_eq_true]
  rw [copy_correct A B C K D E w fallback a ⟨j,_⟩ right (by omega) hjr hr,
    gap_correct A B C K D E w fallback left a j haj hlj (by omega)]

theorem row_correct (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (left right g a : Nat) (_hg : g≤w.length) (hr : right≤w.length) :
    (row (build A B C K D E w fallback) left right g a).1=true ↔
      ∃j,a≤j ∧ left≤j ∧ j<g ∧ j≤right ∧ Copy A B E w a j right ∧
      (Automata.gap C K D
        ((Range.query C (Range.build C w) a (max a left)).map.get C.initial)
        ((Range.query K (Range.build K w) left (max a left)).map.get K.initial)).accepts
          (slice w (max a left) j) := by
  unfold row
  rw [NearIndex.scan_correct]
  constructor
  · rintro ⟨j,hj,he,h⟩
    have haj : a≤j := by omega
    have hlj : left≤j := by omega
    have hjr : j≤right := by omega
    exact ⟨j,haj,hlj,by omega,hjr,
      (queryAt_correct A B C K D E w fallback left right a j haj hlj hjr hr).mp h⟩
  · rintro ⟨j,haj,hlj,hjg,hjr,h⟩
    exact ⟨j,by omega,by omega,
      (queryAt_correct A B C K D E w fallback left right a j haj hlj hjr hr).mpr h⟩

theorem query_correct (A B C K D E : DFA (Fin σ)) (w : Word (Fin σ)) (fallback : Fin σ)
    (left right g0 g : Nat) (hg : g≤w.length) (hr : right≤w.length) :
    (query (build A B C K D E w fallback) left right g0 g).1=true ↔
      Case A B C K D E w left right g0 g .nearBorder := by
  unfold query
  rw [NearIndex.scan_correct,nearBorder_step A B C K D E w left right g0 g hr]
  constructor
  · rintro ⟨a,ha,he,h⟩
    obtain ⟨j,haj,hlj,hjg,hjr,hcopy,hgap⟩:=(row_correct A B C K D E w fallback left right g a hg hr).mp h
    exact ⟨a,j,by omega,haj,hlj,hjg,hjr,hcopy,hgap⟩
  · rintro ⟨a,j,ha,haj,hlj,hjg,hjr,hcopy,hgap⟩
    exact ⟨a,by omega,by omega,
      (row_correct A B C K D E w fallback left right g a hg hr).mpr ⟨j,haj,hlj,hjg,hjr,hcopy,hgap⟩⟩

end REWB.BoundaryRange.NearIndex.Border
