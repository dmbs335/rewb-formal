import REWB.GlobalSemanticCoverage
import REWB.RankIndexSchedule

/-! Global residual coverage by actual sampled strips and duplicate-free
run schedules. The subsequent matching queries for the residual cases
are still separate operations. -/
namespace REWB.IndexedGlobalCoverage
open REWB.Periodic REWB.RunGeometry REWB.GlobalCoverage
variable {α : Type} {σ : Nat}

theorem strip_unique (f : Nat→α) (n l r a b d i : Nat)
    (hs : MaximalStrip f n l r d) (ht : MaximalStrip f n a b d)
    (hli : l≤i) (hir : i<r) (hai : a≤i) (hib : i<b) : l=a ∧ r=b := by
  obtain ⟨hd,hlr,hrn,hS,hSl,hSr⟩ := hs
  obtain ⟨_,hab,hbn,hT,hTl,hTr⟩ := ht
  have hl : l=a := by
    by_cases hla : l<a
    · rcases hTl with hz|hm
      · omega
      · exact False.elim (hm (hS (a-1) (by omega) (by omega)))
    · by_cases hal : a<l
      · rcases hSl with hz|hm
        · omega
        · exact False.elim (hm (hT (l-1) (by omega) (by omega)))
      · omega
  refine ⟨hl,?_⟩
  by_cases hrb : r<b
  · rcases hSr with hz|hm
    · omega
    · exact False.elim (hm (hT r (by omega) hrb))
  · by_cases hbr : b<r
    · rcases hTr with hz|hm
      · omega
      · exact False.elim (hm (hS b (by omega) hbr))
    · omega

theorem strip_complete (f : Nat→Fin σ) (n s p e k l r : Nat)
    (hc : Copy f n p e k) (hs : 0<s) (hlen : s≤e-p)
    (ht : MaximalStrip f n l r (k-p)) (hl : l≤p) (hr : e≤r) :
    (⟨l,r,k-p⟩ : IndexedGrid.Strip)∈(IndexedGrid.generate f n s).strips := by
  obtain ⟨S,hm,hlo,hhi,hd⟩ := IndexedGrid.generate_complete f n s p e k hs hc hlen
  have hS:=IndexedGrid.generate_sound f n s S hm
  rw [hd] at hS
  obtain ⟨h1,h2⟩ := strip_unique f n l r S.lo S.hi (k-p) p ht hS
    hl (by have hh:=hc.positive; omega) hlo (by have hh:=hc.positive; omega)
  have he : S=(⟨l,r,k-p⟩ : IndexedGrid.Strip) := by
    cases S
    simp_all only [IndexedGrid.Strip.mk.injEq]
  rwa [he] at hm

theorem largePair_period_le (R : Bounds) (p d : Nat) (hm : (p,d)∈largePairs R) :
    R.period≤d := by
  obtain ⟨j,hj,hmem⟩ := List.mem_flatMap.mp hm
  obtain ⟨i,hi,he⟩ := List.mem_map.mp hmem
  have hd : (j+1)*R.period=d := congrArg Prod.snd he
  have hle:=Nat.mul_le_mul_right R.period (by omega : 1≤j+1)
  simpa only [Nat.one_mul,hd] using hle

inductive Residual (f : Nat→Fin σ) (n s L D Q p e k : Nat) : Prop
  | short (h : e-p<L) : Residual f n s L D Q p e k
  | separated (l r : Nat)
      (member : (⟨l,r,k-p⟩ : IndexedGrid.Strip)∈(IndexedGrid.generate f n s).strips)
      (left : l≤p) (right : e≤r) (disjoint : r-l≤k-p) :
      Residual f n s L D Q p e k
  | longGap (l r a : Nat)
      (member : (⟨l,r,k-p⟩ : IndexedGrid.Strip)∈(IndexedGrid.generate f n s).strips)
      (left : l≤p) (right : e≤r) (cutLeft : e≤a*D) (cutRight : a*D≤k)
      (containsLeft : max l (a*D-(k-p))≤p)
      (containsRight : e≤min r (a*D))
      (separates : min r (a*D)≤max l (a*D-(k-p))+(k-p)) :
      Residual f n s L D Q p e k
  | low (R : Bounds) (member : (R,p)∈RankIndexSchedule.low f n s D)
      (left : R.lo≤p) (right : e+(k-p)≤R.hi)
      (displacement : R.period=k-p) (exponent : R.hi-R.lo<3*R.period) :
      Residual f n s L D Q p e k
  | large (R : Bounds) (member : (R,(p,k-p))∈RankIndexSchedule.large f n s Q)
      (left : R.lo≤p) (right : e+(k-p)≤R.hi) : Residual f n s L D Q p e k

theorem realize (f : Nat→Fin σ) (n s L D Q p e k : Nat)
    (hc : Copy f n p e k) (hs : 0<s) (hSL : s≤L)
    (h : GlobalCoverageP2.Residual f n L D Q p e k) : Residual f n s L D Q p e k := by
  by_cases hshort : e-p<L
  · exact .short hshort
  have hlong : s≤e-p := by omega
  cases h with
  | short h => exact .short h
  | separated l r h hl hr hd =>
    exact .separated l r (strip_complete f n s p e k l r hc hs hlong h hl hr) hl hr hd
  | longGap l r a h hl hr hcl hcr h1 h2 h3 =>
    exact .longGap l r a (strip_complete f n s p e k l r hc hs hlong h hl hr)
      hl hr hcl hcr h1 h2 h3
  | low R hv hl hr hd he hp =>
    exact .low R (RankIndexSchedule.low_complete f n s D p e (k-p) R hv hs hlong hl hr hd hp)
      hl hr hd he
  | large R hv hl hr hc hQ hp =>
    exact .large R (RankIndexSchedule.large_complete f n s Q p e (k-p) R hv hs hlong hl hr
      (largePair_period_le R p (k-p) hp) hc hQ hp) hl hr

theorem p2_cover (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n s L D Q : Nat)
    (hm : MatchesWithin P.nested2 (segment f 0 n) 2)
    (hs : 0<s) (hSL : s≤L) (hD : 0<D) (hQL : Q≤L) :
    (∃ x,P2Periodic.Witness P f n [] [] x ∧ Residual f n s L D Q x.p x.e x.k) ∨
    (SmallPeriodP2.solve P f n Q).accepted=true := by
  rcases GlobalSemanticCoverage.p2_cover P f n L D Q hm (by omega) hD hQL with
    ⟨x,hx,hr⟩|ha
  · refine Or.inl ⟨x,hx,?_⟩
    by_cases hshort : x.e-x.p<L
    · exact .short hshort
    · have hp : x.p<x.e := by omega
      exact realize f n s L D Q x.p x.e x.k (GlobalCoverageP2.outer_copy P f n x hx hp) hs hSL hr
  · exact Or.inr ha

theorem p1_cover (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n s L D Q : Nat)
    (hm : MatchesWithin P.nested1 (segment f 0 n) 2)
    (hs : 0<s) (hSL : s≤L) (hD : 0<D) (hQL : Q≤L) :
    (∃ w : GlobalCoverageP1.Witness P f n,
      Residual f n s L D Q w.outerStart w.target.e w.target.k) ∨
    (CountedP1Cubic.solve P f n Q).answer=true := by
  rcases GlobalSemanticCoverage.p1_cover P f n L D Q hm (by omega) hD hQL with ⟨w,hr⟩|ha
  · refine Or.inl ⟨w,?_⟩
    by_cases hshort : w.target.e-w.outerStart<L
    · exact .short hshort
    · have hp : w.outerStart<w.target.e := by omega
      exact realize f n s L D Q w.outerStart w.target.e w.target.k
        (GlobalCoverageP1.outer_copy P f n w hp) hs hSL hr
  · exact Or.inr ha

end REWB.IndexedGlobalCoverage
