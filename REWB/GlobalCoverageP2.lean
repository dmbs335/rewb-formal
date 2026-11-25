import REWB.GlobalCoverage
import REWB.SmallPeriodP2

/-! Connect absolute P2 witnesses to the global outer-copy geometry.
The small-period case is discharged by the actual cached P2 solver.
The other cases retain explicit geometric evidence for the still-needed
short/range-query algorithms; this module does not assign them costs. -/
namespace REWB.GlobalCoverageP2
open REWB.Periodic REWB.RunGeometry REWB.GlobalCoverage
open REWB.P2Periodic (factor)
variable {α : Type}

theorem factor_rebase (f : Nat→α) (l a b : Nat)
    (hla : l≤a) (hab : a≤b) :
    factor (shift f l) (a-l) (b-l)=factor f a b := by
  unfold factor
  rw [LongSourceCoverage.segment_shift,show l+(a-l)=a by omega,
    show b-l-(a-l)=b-a by omega]

theorem prefix_context (f : Nat→α) (n l p : Nat)
    (hlp : l≤p) (hpn : p≤n) :
    (segment f 0 n).take l++factor (shift f l) 0 (p-l)=factor f 0 p := by
  rw [SmallPeriodP2.segment_take f 0 n l (by omega)]
  unfold factor
  rw [LongSourceCoverage.segment_shift]
  simp only [Nat.add_zero,Nat.sub_zero]
  have he := segment_append f 0 l (p-l)
  simp only [Nat.zero_add] at he
  rw [show l+(p-l)=p by omega] at he
  exact he.symm

theorem suffix_context (f : Nat→α) (n l a r : Nat)
    (hla : l≤a) (har : a≤r) (hrn : r≤n) :
    factor (shift f l) (a-l) (r-l)++(segment f 0 n).drop r=factor f a n := by
  rw [factor_rebase f l a r hla har,
    SmallPeriodP2.segment_drop f 0 n r hrn]
  simp only [Nat.zero_add]
  unfold factor
  have he := segment_append f a (r-a) (n-r)
  rw [show a+(r-a)=r by omega,show (r-a)+(n-r)=n-a by omega] at he
  exact he.symm

/-- Rebase all eight real endpoints into a containing run, retaining
the exact global A prefix and H suffix through shared contexts. -/
theorem relative_witness (P : SevenDFA α) (f : Nat→α) (n l r : Nat)
    (x : P2Periodic.Layout Nat)
    (hw : P2Periodic.Witness P f n [] [] x)
    (hlp : l≤x.p) (hfr : x.f≤r) (hrn : r≤n) :
    P2Periodic.Witness P (shift f l) (r-l)
      ((segment f 0 n).take l) ((segment f 0 n).drop r)
      (x.map (fun a=>a-l)) := by
  rcases hw with ⟨hpi,hia,haj,hjt,hte,hek,hkf,hfn,hA,hB,hC,hD,hF,hG,hH,hu,hv⟩
  simp only [List.nil_append] at hA
  simp only [List.append_nil] at hH
  simp only [P2Periodic.Witness,P2Periodic.Layout.map]
  refine ⟨by omega,by omega,by omega,by omega,by omega,by omega,by omega,by omega,
    ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rwa [prefix_context f n l x.p hlp (by omega)]
  · rwa [factor_rebase f l x.p x.i hlp hpi]
  · rwa [factor_rebase f l x.i x.a (by omega) hia]
  · rwa [factor_rebase f l x.a x.j (by omega) haj]
  · rwa [factor_rebase f l x.t x.e (by omega) hte]
  · rwa [factor_rebase f l x.e x.k (by omega) hek]
  · rwa [suffix_context f n l x.f r (by omega) hfr hrn]
  · rwa [factor_rebase f l x.i x.a (by omega) hia,
      factor_rebase f l x.j x.t (by omega) hjt]
  · rwa [factor_rebase f l x.p x.e hlp (by omega),
      factor_rebase f l x.k x.f (by omega) hkf]

theorem outer_copy (P : SevenDFA α) (f : Nat→α) (n : Nat)
    (x : P2Periodic.Layout Nat)
    (hw : P2Periodic.Witness P f n [] [] x) (hpos : x.p<x.e) :
    Copy f n x.p x.e x.k := by
  rcases hw with ⟨hpi,hia,haj,hjt,hte,hek,hkf,hfn,hA,hB,hC,hD,hF,hG,hH,hu,hv⟩
  have hlen := congrArg List.length hv
  simp only [factor,segment_length] at hlen
  refine ⟨hpos,hek,by omega,?_⟩
  simpa only [factor,← hlen] using hv

/-- A containing small-period cubic run now needs no pre-rebased local
witness from the caller. All coordinates and boundary contexts are
derived from the original absolute witness. -/
theorem small_complete [DecidableEq α] (P : SevenDFA α) (f : Nat→α)
    (n Q : Nat) (x : P2Periodic.Layout Nat)
    (hw : P2Periodic.Witness P f n [] [] x)
    (R : Bounds) (hR : R.Valid f n) (hlp : R.lo≤x.p) (hfr : x.f≤R.hi)
    (hc : 3*R.period≤R.hi-R.lo) (hq : R.period≤Q)
    (hlong : R.period≤x.e-x.p) : (SmallPeriodP2.solve P f n Q).accepted=true := by
  apply SmallPeriodP2.solve_complete P f n Q R hR hq hc
    (x.map (fun a=>a-R.lo))
    (relative_witness P f n R.lo R.hi x hw hlp hfr hR.2.1)
  change R.period≤(x.e-R.lo)-(x.p-R.lo)
  omega

/-- The residual cases name the missing query branches explicitly.
Small-period acceptance is an executable result, not another witness
assumption. Empty outer captures are included in the short branch. -/
inductive Residual (f : Nat→α) (n L D Q p e k : Nat) : Prop
  | short (h : e-p<L) : Residual f n L D Q p e k
  | separated (l r : Nat) (h : MaximalStrip f n l r (k-p))
      (left : l≤p) (right : e≤r) (disjoint : r-l≤k-p) :
      Residual f n L D Q p e k
  | longGap (l r a : Nat) (h : MaximalStrip f n l r (k-p))
      (left : l≤p) (right : e≤r)
      (cutLeft : e≤a*D) (cutRight : a*D≤k)
      (containsLeft : max l (a*D-(k-p))≤p)
      (containsRight : e≤min r (a*D))
      (separates : min r (a*D)≤max l (a*D-(k-p))+(k-p)) :
      Residual f n L D Q p e k
  | low (R : Bounds) (valid : R.Valid f n)
      (left : R.lo≤p) (right : e+(k-p)≤R.hi)
      (displacement : R.period=k-p) (exponent : R.hi-R.lo<3*R.period)
      (scheduled : p∈lowStarts R D) : Residual f n L D Q p e k
  | large (R : Bounds) (valid : R.Valid f n)
      (left : R.lo≤p) (right : e+(k-p)≤R.hi)
      (cubic : 3*R.period≤R.hi-R.lo) (largePeriod : Q<R.period)
      (scheduled : (p,k-p)∈largePairs R) : Residual f n L D Q p e k

/-- Every absolute P2 witness is either accepted by the concrete cubic
small-period branch or lies in one explicitly described residual query
case. No supplied coverage assumption or minimum period is used. -/
theorem cover [DecidableEq α] (P : SevenDFA α) (f : Nat→α)
    (n L D Q : Nat) (x : P2Periodic.Layout Nat)
    (hw : P2Periodic.Witness P f n [] [] x)
    (hL : 0<L) (hD : 0<D) (hQL : Q≤L) :
    Residual f n L D Q x.p x.e x.k ∨
      (SmallPeriodP2.solve P f n Q).accepted=true := by
  by_cases hpos : x.p<x.e
  · have hc := GlobalCoverage.cover f n L D Q x.p x.e x.k
      (outer_copy P f n x hw hpos) hD hQL
    cases hc with
    | short h => exact Or.inl (.short h)
    | separated l r h hl hr hs => exact Or.inl (.separated l r h hl hr hs)
    | longGap l r a h hl hr hcl hcr h1 h2 h3 =>
      exact Or.inl (.longGap l r a h hl hr hcl hcr h1 h2 h3)
    | low R hv hl hr hd he hs => exact Or.inl (.low R hv hl hr hd he hs)
    | large R hv hl hr hc hq hs => exact Or.inl (.large R hv hl hr hc hq hs)
    | smallPeriod R hv hl hr hc hq hlong =>
      have heq := hw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      have hlen := congrArg List.length heq
      simp only [factor,segment_length] at hlen
      have hxf : x.f≤R.hi := by
        have hkf := hw.2.2.2.2.2.2.1
        omega
      exact Or.inr (small_complete P f n Q x hw R hv hl hxf hc hq hlong)
  · exact Or.inl (.short (by omega))

end REWB.GlobalCoverageP2
