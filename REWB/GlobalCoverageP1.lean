import REWB.GlobalCoverageP2
import REWB.CountedP1Cubic

/-! Absolute P1 witnesses enter the same geometric schedules as P2.
The earlier inner source retains its original text coordinates and may
lie completely outside the outer-copy run. The small-period result is
acceptance by the actual counted long/short-source dispatcher. -/
namespace REWB.GlobalCoverageP1
open REWB.Periodic REWB.RunGeometry REWB.GlobalCoverage
open REWB.P2Periodic (factor)
open REWB.GlobalCoverageP2 (factor_rebase suffix_context)
variable {α : Type} {σ : Nat}

structure Witness (P : SevenDFA α) (f : Nat→α) (n : Nat) where
  outerStart : Nat
  target : P1Target.Layout Nat
  earlierStart : Nat
  target_ok : P1Target.Witness P f n outerStart [] target
  earlier : earlierStart+(target.t-target.j)≤outerStart
  equal_inner : segment f earlierStart (target.t-target.j)=factor f target.j target.t
  prefix_ok : P.A.accepts (segment f 0 earlierStart)
  gap_ok : P.C.accepts (Spec.slice (segment f 0 n)
    (earlierStart+(target.t-target.j)) outerStart)

theorem relative_target (P : SevenDFA α) (f : Nat→α) (n l r p : Nat)
    (x : P1Target.Layout Nat) (hw : P1Target.Witness P f n p [] x)
    (hlp : l≤p) (hfr : x.f≤r) (hrn : r≤n) :
    P1Target.Witness P (shift f l) (r-l) (p-l)
      ((segment f 0 n).drop r) (x.map (fun a=>a-l)) := by
  rcases hw with ⟨hpj,hjt,hte,hek,hkf,hfn,hD,hB,hF,hG,hH,hv⟩
  simp only [List.append_nil] at hH
  simp only [P1Target.Witness,P1Target.Layout.map]
  refine ⟨by omega,by omega,by omega,by omega,by omega,by omega,
    ?_,?_,?_,?_,?_,?_⟩
  · rwa [factor_rebase f l p x.j hlp hpj]
  · rwa [factor_rebase f l x.j x.t (by omega) hjt]
  · rwa [factor_rebase f l x.t x.e (by omega) hte]
  · rwa [factor_rebase f l x.e x.k (by omega) hek]
  · rwa [suffix_context f n l x.f r (by omega) hfr hrn]
  · rwa [factor_rebase f l p x.e hlp (by omega),
      factor_rebase f l x.k x.f (by omega) hkf]

/-- Global-to-local witness conversion preserves the arbitrary earlier
source; only the outer-run target coordinates are translated. -/
def relative_witness (P : SevenDFA α) (f : Nat→α) (n : Nat)
    (w : Witness P f n) (R : Bounds)
    (hlp : R.lo≤w.outerStart) (hfr : w.target.f≤R.hi) (hrn : R.hi≤n)
    (hlong : R.period≤w.target.e-w.outerStart) : P1Cubic.Witness P f n R := by
  have hw := w.target_ok
  rcases hw with ⟨hpj,hjt,hte,hek,hkf,hfn,hD,hB,hF,hG,hH,hv⟩
  have hlen : (w.target.t-R.lo)-(w.target.j-R.lo)=w.target.t-w.target.j := by omega
  have hstart : R.lo+(w.outerStart-R.lo)=w.outerStart := by omega
  refine ⟨w.outerStart-R.lo,w.target.map (fun a=>a-R.lo),w.earlierStart,
    relative_target P f n R.lo R.hi w.outerStart w.target w.target_ok hlp hfr hrn,
    ?_,?_,?_,w.prefix_ok,?_⟩
  · change R.period≤(w.target.e-R.lo)-(w.outerStart-R.lo)
    omega
  · change w.earlierStart+((w.target.t-R.lo)-(w.target.j-R.lo))≤
      R.lo+(w.outerStart-R.lo)
    rw [hlen,hstart]
    exact w.earlier
  · change segment f w.earlierStart ((w.target.t-R.lo)-(w.target.j-R.lo))=
      factor (shift f R.lo) (w.target.j-R.lo) (w.target.t-R.lo)
    rw [hlen,factor_rebase f R.lo w.target.j w.target.t (by omega) hjt]
    exact w.equal_inner
  · change P.C.accepts (Spec.slice (segment f 0 n)
      (w.earlierStart+((w.target.t-R.lo)-(w.target.j-R.lo)))
      (R.lo+(w.outerStart-R.lo)))
    rw [hlen,hstart]
    exact w.gap_ok

theorem outer_copy (P : SevenDFA α) (f : Nat→α) (n : Nat)
    (w : Witness P f n) (hpos : w.outerStart<w.target.e) :
    Copy f n w.outerStart w.target.e w.target.k := by
  rcases w.target_ok with ⟨hpj,hjt,hte,hek,hkf,hfn,hD,hB,hF,hG,hH,hv⟩
  have hlen := congrArg List.length hv
  simp only [factor,segment_length] at hlen
  refine ⟨hpos,hek,by omega,?_⟩
  simpa only [factor,← hlen] using hv

theorem small_complete (P : SevenDFA (Fin σ)) (f : Nat→Fin σ)
    (n Q : Nat) (w : Witness P f n) (R : Bounds) (hR : R.Valid f n)
    (hlp : R.lo≤w.outerStart) (hfr : w.target.f≤R.hi)
    (hc : 3*R.period≤R.hi-R.lo) (hq : R.period≤Q)
    (hlong : R.period≤w.target.e-w.outerStart) :
    (CountedP1Cubic.solve P f n Q).answer=true :=
  CountedP1Cubic.solve_complete P f n Q R hR hq hc
    (relative_witness P f n w R hlp hfr hR.2.1 hlong)

/-- Every P1 witness is either accepted by the concrete counted cubic
dispatcher or enters one explicitly enumerated residual query class. -/
theorem cover (P : SevenDFA (Fin σ)) (f : Nat→Fin σ)
    (n L D Q : Nat) (w : Witness P f n)
    (hL : 0<L) (hD : 0<D) (hQL : Q≤L) :
    GlobalCoverageP2.Residual f n L D Q w.outerStart w.target.e w.target.k ∨
      (CountedP1Cubic.solve P f n Q).answer=true := by
  by_cases hpos : w.outerStart<w.target.e
  · have hc := GlobalCoverage.cover f n L D Q w.outerStart w.target.e w.target.k
      (outer_copy P f n w hpos) hD hQL
    cases hc with
    | short h => exact Or.inl (.short h)
    | separated l r h hl hr hs => exact Or.inl (.separated l r h hl hr hs)
    | longGap l r a h hl hr hcl hcr h1 h2 h3 =>
      exact Or.inl (.longGap l r a h hl hr hcl hcr h1 h2 h3)
    | low R hv hl hr hd he hs => exact Or.inl (.low R hv hl hr hd he hs)
    | large R hv hl hr hc hq hs => exact Or.inl (.large R hv hl hr hc hq hs)
    | smallPeriod R hv hl hr hc hq hlong =>
      rcases w.target_ok with ⟨hpj,hjt,hte,hek,hkf,hfn,hD,hB,hF,hG,hH,heq⟩
      have hlen := congrArg List.length heq
      simp only [factor,segment_length] at hlen
      have hxf : w.target.f≤R.hi := by omega
      exact Or.inr (small_complete P f n Q w R hv hl hxf hc hq hlong)
  · exact Or.inl (.short (by omega))

end REWB.GlobalCoverageP1
