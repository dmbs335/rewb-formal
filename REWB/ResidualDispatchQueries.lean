import REWB.ResidualDispatchCoverage
import REWB.ResidualSeparatedP1
import REWB.ResidualSeparatedP2

/-! Closed semantic dispatch to the actual window list. P1 retains its
absolute earlier source. P2 uses oneUseRange's source lower bound. These
are exact query predicates; this file does not assert a fast runtime
implementation of either predicate or execute an unbounded search. -/
namespace REWB.ResidualDispatch
open REWB.Periodic REWB.IndexedGrid REWB.ResidualSeparated REWB.BoundaryApplication
variable {α : Type} {σ : Nat}

def P1Query (P : SevenDFA α) (w : Word α) (c : Strip) : Prop :=
  ∃q : Fin P.G.stateCount,Spec.boundaryRange P.A P.B P.C
    (gapStart P.G (Range.build P.G w) c.lo c.hi c.distance q) P.D
    (outerSuffix P.F P.G P.H (Range.build P.H w) c.hi c.distance w.length q) w c.lo c.hi

def P2Query (P : SevenDFA α) (w : Word α) (c : Strip) : Prop :=
  ∃q : Fin P.G.stateCount,Spec.oneUseRange
    (innerPrefix P.A P.B P.G (Range.build P.A w) (Range.build P.G w) c.lo c.hi c.distance q)
    P.C P.D (outerSuffix P.F P.G P.H (Range.build P.H w) c.hi c.distance w.length q) w c.lo c.hi

theorem p1_query_sound (P : SevenDFA α) (w : Word α) (c : Strip)
    (hw : Window w c.lo c.hi c.distance) (hq : P1Query P w c) : MatchesWithin P.nested1 w 2 := by
  obtain ⟨v⟩:=(p1_iff P w c.lo c.hi c.distance hw).mp hq
  exact P1Witness.sound P w c.lo c.hi c.distance hw v

theorem p2_query_sound (P : SevenDFA α) (w : Word α) (c : Strip)
    (hw : Window w c.lo c.hi c.distance) (hq : P2Query P w c) : MatchesWithin P.nested2 w 2 := by
  obtain ⟨v⟩:=(p2_iff P w c.lo c.hi c.distance hw).mp hq
  exact P2Witness.sound P w c.lo c.hi c.distance hw v

theorem scheduled_p1_sound (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n s L D Q : Nat) (c : Strip)
    (hm : c∈(prepare f n s L D Q).windows) (hq : P1Query P (segment f 0 n) c) :
    MatchesWithin P.nested1 (segment f 0 n) 2 :=
  p1_query_sound P _ c (prepare_sound f n s L D Q c hm) hq

theorem scheduled_p2_sound (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n s L D Q : Nat) (c : Strip)
    (hm : c∈(prepare f n s L D Q).windows) (hq : P2Query P (segment f 0 n) c) :
    MatchesWithin P.nested2 (segment f 0 n) 2 :=
  p2_query_sound P _ c (prepare_sound f n s L D Q c hm) hq

def ShortP1 (P : SevenDFA α) (f : Nat→α) (n L : Nat) : Prop :=
  ∃v : GlobalCoverageP1.Witness P f n,v.target.e-v.outerStart<L

def ShortP2 (P : SevenDFA α) (f : Nat→α) (n L : Nat) : Prop :=
  ∃x,P2Periodic.Witness P f n [] [] x ∧ x.e-x.p<L

/-- Soundness includes an empty outer copy and keeps the earlier source
at its original absolute coordinates. -/
theorem global_p1_sound (P : SevenDFA α) (f : Nat→α) (n : Nat) (v : GlobalCoverageP1.Witness P f n) :
    MatchesWithin P.nested1 (segment f 0 n) 2 := by
  obtain ⟨hpj,hjt,hte,hek,hkf,hfn,_,_,_,_,_,he⟩:=v.target_ok
  have hlen:=congrArg List.length he
  simp only [P2Periodic.factor,segment_length] at hlen
  have hk : v.target.k=v.outerStart+(v.target.k-v.outerStart) := by omega
  have hf : v.target.f=v.target.e+(v.target.k-v.outerStart) := by omega
  have hw : Window (segment f 0 n) v.outerStart v.target.e (v.target.k-v.outerStart) := by
    refine ⟨by omega,by simpa only [segment_length] using (show v.target.e+(v.target.k-v.outerStart)≤n by omega),
      by omega,?_⟩
    rw [←GlobalSemanticCoverage.factor_slice f n v.outerStart v.target.e (by omega) (by omega),
      ←GlobalSemanticCoverage.factor_slice f n (v.outerStart+(v.target.k-v.outerStart))
        (v.target.e+(v.target.k-v.outerStart)) (by omega) (by omega),←hk,←hf]
    exact he
  exact P1Witness.sound P _ _ _ _ hw
    (of_global P f n v.outerStart v.target.e (v.target.k-v.outerStart) v (Nat.le_refl _) (Nat.le_refl _) hk)

theorem short_p1_sound (P : SevenDFA α) (f : Nat→α) (n L : Nat) (hs : ShortP1 P f n L) :
    MatchesWithin P.nested1 (segment f 0 n) 2 := by
  obtain ⟨v,_⟩:=hs
  exact global_p1_sound P f n v

theorem short_p2_sound (P : SevenDFA α) (f : Nat→α) (n L : Nat) (hs : ShortP2 P f n L) :
    MatchesWithin P.nested2 (segment f 0 n) 2 := by
  obtain ⟨x,hx,_⟩:=hs
  simpa only [List.nil_append,List.append_nil] using P2Periodic.witness_sound P f n [] [] x hx

theorem p1_dispatch_complete (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n s L D Q : Nat)
    (hs : 0<s) (hSL : s≤L) (hD : 0<D) (hQL : Q≤L)
    (hm : MatchesWithin P.nested1 (segment f 0 n) 2) :
    (CountedP1Cubic.solve P f n Q).answer=true ∨ ShortP1 P f n L ∨
      ∃c,c∈(prepare f n s L D Q).windows ∧ P1Query P (segment f 0 n) c := by
  rcases IndexedGlobalCoverage.p1_cover P f n s L D Q hm hs hSL hD hQL with ⟨v,hr⟩|ha
  · by_cases hshort : v.target.e-v.outerStart<L
    · exact Or.inr (Or.inl ⟨v,hshort⟩)
    · have hp : v.outerStart<v.target.e := by omega
      have hc:=GlobalCoverageP1.outer_copy P f n v hp
      obtain ⟨c,hc',hl,he,hq⟩:=residual_window f n s L D Q v.outerStart v.target.e v.target.k hD hc (by omega) hr
      have hw:=prepare_sound f n s L D Q c hc'
      have hk:=hc.separated
      refine Or.inr (Or.inr ⟨c,hc',?_⟩)
      simpa only [P1Query,segment_length] using
        ResidualSeparated.p1_complete P f n c.lo c.hi c.distance hw v hl he (by omega)
  · exact Or.inl ha

theorem p2_dispatch_complete (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n s L D Q : Nat)
    (hs : 0<s) (hSL : s≤L) (hD : 0<D) (hQL : Q≤L)
    (hm : MatchesWithin P.nested2 (segment f 0 n) 2) :
    (SmallPeriodP2.solve P f n Q).accepted=true ∨ ShortP2 P f n L ∨
      ∃c,c∈(prepare f n s L D Q).windows ∧ P2Query P (segment f 0 n) c := by
  rcases IndexedGlobalCoverage.p2_cover P f n s L D Q hm hs hSL hD hQL with ⟨x,hx,hr⟩|ha
  · by_cases hshort : x.e-x.p<L
    · exact Or.inr (Or.inl ⟨x,hx,hshort⟩)
    · have hp : x.p<x.e := by omega
      have hc:=GlobalCoverageP2.outer_copy P f n x hx hp
      obtain ⟨c,hc',hl,he,hq⟩:=residual_window f n s L D Q x.p x.e x.k hD hc (by omega) hr
      have hw:=prepare_sound f n s L D Q c hc'
      have hk:=hc.separated
      refine Or.inr (Or.inr ⟨c,hc',?_⟩)
      simpa only [P2Query,segment_length] using
        ResidualSeparated.p2_complete P f n c.lo c.hi c.distance hw x hx hl he (by omega)
  · exact Or.inl ha

theorem p1_dispatch_iff (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n s L D Q : Nat)
    (hs : 0<s) (hSL : s≤L) (hD : 0<D) (hQL : Q≤L) :
    MatchesWithin P.nested1 (segment f 0 n) 2 ↔
      (CountedP1Cubic.solve P f n Q).answer=true ∨ ShortP1 P f n L ∨
        ∃c,c∈(prepare f n s L D Q).windows ∧ P1Query P (segment f 0 n) c := by
  refine ⟨p1_dispatch_complete P f n s L D Q hs hSL hD hQL,?_⟩
  rintro (ha|ha|⟨c,hc,hq⟩)
  · exact CountedP1Cubic.solve_sound P f n Q ha
  · exact short_p1_sound P f n L ha
  · exact scheduled_p1_sound P f n s L D Q c hc hq

theorem p2_dispatch_iff (P : SevenDFA (Fin σ)) (f : Nat→Fin σ) (n s L D Q : Nat)
    (hs : 0<s) (hSL : s≤L) (hD : 0<D) (hQL : Q≤L) :
    MatchesWithin P.nested2 (segment f 0 n) 2 ↔
      (SmallPeriodP2.solve P f n Q).accepted=true ∨ ShortP2 P f n L ∨
        ∃c,c∈(prepare f n s L D Q).windows ∧ P2Query P (segment f 0 n) c := by
  refine ⟨p2_dispatch_complete P f n s L D Q hs hSL hD hQL,?_⟩
  rintro (ha|ha|⟨c,hc,hq⟩)
  · exact SmallPeriodP2.solve_sound P f n Q ha
  · exact short_p2_sound P f n L ha
  · exact scheduled_p2_sound P f n s L D Q c hc hq

end REWB.ResidualDispatch
